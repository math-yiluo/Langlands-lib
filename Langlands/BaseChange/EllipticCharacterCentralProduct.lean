import Langlands.BaseChange.RegularEllipticOpen
import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Langlands.JacquetLanglands.LocalCharacter
import Langlands.Representation.Hecke.IntegratedConvolution

/-! # Central translation of regular elliptic character values -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis JacquetLanglands MeasureTheory _root_.Polynomial

universe u uV uW

private theorem irreducible_scaleRoots {F : Type u} [Field F] {p : F[X]}
    (hp : p.Monic) (hirr : Irreducible p) {a : F} (ha : a ≠ 0) :
    Irreducible (p.scaleRoots a) := by
  have hmono := (monic_scaleRoots_iff a).mpr hp
  apply hmono.irreducible_iff_natDegree.mpr
  constructor
  · intro he
    have hd := congrArg natDegree he
    rw [natDegree_scaleRoots, natDegree_one] at hd
    exact hirr.natDegree_pos.ne' hd
  · intro f g hf hg he
    have hmul := congrArg (fun q : F[X] => q.scaleRoots a⁻¹) he
    change (f * g).scaleRoots a⁻¹ = (p.scaleRoots a).scaleRoots a⁻¹ at hmul
    rw [mul_scaleRoots_of_noZeroDivisors, ← scaleRoots_mul, mul_inv_cancel₀ ha,
      scaleRoots_one] at hmul
    have hmF := (monic_scaleRoots_iff a⁻¹).mpr hf
    have hmG := (monic_scaleRoots_iff a⁻¹).mpr hg
    simpa only [natDegree_scaleRoots] using
      (hp.irreducible_iff_natDegree.mp hirr).2 _ _ hmF hmG hmul

private theorem charpoly_smul {F : Type u} [Field F] [Infinite F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) {a : F} (ha : a ≠ 0) :
    (a • A).charpoly = A.charpoly.scaleRoots a := by
  apply Polynomial.eq_of_infinite_eval_eq
  suffices h : ∀ x : F, ((a • A).charpoly).eval x = (A.charpoly.scaleRoots a).eval x by
    simpa only [h, Set.ofPred_true] using (Set.infinite_univ : (Set.univ : Set F).Infinite)
  intro x
  obtain ⟨y, rfl⟩ : ∃ y : F, a * y = x := ⟨a⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly,
    Matrix.eval_charpoly, ← Matrix.det_smul, smul_sub]
  congr 1
  rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
  rfl

private theorem isRegularElliptic_scalar_mul {F : Type u} [Field F] [CharZero F] {n : ℕ}
    {g : GeneralLinear n F} (hg : IsRegularElliptic g) (z : Fˣ) :
    IsRegularElliptic (GeneralLinear.scalar z * g) := by
  have : Infinite F := Infinite.of_injective (fun k : ℕ => (k : F)) Nat.cast_injective
  let zg : GeneralLinear n F := GeneralLinear.scalar z * g
  have hm : (↑zg : Matrix (Fin n) (Fin n) F) =
      (z : F) • (g : Matrix (Fin n) (Fin n) F) := by
    change Matrix.scalar _ (z : F) * _ = _
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have hirr : Irreducible (↑zg : Matrix (Fin n) (Fin n) F).charpoly := by
    rw [hm, charpoly_smul _ z.ne_zero]
    exact irreducible_scaleRoots (g : Matrix (Fin n) (Fin n) F).charpoly_monic hg.2 z.ne_zero
  exact ⟨hirr.separable, hirr⟩

/-- Multiplication by a central element preserves regular ellipticity. -/
theorem isRegularElliptic_center_mul {F : Type u} [Field F] [CharZero F] {n : ℕ}
    {g : GeneralLinear n F} (hg : IsRegularElliptic g)
    (z : Subgroup.center (GeneralLinear n F)) : IsRegularElliptic ((z : GeneralLinear n F) * g) := by
  have h : (z : GeneralLinear n F) ∈ (GeneralLinear.scalar (n := n)).range := by
    simpa only [GeneralLinear.scalar, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
      using z.property
  obtain ⟨a, ha⟩ := h
  rw [← ha]
  exact isRegularElliptic_scalar_mul hg a

section Distribution

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- When an element acts by a scalar, left translating a test by it multiplies the
trace distribution by that scalar. -/
theorem distribution_leftTranslate_of_scalar {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ) (z : G) (a : ℂ)
    (hz : ∀ v, ρ z v = a • v) (f : SchwartzBruhat G) :
    Character.distribution μ ρ hρ (Hecke.TestFunction.leftTranslate z f) =
      a * Character.distribution μ ρ hρ f := by
  have hAction : Character.finiteRankIntegratedAction μ ρ hρ (Hecke.TestFunction.leftTranslate z f) =
      a • Character.finiteRankIntegratedAction μ ρ hρ f := by
    apply Subtype.ext
    ext v
    exact (Hecke.integratedAction_leftTranslate μ ρ hρ.1 z f v).trans (hz _)
  rw [Character.distribution_apply, hAction, map_smul, smul_eq_mul, Character.distribution_apply]

end Distribution

section LocalValues

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} {hρ : IsAdmissible ρ}

/-- A local character value transforms by the scalar action under left translation. -/
theorem hasCharacterValue_mul_left_of_scalar {g z : G} {b a : ℂ}
    (h : HasCharacterValue ρ hρ g b) (hz : ∀ v, ρ z v = a • v) :
    HasCharacterValue ρ hρ (z * g) (a * b) := by
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  intro μ _
  obtain ⟨U, hU, hg, hvalue⟩ := h μ
  refine ⟨(fun x => z⁻¹ * x) ⁻¹' U, hU.preimage (continuous_const.mul continuous_id),
    by simpa using hg, ?_⟩
  intro f hf
  let k := Hecke.TestFunction.leftTranslate z⁻¹ f
  have hk : Function.support (k : G → ℂ) ⊆ U := by
    intro x hx
    have hzx : z * x ∈ Function.support (f : G → ℂ) := by
      simpa only [Function.mem_support, k, Hecke.TestFunction.leftTranslate_apply, inv_inv]
        using hx
    have hx' : z⁻¹ * (z * x) ∈ U := hf hzx
    simpa using hx'
  have ht : Hecke.TestFunction.leftTranslate z k = f := by
    ext x
    simp [k]
  have hd := distribution_leftTranslate_of_scalar μ ρ hρ z a hz k
  rw [ht, hvalue k hk] at hd
  simpa only [k, Hecke.TestFunction.leftTranslate_apply, inv_inv,
    integral_mul_left_eq_self, mul_assoc] using hd

/-- Local values give a locally constant character on any chosen locus. -/
theorem isLocallyConstant_of_hasCharacterValue {S : Set G} {Θ : S → ℂ}
    (hΘ : ∀ g : S, HasCharacterValue ρ hρ g.val (Θ g)) : IsLocallyConstant Θ := by
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  apply (IsLocallyConstant.iff_exists_open _).2
  intro g
  obtain ⟨U, hU, hg, hval⟩ := hΘ g Measure.haar
  refine ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, hg, ?_⟩
  intro g' hg'
  exact (hΘ g' Measure.haar).unique ⟨U, hU, hg', hval⟩

end LocalValues

section Product

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

attribute [local instance] LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace

local notation "G" => GeneralLinear n F
local notation "Z" => Subgroup.center G
local notation "E" => {g : G // IsRegularElliptic g}

variable {ρ : Representation ℂ (GeneralLinear n F) V}
  {π : Representation ℂ (GeneralLinear n F) W}
  {hρ : IsAdmissible ρ} {hπ : IsAdmissible π}
  (cρ : UnitaryCentralCharacter ρ) (cπ : UnitaryCentralCharacter π)
  (hc : cρ.character = cπ.character)
  (Θρ Θπ : {g : GeneralLinear n F // IsRegularElliptic g} → ℂ)
  (hΘρ : ∀ g, HasCharacterValue ρ hρ g.val (Θρ g))
  (hΘπ : ∀ g, HasCharacterValue π hπ g.val (Θπ g))

open Classical in
private def characterProductOnGroup (Θρ Θπ : E → ℂ) (g : G) : ℂ :=
  if h : IsRegularElliptic g then Θρ ⟨g, h⟩ * star (Θπ ⟨g, h⟩) else 0

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem regularElliptic_center_mul_iff (z : Z) (g : G) :
    IsRegularElliptic ((z : G) * g) ↔ IsRegularElliptic g := by
  constructor
  · intro hg
    simpa using isRegularElliptic_center_mul hg z⁻¹
  · exact fun hg => isRegularElliptic_center_mul hg z

include hc hΘρ hΘπ in
private theorem characterProductOnGroup_center_mul (z : Z) (g : G) :
    characterProductOnGroup Θρ Θπ (z * g) = characterProductOnGroup Θρ Θπ g := by
  classical
  by_cases hg : IsRegularElliptic g
  · let x : E := ⟨g, hg⟩
    have hzg := (regularElliptic_center_mul_iff z g).mpr hg
    let y : E := ⟨z * g, hzg⟩
    have hvalρ : Θρ y = (cρ.character z : ℂ) * Θρ x :=
      (hΘρ y).unique (hasCharacterValue_mul_left_of_scalar (hΘρ x) (cρ.acts z))
    have hvalπ : Θπ y = (cπ.character z : ℂ) * Θπ x :=
      (hΘπ y).unique (hasCharacterValue_mul_left_of_scalar (hΘπ x) (cπ.acts z))
    simp only [characterProductOnGroup, dite_eq_left hg, dite_eq_left hzg]
    change Θρ y * star (Θπ y) = Θρ x * star (Θπ x)
    rw [hvalρ, hvalπ, hc]
    let a : ℂ := cπ.character z
    have ha : a * star a = 1 := by
      change a * (starRingEnd ℂ) a = 1
      rw [mul_comm, Complex.conj_mul', cπ.norm_eq_one z]
      norm_num
    change (a * Θρ x) * star (a * Θπ x) = _
    calc
      _ = (a * star a) * (Θρ x * star (Θπ x)) := by rw [star_mul]; ring
      _ = _ := by rw [ha, one_mul]
  · have hzg : ¬ IsRegularElliptic ((z : G) * g) :=
      fun h => hg ((regularElliptic_center_mul_iff z g).mp h)
    simp [characterProductOnGroup, hg, hzg]

/-- The product of the regular elliptic character values of two representations with the
same unitary central character, extended by zero and descended to the central quotient. -/
def ellipticCharacterProduct : G ⧸ Z → ℂ :=
  Quotient.lift (characterProductOnGroup Θρ Θπ) (by
    intro x y hxy
    let z : Z := ⟨x⁻¹ * y, QuotientGroup.leftRel_apply.mp hxy⟩
    have hcomm := Subgroup.mem_center_iff.mp z.property x
    have hy : (z : G) * x = y := by
      rw [← hcomm]
      simp [z]
    rw [← hy, characterProductOnGroup_center_mul cρ cπ hc Θρ Θπ hΘρ hΘπ])

open Classical in
theorem ellipticCharacterProduct_mk (g : G) :
    ellipticCharacterProduct cρ cπ hc Θρ Θπ hΘρ hΘπ (QuotientGroup.mk g) =
      if h : IsRegularElliptic g then Θρ ⟨g, h⟩ * star (Θπ ⟨g, h⟩) else 0 :=
  rfl

/-- The elliptic character product is a Borel function on the central quotient. -/
theorem measurable_ellipticCharacterProduct :
    letI := centralQuotientMeasurableSpace F n
    Measurable (ellipticCharacterProduct cρ cπ hc Θρ Θπ hΘρ hΘπ) := by
  classical
  let : MeasurableSpace (G ⧸ Z) := centralQuotientMeasurableSpace F n
  have : BorelSpace (G ⧸ Z) := centralQuotientBorelSpace F n
  let p : G ⧸ Z → ℂ := ellipticCharacterProduct cρ cπ hc Θρ Θπ hΘρ hΘπ
  let q : G → G ⧸ Z := QuotientGroup.mk
  let S : Set G := {g | IsRegularElliptic g}
  let U := q '' S
  have hU : IsOpen U := QuotientGroup.isOpenMap_coe (N := Z) S (isOpen_regularElliptic F n)
  have hpre : q ⁻¹' U = S := by
    ext g
    constructor
    · rintro ⟨x, hx, hxg⟩
      let z : Z := ⟨x⁻¹ * g, QuotientGroup.eq.mp hxg⟩
      have hcomm := Subgroup.mem_center_iff.mp z.property x
      have he : (z : G) * x = g := by
        rw [← hcomm]
        simp [z]
      exact he ▸ isRegularElliptic_center_mul hx z
    · exact fun hg => ⟨g, hg, rfl⟩
  have hpC : ContinuousOn p U := by
    apply ((QuotientGroup.isQuotientMap_mk Z).continuousOn_isOpen_iff hU).mpr
    rw [show (QuotientGroup.mk : G → G ⧸ Z) ⁻¹' U = S from hpre,
      continuousOn_iff_continuous_domRestrict]
    have h : S.domRestrict (p ∘ q) = fun g : S => Θρ g * star (Θπ g) := by
      funext g
      exact (ellipticCharacterProduct_mk cρ cπ hc Θρ Θπ hΘρ hΘπ g.val).trans
        (dite_eq_left g.property)
    rw [h]
    exact (isLocallyConstant_of_hasCharacterValue hΘρ).continuous.mul
      ((isLocallyConstant_of_hasCharacterValue hΘπ).continuous.star)
  have hpEq : U.piecewise p (fun _ => 0) = p := by
    funext x
    induction x using QuotientGroup.induction_on with
    | H g =>
      change U.piecewise p (fun _ => 0) (q g) = p (q g)
      by_cases hg : IsRegularElliptic g
      · exact Set.piecewise_eq_of_mem U p _ (show q g ∈ U from ⟨g, hg, rfl⟩)
      · have hx : q g ∉ U := fun h => hg (show g ∈ S from hpre ▸ h)
        rw [Set.piecewise_eq_of_notMem U p _ hx]
        exact ((ellipticCharacterProduct_mk cρ cπ hc Θρ Θπ hΘρ hΘπ g).trans
          (dite_eq_right hg)).symm
  change Measurable p
  rw [← hpEq]
  exact hpC.measurable_piecewise continuousOn_const hU.measurableSet

end Product

end Langlands.BaseChange
