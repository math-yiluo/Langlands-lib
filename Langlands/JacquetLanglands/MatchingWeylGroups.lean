import Langlands.Algebra.DivisionFieldEmbeddingsProof
import Langlands.BaseChange.WeylTorusFinite
import Langlands.GroupScheme.NormOneOuterDescent
import Langlands.JacquetLanglands.MatchingCentralizers
import Langlands.JacquetLanglands.TransportedEllipticCharacter

/-! # Rational Weyl factors for matching elliptic tori -/

noncomputable section

namespace Langlands.JacquetLanglands

open Langlands.BaseChange Langlands.CentralSimple _root_.Polynomial
open scoped TensorProduct

universe u

section Group

variable {G : Type*} [Group G] (g : G)

local notation "Cent" => Subgroup.centralizer (singleton g : Set G)
local notation "Norm" => Subgroup.normalizer (Cent : Set G)

/-- For a commutative centralizer, its normalizer consists of the elements whose
conjugate of the given point belongs to the centralizer. -/
theorem mem_normalizer_centralizer_iff (hcomm : ∀ a b : Cent, Commute a.val b.val) (x : G) :
    x ∈ Norm ↔ x * g * x⁻¹ ∈ Cent := by
  have hg : g ∈ Cent := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine ⟨fun hx => (Subgroup.mem_normalizer_iff.mp hx g).mp hg, fun hx => ?_⟩
  have hcomm' (a b : G)
      (ha : Commute a (x * g * x⁻¹)) (hb : Commute b (x * g * x⁻¹)) : Commute a b := by
    have pull (z : G) (hz : Commute z (x * g * x⁻¹)) : x⁻¹ * z * x ∈ Cent := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have he := (Commute.conj_iff x⁻¹).mpr hz
      simpa [mul_assoc] using he.eq
    exact (Commute.conj_iff x⁻¹).mp
      (by simpa only [inv_inv] using hcomm ⟨_, pull a ha⟩ ⟨_, pull b hb⟩)
  have hgc := hcomm ⟨g, hg⟩ ⟨_, hx⟩
  have he (a : G) : Commute a g ↔ Commute a (x * g * x⁻¹) := by
    refine ⟨fun ha => hcomm ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr ha.eq⟩
      ⟨_, hx⟩, fun ha => hcomm' a g ha hgc⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro a
  simp only [Subgroup.mem_centralizer_singleton_iff]
  exact (Commute.conj_iff x).symm.trans (he (x * a * x⁻¹)).symm

/-- Conjugating the given point identifies its rational Weyl quotient with the
conjugates of that point in its commutative centralizer. -/
def centralizerNormalizerOrbitEquiv (hcomm : ∀ a b : Cent, Commute a.val b.val) :
    Norm ⧸ (Cent).subgroupOf Norm ≃ {t : Cent // IsConj g t.val} := by
  let orbit (x : Norm) : {t : Cent // IsConj g t.val} :=
    ⟨⟨x.val * g * x.val⁻¹, (mem_normalizer_centralizer_iff g hcomm x.val).mp x.property⟩,
      isConj_iff.mpr ⟨x.val, rfl⟩⟩
  have horbit (x y : Norm) : (x⁻¹ * y : Norm) ∈ (Cent).subgroupOf Norm ↔ orbit x = orbit y := by
    change x.val⁻¹ * y.val ∈ Cent ↔ _
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hc
      apply Subtype.ext
      apply Subtype.ext
      change x.val * g * x.val⁻¹ = y.val * g * y.val⁻¹
      have he := congrArg (fun z => x.val * z * y.val⁻¹) hc
      simpa only [mul_assoc, mul_inv_cancel, mul_inv_cancel_left, mul_one] using he.symm
    · intro hc
      have he := congrArg (fun t => x.val⁻¹ * t.val.val * y.val) hc
      simpa [orbit, mul_assoc] using he.symm
  let f : Norm ⧸ (Cent).subgroupOf Norm → {t : Cent // IsConj g t.val} :=
    Quotient.lift orbit fun x y hxy => (horbit x y).mp (QuotientGroup.leftRel_apply.mp hxy)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro q r
    induction q using Quotient.inductionOn with
    | h x =>
      induction r using Quotient.inductionOn with
      | h y =>
        intro hxy
        exact QuotientGroup.eq.mpr ((horbit x y).mpr hxy)
  · intro t
    obtain ⟨x, hx⟩ := isConj_iff.mp t.property
    have hxN : x ∈ Norm := (mem_normalizer_centralizer_iff g hcomm x).mpr
      (by rw [hx]; exact t.val.property)
    exact ⟨QuotientGroup.mk (⟨x, hxN⟩ : Norm), Subtype.ext (Subtype.ext hx)⟩

end Group

section Matching

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D] {n : ℕ}
  {g : GeneralLinear n F} {g' : Dˣ}

private theorem splitCentralizer_commute (hg : IsRegularSemisimple g)
    (a b : Subgroup.centralizer ({g} : Set (GeneralLinear n F))) : Commute a.val b.val := by
  obtain ⟨v, hv⟩ := regularCyclicBasis F n g.val hg
  have ha : Commute a.val g := Subgroup.mem_centralizer_singleton_iff.mp a.property
  have hb : Commute b.val g := Subgroup.mem_centralizer_singleton_iff.mp b.property
  exact Units.ext (commute_of_commute_cyclicBasisMatrix hv
    (ha.map (Units.coeHom _)) (hb.map (Units.coeHom _))).eq

private theorem split_isConj_iff_charpoly_eq (hg : IsRegularSemisimple g)
    (a : GeneralLinear n F) : IsConj g a ↔ g.val.charpoly = a.val.charpoly := by
  constructor
  · intro hc
    obtain ⟨x, rfl⟩ := isConj_iff.mp hc
    simpa only [inv_inv] using (charpoly_conj x⁻¹ g).symm
  · intro hc
    obtain ⟨x, hx⟩ := matrixConj_of_squarefree_charpoly_eq g.val a.val hg.squarefree hc
    exact isConj_iff.mpr ⟨x, Units.ext hx⟩

private theorem division_isConj_iff_reducedCharpoly_eq (h : Corresponds F D g g') (a : Dˣ) :
    IsConj g' a ↔ reducedCharpoly F D g'.val = reducedCharpoly F D a.val := by
  constructor
  · intro hc
    obtain ⟨x, rfl⟩ := isConj_iff.mp hc
    simpa only [inv_inv] using h.2.2.symm.trans (h.conjugate_division x⁻¹).2.2
  · intro hc
    let p := reducedCharpoly F D g'.val
    let : Fact (Irreducible p) := ⟨irreducible_reducedCharpoly_of_separable F D _ h.2.1⟩
    let : Module.Finite F (AdjoinRoot p) := (AdjoinRoot.powerBasis
      (reducedCharpoly_monic F D g'.val).ne_zero).finite
    have ha : aeval a.val p = 0 := by
      dsimp only [p]
      rw [hc]
      exact Langlands.CentralDivision.aeval_reducedCharpoly F D a.val
    have hker (y : D) (hy : aeval y p = 0) (q : F[X]) (hq : q ∈ Ideal.span {p}) :
        aeval y q = 0 := by
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hq
      rw [map_mul, hy, mul_zero]
    let f : AdjoinRoot p →ₐ[F] D := Ideal.Quotient.liftₐ _ (aeval a.val) (hker _ ha)
    let f' : AdjoinRoot p →ₐ[F] D := Ideal.Quotient.liftₐ _ (aeval g'.val)
      (hker _ (Langlands.CentralDivision.aeval_reducedCharpoly F D g'.val))
    obtain ⟨x, hx⟩ := Langlands.CentralDivision.exists_unit_conj F D (AdjoinRoot p) f f'
    have hroot : f (AdjoinRoot.root p) = a.val :=
      (Ideal.Quotient.lift_mk _ _ _).trans (aeval_X _)
    have hroot' : f' (AdjoinRoot.root p) = g'.val :=
      (Ideal.Quotient.lift_mk _ _ _).trans (aeval_X _)
    refine isConj_iff.mpr ⟨x, Units.ext ?_⟩
    change x.val * g'.val * (x⁻¹).val = a.val
    simpa only [hroot, hroot'] using (hx (AdjoinRoot.root p)).symm

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
  [TopologicalSpace D] [IsModuleTopology F D]

/-- Corresponding points of the matched tori have the same characteristic
polynomial, including at points that are not regular. -/
theorem Corresponds.centralizerEquiv_charpoly_eq (h : Corresponds F D g g')
    (t : glCentralizer g) :
    t.val.val.charpoly = reducedCharpoly F D (h.centralizerEquiv t).val.val := by
  classical
  obtain rfl := h.eq_reducedDegree
  let L := finiteGaloisSplittingField F D
  let e := finiteGaloisSplittingChart F D
  let i := (Algebra.ofId F L).mapMatrix (m := Fin (reducedDegree F D))
  let j := (e.toAlgHom.restrictScalars F).comp
    (Algebra.TensorProduct.includeRight (R := F) (A := L) (B := D))
  have hgL : (i g.val).charpoly = g.val.charpoly.map (algebraMap F L) :=
    Matrix.charpoly_map _ _
  have hg'L : (j g'.val).charpoly = (reducedCharpoly F D g'.val).map (algebraMap F L) :=
    (reducedCharpoly_map_chart F D e g'.val).symm
  have hchar : (i g.val).charpoly = (j g'.val).charpoly := by rw [hgL, hg'L, h.2.2]
  have hsq : Squarefree (i g.val).charpoly := by rw [hgL]; exact h.1.1.map.squarefree
  obtain ⟨x, hx⟩ := matrixConj_of_squarefree_charpoly_eq (i g.val) (j g'.val) hsq hchar
  let c := (Langlands.GroupScheme.NormOneOuterDescent.conjugationAlgEquiv L x).toAlgHom
  let cF := c.restrictScalars F
  have hc : c (i g.val) = j g'.val := hx
  let A := Subalgebra.centralizer F {g.val}
  let B := Subalgebra.centralizer F {g'.val}
  have ht : Commute t.val g := by
    apply Subgroup.mem_centralizer_singleton_iff.mp
    exact (congrArg (fun H : Subgroup (GeneralLinear _ F) => t.val ∈ H)
      (glCentralizer_eq_centralizer g)).mp t.property
  let tA : A := ⟨t.val.val, (Subalgebra.mem_centralizer_iff F).mpr fun _ hy =>
    (Set.mem_singleton_iff.mp hy).symm ▸ ((ht.map (Units.coeHom _)).symm.eq)⟩
  let gA : A := ⟨g.val, (Subalgebra.mem_centralizer_iff F).mpr fun _ hy =>
    (Set.mem_singleton_iff.mp hy).symm ▸ rfl⟩
  have he : (h.centralizerEquiv t).val.val = (h.centralizerAlgebraEquiv tA).val := rfl
  let f := (cF.comp i).comp A.val
  let f' := (j.comp B.val).comp h.centralizerAlgebraEquiv.toAlgHom
  have hgen : f gA = f' gA :=
    hc.trans (congrArg j (h.centralizerAlgebraEquiv_apply_of_val_eq gA rfl)).symm
  obtain ⟨v, hv⟩ := regularCyclicBasis F (reducedDegree F D) g.val h.1.1
  obtain ⟨a, ha⟩ := exists_sum_pow_of_commute hv (ht.map (Units.coeHom _))
  have htA : tA = ∑ k, a k • gA ^ (k : ℕ) := by
    apply Subtype.ext
    change t.val.val = A.val (∑ k, a k • gA ^ (k : ℕ))
    rw [map_sum]
    simp only [map_smul, map_pow]
    exact ha
  have ht' : f tA = f' tA := by rw [htA]; simp only [map_sum, map_smul, map_pow, hgen]
  change c (i t.val.val) = j (h.centralizerAlgebraEquiv tA).val at ht'
  apply Polynomial.map_injective (algebraMap F L) (algebraMap F L).injective
  rw [he, reducedCharpoly_map_chart F D e, ← Matrix.charpoly_map]
  change (i t.val.val).charpoly = (j (h.centralizerAlgebraEquiv tA).val).charpoly
  rw [← ht']
  change (i t.val.val).charpoly = (x.val * i t.val.val * x⁻¹.val).charpoly
  rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]

/-- The torus isomorphism matches a split point and a division point
whenever either point is regular. -/
theorem Corresponds.on_centralizerEquiv (h : Corresponds F D g g') (t : glCentralizer g) :
    IsRegularSemisimple t.val ↔ Corresponds F D t.val (h.centralizerEquiv t).val := by
  rw [corresponds_iff, IsRegular, ← h.centralizerEquiv_charpoly_eq t]
  exact ⟨fun ht => ⟨ht, ht, rfl⟩, And.left⟩

/-- The normalizer modulo the rational torus of a maximal division centralizer. -/
abbrev divisionRationalWeylGroup (g' : Dˣ) :=
  (Subgroup.normalizer (divisionCentralizer g' : Set Dˣ)) ⧸
    (divisionCentralizer g').subgroupOf (Subgroup.normalizer (divisionCentralizer g' : Set Dˣ))

/-- Matching elliptic centralizers have equinumerous rational normalizer quotients. -/
def Corresponds.rationalWeylGroupEquiv (h : Corresponds F D g g') :
    WeylTorus.RationalWeylGroup (⟨glCentralizer g, g, h.1.1, rfl⟩ : WeylTorus F n) ≃
      divisionRationalWeylGroup g' := by
  let e := h.centralizerEquiv
  have hcomm (a b : glCentralizer g) : Commute a.val b.val := by
    have ha : a.val ∈ Subgroup.centralizer {g} := glCentralizer_eq_centralizer g ▸ a.property
    have hb : b.val ∈ Subgroup.centralizer {g} := glCentralizer_eq_centralizer g ▸ b.property
    exact splitCentralizer_commute h.1.1 ⟨_, ha⟩ ⟨_, hb⟩
  have hcomm' (a b : divisionCentralizer g') : Commute a.val b.val := by
    have he : Commute (e.symm a) (e.symm b) := Subtype.ext (hcomm _ _).eq
    have he' : Commute (e (e.symm a)) (e (e.symm b)) := he.map e.toMonoidHom
    rw [ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply] at he'
    exact he'.map (divisionCentralizer g').subtype
  let e₁ :
      WeylTorus.RationalWeylGroup (⟨glCentralizer g, g, h.1.1, rfl⟩ : WeylTorus F n) ≃
        {t : glCentralizer g // IsConj g t.val} := by
    change (Subgroup.normalizer (glCentralizer g : Set (GeneralLinear n F))) ⧸
      (glCentralizer g).subgroupOf (Subgroup.normalizer
        (glCentralizer g : Set (GeneralLinear n F))) ≃ _
    rw [glCentralizer_eq_centralizer]
    exact centralizerNormalizerOrbitEquiv g (splitCentralizer_commute h.1.1)
  let e₂ : divisionRationalWeylGroup g' ≃ {t : divisionCentralizer g' // IsConj g' t.val} := by
    unfold divisionRationalWeylGroup
    revert hcomm'
    rw [divisionCentralizer_eq_centralizer]
    exact centralizerNormalizerOrbitEquiv g'
  refine e₁.trans ((e.toEquiv.subtypeEquiv ?_).trans e₂.symm)
  intro t
  change IsConj g t.val ↔ IsConj g' (h.centralizerEquiv t).val
  rw [split_isConj_iff_charpoly_eq h.1.1, division_isConj_iff_reducedCharpoly_eq h,
    h.2.2, h.centralizerEquiv_charpoly_eq t]

/-- The matched rational normalizer quotients give the same denominator in the
two Weyl weights. -/
theorem Corresponds.natCard_rationalWeylGroup_eq (h : Corresponds F D g g') :
    Nat.card (WeylTorus.RationalWeylGroup (⟨glCentralizer g, g, h.1.1, rfl⟩ : WeylTorus F n)) =
      Nat.card (divisionRationalWeylGroup g') :=
  Nat.card_congr h.rationalWeylGroupEquiv

end Matching

end Langlands.JacquetLanglands
