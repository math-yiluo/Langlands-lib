import Langlands.TraceFormula.GeneralLinearBaseChangeNormPairing
import Langlands.TraceFormula.TwistedOrbitalConjugation
import Langlands.Global.AdelicGLDeterminantNormOne
import Mathlib.Topology.Algebra.Group.OpenMapping

/-!
# Twisted centralizers of related rational points of `Res_{L/K} GL_n` and `GL_n`

For a rational norm-one point `r` of `Res_{L/K} GL_n` with matrix coordinate `a ∈ GL_n(L)`
and a rational norm-one point `q` of `GL_n` with regular semisimple matrix coordinate
`b ∈ GL_n(K)`, related by `y⁻¹ N(a) y = b` for some `y ∈ GL_n(L)`, the `θ`-centralizer of `r`
in the norm-one adelic points of `Res_{L/K} GL_n` is isomorphic, as a topological group, to
the centralizer of `q` in the norm-one adelic points of `GL_n`. In adelic matrix coordinates
the isomorphism is `x ↦ y⁻¹ x y`, and it matches rational points.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Matrix
open scoped CategoryTheory.MonObj NNReal
open Langlands.BaseChange Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.GroupScheme Langlands.JacquetLanglands Langlands.QuotientIntegration
open Langlands.Global.AdelicFunctoriality Langlands.Global.AdelicBlockDeterminantCharacter
open Langlands.TraceFormula.AdelicGroupAutomorphism

namespace Langlands.TraceFormula

local instance baseChangeCentralizerGLAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance baseChangeCentralizerGLSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "Wₙ" => weilGroup K L GLₙ

set_option hygiene false in
local notation "Θₙ" => normOneAut K (unitGaloisAut K L GLₙ σ)

section Regularity

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- A rational matrix whose image at a finite place is regular elliptic is regular
semisimple. -/
theorem isRegularSemisimple_of_localProjection_rational (v : Langlands.Global.FinitePlace F)
    (g₀ : GeneralLinear n F)
    (hg₀ : IsRegularElliptic (FiniteAdelicGL.localProjection F n v
      (AdelicGL.finite F n (AdelicGL.rational F n g₀)))) : IsRegularSemisimple g₀ := by
  have h := hg₀.isRegularSemisimple
  change (g₀.val.map (algebraMap F (Langlands.Global.FiniteCompletion F v))).charpoly.Separable
    at h
  rw [Matrix.charpoly_map] at h
  exact (Polynomial.separable_map _).mp h

end Regularity

/-- A matrix over `K` whose scalar extension to `L` is regular semisimple is regular
semisimple. -/
theorem isRegularSemisimple_of_baseChange {K L : Type u} [Field K] [Field L] [Algebra K L]
    {n : ℕ} {b : GeneralLinear n K} (h : IsRegularSemisimple (baseChange K L n b)) :
    IsRegularSemisimple b := by
  change (b.val.map (algebraMap K L)).charpoly.Separable at h
  rw [Matrix.charpoly_map] at h
  exact (Polynomial.separable_map _).mp h

/-- Open mapping theorem: a continuous bijective homomorphism from a σ-compact topological
group onto a Hausdorff Baire topological group is an isomorphism of topological groups. -/
theorem exists_continuousMulEquiv_of_bijective {G H : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SigmaCompactSpace G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [BaireSpace H] [T2Space H] (F : G →* H) (hF : Continuous F)
    (hb : Function.Bijective F) : ∃ e : G ≃ₜ* H, ∀ x, e x = F x := by
  let M : G ≃* H := MulEquiv.ofBijective F hb
  let Hm : G ≃ₜ H := M.toEquiv.toHomeomorphOfContinuousOpen hF
    (MonoidHom.isOpenMap_of_sigmaCompact F hb.2 hF)
  exact ⟨{ M with continuous_toFun := Hm.continuous, continuous_invFun := Hm.symm.continuous },
    fun _ => rfl⟩

section Centralizer

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] {n l : ℕ} {σ : L ≃ₐ[K] L}

local instance (priority := low) baseChangeCentralizerUpperAlgebra : Algebra K (Adeles L) :=
  ((algebraMap L (Adeles L)).comp (algebraMap K L)).toAlgebra

/-- Entrywise extension of adelic coefficients from `𝔸_K` to `𝔸_L`, as a continuous group
homomorphism `GL_n(𝔸_K) → GL_n(𝔸_L)`. -/
def adelicCoefficientExtension : AdelicGL K n →ₜ* AdelicGL L n where
  toMonoidHom := GeneralLinearGroup.map (adeleInclusion (K := K) (L := L))
  continuous_toFun := continuous_adeleInclusion.generalLinearGroup_map

omit [FiniteDimensional K L] in
/-- `adelicCoefficientExtension` is entrywise application of the adele inclusion. -/
theorem adelicCoefficientExtension_apply (x : AdelicGL K n) :
    adelicCoefficientExtension (L := L) x =
      GeneralLinearGroup.map (adeleInclusion (K := K) (L := L)) x := rfl

omit [FiniteDimensional K L] in
/-- On rational matrices, coefficient extension is the scalar extension `GL_n(K) → GL_n(L)`. -/
theorem adelicCoefficientExtension_rational (g : GeneralLinear n K) :
    adelicCoefficientExtension (K := K) (L := L) (AdelicGL.rational K n g) =
      AdelicGL.rational L n (baseChange K L n g) := by
  ext i j
  exact adeleInclusion_diagonal (g i j)

omit [FiniteDimensional K L] in
/-- Coefficient extension `GL_n(𝔸_K) → GL_n(𝔸_L)` is injective. -/
theorem adelicCoefficientExtension_injective :
    Function.Injective (adelicCoefficientExtension (K := K) (L := L) (n := n)) := by
  intro x x' h
  apply Units.ext
  ext i j
  exact Langlands.ClassFieldTheory.Global.IdeleGaloisDescentProof.adeleInclusion_injective
    (K := K) (E := L) (congrArg (fun z : AdelicGL L n => z i j) h)

omit [FiniteDimensional K L] in
/-- The adelic absolute value of the determinant of the coefficient extension of `x` is the
`[L : K]`-th power of that of `x`. -/
theorem determinantNorm_adelicCoefficientExtension (x : AdelicGL K n) :
    determinantNorm L n (adelicCoefficientExtension x) =
      determinantNorm K n x ^ Module.finrank K L := by
  change IdeleAbsoluteValue.full L (GeneralLinearGroup.det
    (GeneralLinearGroup.map (adeleInclusion (K := K) (L := L)) x)) = _
  rw [GeneralLinearGroup.map_det]
  change IdeleAbsoluteValue.full L (ideleInclusion (K := K) (L := L) (GeneralLinearGroup.det x)) = _
  rw [← full_ideleNorm K L, ideleNorm_ideleInclusion, map_pow]
  rfl

/-- The coefficient extension of `x` has determinant of absolute value one exactly when `x`
does. -/
theorem adelicCoefficientExtension_mem_determinantNormOne_iff (x : AdelicGL K n) :
    adelicCoefficientExtension (K := K) (L := L) x ∈ AdelicGL.determinantNormOne L n ↔
      x ∈ AdelicGL.determinantNormOne K n := by
  change determinantNorm L n (adelicCoefficientExtension x) = 1 ↔ determinantNorm K n x = 1
  rw [determinantNorm_adelicCoefficientExtension]
  constructor
  · intro h
    apply Units.ext
    change (determinantNorm K n x).val = (1 : ℝ≥0)
    apply (pow_left_inj₀ zero_le zero_le (Module.finrank_pos (R := K) (M := L)).ne').mp
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, one_pow] using congrArg Units.val h
  · intro h
    rw [h, one_pow]

omit [FiniteDimensional K L] in
/-- The adelic Galois transport fixes matrices with coefficients in `𝔸_K`. -/
theorem adelicEquiv_adelicCoefficientExtension (hcyc : IsCyclicAlgebra σ l) (x : AdelicGL K n) :
    AdelicGLTransport.adelicEquiv n σ.toRingEquiv (adelicCoefficientExtension (L := L) x) =
      adelicCoefficientExtension x := by
  rw [← entrywiseAut_adeleCoefficientAut]
  ext i j
  rw [entrywiseAut_apply_apply]
  exact (adeleCoefficientAut_fixed_iff K L hcyc _).mpr ⟨x i j, rfl⟩

omit [FiniteDimensional K L] in
/-- An adelic matrix over `𝔸_K` is rational exactly when its coefficient extension to `𝔸_L`
is rational. -/
theorem adelicCoefficientExtension_mem_range_rational_iff (hcyc : IsCyclicAlgebra σ l)
    (x : AdelicGL K n) :
    adelicCoefficientExtension (L := L) x ∈ (AdelicGL.rational L n).range ↔
      x ∈ (AdelicGL.rational K n).range := by
  constructor
  · rintro ⟨w, hw⟩
    have hfix : entrywiseAut σ n w = w := by
      apply AdelicGL.rational_injective L n
      calc AdelicGL.rational L n (entrywiseAut σ n w)
          = AdelicGLTransport.adelicEquiv n σ.toRingEquiv (AdelicGL.rational L n w) :=
            (AdelicGLTransport.adelicEquiv_rational n σ.toRingEquiv w).symm
        _ = AdelicGL.rational L n w := by
            rw [hw, adelicEquiv_adelicCoefficientExtension hcyc]
    obtain ⟨v, hv⟩ := IsCyclicAlgebra.exists_baseChange_eq_of_entrywiseAut_eq (F := K) (E := L)
      (n := n) hcyc hfix
    refine ⟨v, adelicCoefficientExtension_injective (K := K) (L := L) (n := n) ?_⟩
    rw [adelicCoefficientExtension_rational, hv, hw]
  · rintro ⟨v, rfl⟩
    exact ⟨baseChange K L n v, (adelicCoefficientExtension_rational v).symm⟩

omit [NumberField K] [FiniteDimensional K L] in
private theorem twistedConj_adelicRational' (σ : L ≃ₐ[K] L) (x δ : GeneralLinear n L) :
    twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv) (AdelicGL.rational L n x)
        (AdelicGL.rational L n δ) =
      AdelicGL.rational L n (x⁻¹ * δ * entrywiseAut σ n x) := by
  rw [twistedConj_apply, map_mul, map_mul, map_inv, AdelicGLTransport.adelicEquiv_rational]
  rfl

set_option maxHeartbeats 1400000 in
omit [FiniteDimensional K L] in
private theorem exactTwistedCentralizer_adelic'
    (hcyc : IsCyclicAlgebra σ l) {g : GeneralLinear n K} (hg : IsRegularSemisimple g)
    {a : AdelicGL L n}
    (hn : cyclicNorm (adeleCoefficientAut K L σ) l a = baseChange K (Adeles L) n g) :
    (∀ x : AdelicGL K n, Commute x (AdelicGL.rational K n g) →
      twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv)
        (adelicCoefficientExtension x) a = a) ∧
    (∀ y : AdelicGL L n, twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv) y a = a →
      ∃ x : AdelicGL K n, Commute x (AdelicGL.rational K n g) ∧
        adelicCoefficientExtension x = y) := by
  let s := adeleCoefficientAut K L σ
  let f := adeleInclusionAlgHom K L
  let e := exactRegularNormCentralizerEquiv f
    (Langlands.ClassFieldTheory.Global.IdeleGaloisDescentProof.adeleInclusion_injective
      (K := K) (E := L))
    (adeleCoefficientAut_fixed_iff K L hcyc) (adeleCoefficientAut_pow_eq_one hcyc) hg hn
  constructor
  · intro x hx
    let t : Subgroup.centralizer ({baseChange K (Adeles K) n g} : Set (AdelicGL K n)) :=
      ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr hx⟩
    have h := (mem_sigmaCentralizer s n a (e t).val).mp (e t).property
    exact h
  · intro y hy
    have hm : y ∈ sigmaCentralizer s n a := (mem_sigmaCentralizer s n a y).mpr hy
    obtain ⟨x, hx⟩ := e.surjective ⟨y, hm⟩
    exact ⟨x.val, Subgroup.mem_centralizer_singleton_iff.mp x.property, congrArg Subtype.val hx⟩

private theorem commute_of_inv_mul_conj_eq' {G : Type*} [Group G] {x y : G}
    (h : x⁻¹ * y * x = y) : Commute x y := by
  change x * y = y * x
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using
    (congrArg (fun z => x * z) h).symm

omit [FiniteDimensional K L] in
/-- An element of the norm-one points of `GL_n` centralizes `q` exactly when its adelic matrix
commutes with the matrix of `q`. -/
theorem mem_centralizer_iff_commute_adelicHomeomorph (q z : normOneSubgroup K GLₙ) :
    z ∈ twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q ↔
      Commute (GeneralLinearGroupPoints.adelicHomeomorph K n (z : AdelicGroupPoints K GLₙ))
        (GeneralLinearGroupPoints.adelicHomeomorph K n (q : AdelicGroupPoints K GLₙ)) := by
  let φ := GeneralLinearGroupPoints.adelicHomeomorph K n
  rw [mem_twistedCentralizer]
  constructor
  · intro hz
    have h : (z : AdelicGroupPoints K GLₙ)⁻¹ * (q : AdelicGroupPoints K GLₙ) *
        (z : AdelicGroupPoints K GLₙ) = q := congrArg Subtype.val hz
    exact (commute_of_inv_mul_conj_eq' h).map φ
  · intro hc
    apply Subtype.ext
    apply φ.injective
    change φ ((z : AdelicGroupPoints K GLₙ)⁻¹ * (q : AdelicGroupPoints K GLₙ) *
      (z : AdelicGroupPoints K GLₙ)) = φ q
    rw [map_mul, map_mul, map_inv, mul_assoc, ← hc.eq, inv_mul_cancel_left]

omit [FiniteDimensional K L] in
/-- The centralizer of a rational norm-one point of `GL_n` with regular semisimple matrix
coordinate is commutative. -/
theorem centralizer_commutative_of_isRegularSemisimple (q : normOneSubgroup K GLₙ)
    {b : GeneralLinear n K}
    (hb : GeneralLinearGroupPoints.adelicHomeomorph K n (q : AdelicGroupPoints K GLₙ) =
      AdelicGL.rational K n b) (hreg : IsRegularSemisimple b) :
    ∀ x y : twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q, x * y = y * x := by
  intro x y
  let φ := GeneralLinearGroupPoints.adelicHomeomorph K n
  have hx := (mem_centralizer_iff_commute_adelicHomeomorph q x.val).mp x.property
  have hy := (mem_centralizer_iff_commute_adelicHomeomorph q y.val).mp y.property
  rw [hb] at hx hy
  apply Subtype.ext
  apply Subtype.ext
  apply φ.injective
  change φ ((x : AdelicGroupPoints K GLₙ) * (y : AdelicGroupPoints K GLₙ)) =
    φ ((y : AdelicGroupPoints K GLₙ) * (x : AdelicGroupPoints K GLₙ))
  rw [map_mul, map_mul]
  exact adelicGL_commute_of_regular_rational_centralizer K n hreg hx hy

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
/-- Let `r` be a norm-one point of `Res_{L/K} GL_n` with rational matrix coordinate `a`, and
`q` a norm-one point of `GL_n` with regular semisimple rational matrix coordinate `b`, such
that `Φ(N(r)) y = y ι(b)` for a rational `y ∈ GL_n(L)`. Then there is a topological group
isomorphism `e` from the `θ`-centralizer of `r` onto the centralizer of `q` with
`ι(e(x)) = y⁻¹ Φ(x) y` in adelic matrix coordinates, and `e` matches rational points. -/
theorem exists_baseChangeCentralizerEquiv (hcyc : IsCyclicAlgebra σ l)
    (r : normOneSubgroup K Wₙ) (q : normOneSubgroup K GLₙ)
    {a y : GeneralLinear n L} {b : GeneralLinear n K}
    (ha : cyclicWeilAdelicMap K L n (r : AdelicGroupPoints K Wₙ) = AdelicGL.rational L n a)
    (hb : GeneralLinearGroupPoints.adelicHomeomorph K n (q : AdelicGroupPoints K GLₙ) =
      AdelicGL.rational K n b)
    (hy : cyclicWeilAdelicMap K L n (((List.range l).map fun k =>
        adelicAut K (unitGaloisAut K L GLₙ σ ^ k) (r : AdelicGroupPoints K Wₙ)).prod) *
        AdelicGL.rational L n y =
      AdelicGL.rational L n y *
        Matrix.GeneralLinearGroup.map (adeleInclusion (K := K) (L := L))
          (GeneralLinearGroupPoints.adelicHomeomorph K n (q : AdelicGroupPoints K GLₙ)))
    (hreg : IsRegularSemisimple b) :
    ∃ e : twistedCentralizer (Θₙ).toMonoidHom r ≃ₜ*
        twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q,
      (∀ x : twistedCentralizer (Θₙ).toMonoidHom r,
        adelicCoefficientExtension (L := L)
            (GeneralLinearGroupPoints.adelicHomeomorph K n
              ((e x : normOneSubgroup K GLₙ) : AdelicGroupPoints K GLₙ)) =
          (AdelicGL.rational L n y)⁻¹ *
            cyclicWeilAdelicMap K L n ((x : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ) *
              AdelicGL.rational L n y) ∧
      (∀ x : twistedCentralizer (Θₙ).toMonoidHom r,
        (e x : normOneSubgroup K GLₙ) ∈ rationalNormOneSubgroup K GLₙ ↔
          (x : normOneSubgroup K Wₙ) ∈ rationalNormOneSubgroup K Wₙ) := by
  obtain ⟨E, hE⟩ := (generalLinearWeilAdelicTwist K L n).1
  let en := generalLinearWeilNormOneHomeomorph K L n E hE
  let eG := GeneralLinearGroupPoints.normOneAdelicHomeomorph K n
  let t := AdelicGLTransport.adelicEquiv n σ.toRingEquiv
  let A := AdelicGL.rational L n a
  let B := AdelicGL.rational L n y
  let a' := twistedConj t B A
  have hy' : y⁻¹ * cyclicNorm σ l a * y = baseChange K L n b := by
    rw [cyclicWeilAdelicMap_norm σ l _ a ha, hb, adeleInclusion_map_rational, ← map_mul,
      ← map_mul] at hy
    rw [mul_assoc, inv_mul_eq_iff_eq_mul]
    exact AdelicGL.rational_injective L n hy
  have hN : cyclicNorm (adeleCoefficientAut K L σ) l a' = baseChange K (Adeles L) n b := by
    change cyclicNorm (adeleCoefficientAut K L σ) l
      (twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv) (AdelicGL.rational L n y)
        (AdelicGL.rational L n a)) = _
    rw [twistedConj_adelicRational', cyclicNorm_adelicRational, cyclicNorm_twistedConj,
      hcyc.pow_eq_one, entrywiseAut_one_apply, hy']
    rfl
  obtain ⟨hforward, hback⟩ := exactTwistedCentralizer_adelic' hcyc hreg hN
  let Cq := twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) q
  let Cr := twistedCentralizer (Θₙ).toMonoidHom r
  let j : AdelicGL K n →ₜ* AdelicGL L n := adelicCoefficientExtension
  have hconj (x : normOneSubgroup K Wₙ) : (en (twistedConj Θₙ x r)).val =
      twistedConj t (en x).val (en r).val :=
    generalLinearWeilNormOne_twistedConj (σ := σ) E hE x r
  have hEx (z : normOneSubgroup K Wₙ) :
      (en z).val = cyclicWeilAdelicMap K L n (z : AdelicGroupPoints K Wₙ) := congrFun hE _
  have hr' : (en r).val = A := (hEx r).trans ha
  have hcomm (x : Cq) : Commute (eG x.val).val (AdelicGL.rational K n b) := by
    have h : Commute (eG x.val).val
        (GeneralLinearGroupPoints.adelicHomeomorph K n (q : AdelicGroupPoints K GLₙ)) :=
      (mem_centralizer_iff_commute_adelicHomeomorph q x.val).mp x.property
    rwa [hb] at h
  have hjn (z : AdelicGL K n) (hz : z ∈ AdelicGL.determinantNormOne K n) :
      determinantNorm L n (j z) = 1 :=
    (adelicCoefficientExtension_mem_determinantNormOne_iff (L := L) z).2 hz
  obtain ⟨f, hf, hfc⟩ : ∃ f : Cq →* AdelicGL L n,
      (∀ x : Cq, f x = B * j (eG x.val).val * B⁻¹) ∧ Continuous f := by
    refine ⟨(MulAut.conj B).toMonoidHom.comp (j.toMonoidHom.comp
      ((AdelicGL.determinantNormOne K n).subtype.comp
        (eG.toMulEquiv.toMonoidHom.comp Cq.subtype))), fun _ => rfl, ?_⟩
    have hc : Continuous (fun x : Cq => j (eG x.val).val) :=
      j.continuous.comp (continuous_subtype_val.comp (eG.continuous.comp continuous_subtype_val))
    exact (continuous_const.mul hc).mul continuous_const
  have hnorm (x : Cq) : f x ∈ AdelicGL.determinantNormOne L n := by
    change determinantNorm L n (f x) = 1
    rw [hf, map_mul, map_mul, map_inv, hjn _ (eG x.val).property, mul_one, mul_inv_cancel]
  have hC (x : Cq) : en.symm ⟨f x, hnorm x⟩ ∈ Cr := by
    change twistedConj Θₙ (en.symm ⟨f x, hnorm x⟩) r = r
    apply en.injective
    apply Subtype.ext
    rw [hconj, en.apply_symm_apply, hr']
    apply (conj_mem_twistedCentralizer_iff t B A (f x)).mp
    change twistedConj t (B⁻¹ * f x * B) a' = a'
    rw [show B⁻¹ * f x * B = j (eG x.val).val by rw [hf]; group]
    exact hforward (eG x.val).val (hcomm x)
  obtain ⟨F, hFf, hFc⟩ : ∃ F : Cq →* Cr, (∀ x : Cq, (en (F x).val).val = f x) ∧ Continuous F := by
    let f₁ := f.codRestrict (AdelicGL.determinantNormOne L n) hnorm
    let f₂ := en.symm.toMonoidHom.comp f₁
    refine ⟨f₂.codRestrict Cr hC, fun x => congrArg Subtype.val (en.apply_symm_apply (f₁ x)), ?_⟩
    exact (en.symm.continuous.comp (hfc.subtype_mk hnorm)).subtype_mk hC
  have hinj : Function.Injective F := by
    intro x x' h
    have h2 : f x = f x' := by rw [← hFf, ← hFf, h]
    rw [hf, hf] at h2
    have h3 : j (eG x.val).val = j (eG x'.val).val := mul_left_cancel (mul_right_cancel h2)
    exact Subtype.ext (eG.injective (Subtype.ext
      (adelicCoefficientExtension_injective (K := K) (L := L) (n := n) h3)))
  have hs : Function.Surjective F := by
    intro z
    have hzc : twistedConj t (en z.val).val A = A := by
      have hz : twistedConj Θₙ z.val r = r := z.property
      have h := hconj z.val
      rw [hz, hr'] at h
      exact h.symm
    have hz' : twistedConj t (B⁻¹ * (en z.val).val * B) a' = a' :=
      (conj_mem_twistedCentralizer_iff t B A _).mpr hzc
    obtain ⟨v, hvc, hv⟩ := hback _ hz'
    have hvn : determinantNorm L n (j v) = 1 := by
      change j v = B⁻¹ * (en z.val).val * B at hv
      have hwn : determinantNorm L n (en z.val).val = 1 := (en z.val).property
      rw [hv, map_mul, map_mul, map_inv, hwn, mul_one, inv_mul_cancel]
    let v₁ : AdelicGL.determinantNormOne K n :=
      ⟨v, (adelicCoefficientExtension_mem_determinantNormOne_iff v).mp hvn⟩
    have hv₂ : (eG (eG.symm v₁)).val = v := congrArg Subtype.val (eG.apply_symm_apply v₁)
    have hmem : eG.symm v₁ ∈ Cq := by
      apply (mem_centralizer_iff_commute_adelicHomeomorph q (eG.symm v₁)).mpr
      change Commute (eG (eG.symm v₁)).val
        (GeneralLinearGroupPoints.adelicHomeomorph K n (q : AdelicGroupPoints K GLₙ))
      rw [hv₂, hb]
      exact hvc
    refine ⟨⟨eG.symm v₁, hmem⟩, Subtype.ext (en.injective (Subtype.ext ?_))⟩
    rw [hFf, hf]
    change B * j (eG (eG.symm v₁)).val * B⁻¹ = (en z.val).val
    rw [hv₂, show j v = B⁻¹ * (en z.val).val * B from hv]
    group
  have hCq : IsClosed (Cq : Set (normOneSubgroup K GLₙ)) :=
    isClosed_twistedCentralizer (MonoidHom.id (normOneSubgroup K GLₙ)) continuous_id q
  have hCr : IsClosed (Cr : Set (normOneSubgroup K Wₙ)) :=
    isClosed_twistedCentralizer (Θₙ).toMonoidHom (Θₙ).continuous r
  have : LocallyCompactSpace Cq := hCq.locallyCompactSpace
  have : SecondCountableTopology Cq :=
    TopologicalSpace.Subtype.secondCountableTopology (Cq : Set (normOneSubgroup K GLₙ))
  have : LocallyCompactSpace Cr := hCr.locallyCompactSpace
  obtain ⟨e', he'⟩ := exists_continuousMulEquiv_of_bijective F hFc ⟨hinj, hs⟩
  have hcoord (x : Cr) : j (eG (e'.symm x).val).val =
      B⁻¹ * cyclicWeilAdelicMap K L n ((x : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ) * B := by
    have h1 : f (e'.symm x) = (en x.val).val := by
      rw [← hFf, ← he', e'.apply_symm_apply]
    rw [hf, hEx] at h1
    rw [← h1]
    group
  refine ⟨e'.symm, hcoord, fun x => ?_⟩
  have hB : B ∈ (AdelicGL.rational L n).range := ⟨y, rfl⟩
  rw [mem_rationalNormOneSubgroup_gl_iff, mem_rationalNormOneSubgroup_weil_iff,
    ← adelicCoefficientExtension_mem_range_rational_iff (L := L) hcyc]
  change j (eG (e'.symm x).val).val ∈ _ ↔ _
  rw [hcoord]
  constructor
  · intro h
    have h' := mul_mem (mul_mem hB h) (inv_mem hB)
    rwa [show B * (B⁻¹ * cyclicWeilAdelicMap K L n
      ((x : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ) * B) * B⁻¹ =
        cyclicWeilAdelicMap K L n ((x : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ) by
          group] at h'
  · intro h
    exact mul_mem (mul_mem (inv_mem hB) h) hB

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
/-- If `Φ(N(r)) y = y ι(b)` for rational coordinates `a` of `r` and `b` of `q`, and either
`Φ(N(r))` is regular elliptic at a finite place of `L` or the coordinate of `q` is regular
elliptic at a finite place of `K`, then `b` is regular semisimple. -/
theorem isRegularSemisimple_of_baseChangeNormRelated (σ : L ≃ₐ[K] L) (l : ℕ)
    (r : normOneSubgroup K Wₙ) (q : normOneSubgroup K GLₙ)
    {a y : GeneralLinear n L} {b : GeneralLinear n K}
    (ha : cyclicWeilAdelicMap K L n (r : AdelicGroupPoints K Wₙ) = AdelicGL.rational L n a)
    (hb : GeneralLinearGroupPoints.adelicHomeomorph K n (q : AdelicGroupPoints K GLₙ) =
      AdelicGL.rational K n b)
    (hy : cyclicWeilAdelicMap K L n (((List.range l).map fun k =>
        adelicAut K (unitGaloisAut K L GLₙ σ ^ k) (r : AdelicGroupPoints K Wₙ)).prod) *
        AdelicGL.rational L n y =
      AdelicGL.rational L n y *
        Matrix.GeneralLinearGroup.map (adeleInclusion (K := K) (L := L))
          (GeneralLinearGroupPoints.adelicHomeomorph K n (q : AdelicGroupPoints K GLₙ)))
    (w : Langlands.Global.FinitePlace L) (v : Langlands.Global.FinitePlace K)
    (hreg : IsRegularElliptic (FiniteAdelicGL.localProjection L n w
        (AdelicGL.finite L n (cyclicWeilAdelicMap K L n (((List.range l).map fun k =>
          adelicAut K (unitGaloisAut K L GLₙ σ ^ k) (r : AdelicGroupPoints K Wₙ)).prod)))) ∨
      IsRegularElliptic (FiniteAdelicGL.localProjection K n v
        (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n
          (q : AdelicGroupPoints K GLₙ))))) :
    IsRegularSemisimple b := by
  rw [cyclicWeilAdelicMap_norm σ l _ a ha] at hy hreg
  rw [hb] at hy hreg
  rcases hreg with h | h
  · have hN := isRegularSemisimple_of_localProjection_rational L n w _ h
    rw [adeleInclusion_map_rational, ← map_mul, ← map_mul] at hy
    have hy' : y⁻¹ * cyclicNorm σ l a * y = baseChange K L n b := by
      rw [mul_assoc, inv_mul_eq_iff_eq_mul]
      exact AdelicGL.rational_injective L n hy
    apply isRegularSemisimple_of_baseChange (L := L)
    rw [← hy']
    exact (isRegularSemisimple_conj_iff y _).mpr hN
  · exact isRegularSemisimple_of_localProjection_rational K n v b h

end Centralizer

end Langlands.TraceFormula
