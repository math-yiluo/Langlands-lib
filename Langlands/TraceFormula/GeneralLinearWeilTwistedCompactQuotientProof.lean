import Langlands.BaseChange.ExactRegularNormCentralizer
import Langlands.Global.AdelicParabolicCompactCover
import Langlands.Global.IdeleNormAbsoluteValue
import Langlands.TraceFormula.AdelicRegularCentralizerCompact
import Langlands.TraceFormula.GeneralLinearWeilTwistedClosedOrbitProof
import Langlands.TraceFormula.TwistedOrbitalConjugation

/-! # Compact rational quotients of Weil twisted centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Matrix
open scoped CategoryTheory.MonObj NNReal
open Langlands.BaseChange Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.GroupScheme Langlands.JacquetLanglands Langlands.QuotientIntegration
open Langlands.Global.AdelicFunctoriality Langlands.Global.AdelicBlockDeterminantCharacter
open Langlands.TraceFormula.AdelicGroupAutomorphism

namespace Langlands.TraceFormula

local instance twistedEllipticProofGLAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance twistedEllipticProofGLSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "Wₙ" => weilGroup K L GLₙ

set_option hygiene false in
local notation "Θₙ" => normOneAut K (unitGaloisAut K L GLₙ σ)

section Compactness

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] {n l : ℕ} {σ : L ≃ₐ[K] L}

local instance (priority := low) twistedEllipticUpperAlgebra : Algebra K (Adeles L) :=
  ((algebraMap L (Adeles L)).comp (algebraMap K L)).toAlgebra

private def extendMatrixCoefficients : AdelicGL K n →ₜ* AdelicGL L n where
  toMonoidHom := GeneralLinearGroup.map (adeleInclusion (K := K) (L := L))
  continuous_toFun := continuous_adeleInclusion.generalLinearGroup_map

omit [FiniteDimensional K L] in
private theorem extendMatrixCoefficients_rational (g : GeneralLinear n K) :
    extendMatrixCoefficients (K := K) (L := L) (AdelicGL.rational K n g) =
      AdelicGL.rational L n (baseChange K L n g) := by
  ext i j
  exact adeleInclusion_diagonal (g i j)

omit [FiniteDimensional K L] in
private theorem determinantNorm_extendMatrixCoefficients (x : AdelicGL K n) :
    determinantNorm L n (extendMatrixCoefficients x) =
      determinantNorm K n x ^ Module.finrank K L := by
  change IdeleAbsoluteValue.full L (GeneralLinearGroup.det
    (GeneralLinearGroup.map (adeleInclusion (K := K) (L := L)) x)) = _
  rw [GeneralLinearGroup.map_det]
  change IdeleAbsoluteValue.full L (ideleInclusion (K := K) (L := L) (GeneralLinearGroup.det x)) = _
  rw [← full_ideleNorm K L, ideleNorm_ideleInclusion, map_pow]
  rfl

private theorem extendMatrixCoefficients_mem_determinantNormOne_iff (x : AdelicGL K n) :
    extendMatrixCoefficients (K := K) (L := L) x ∈ AdelicGL.determinantNormOne L n ↔
      x ∈ AdelicGL.determinantNormOne K n := by
  change determinantNorm L n (extendMatrixCoefficients x) = 1 ↔ determinantNorm K n x = 1
  rw [determinantNorm_extendMatrixCoefficients]
  constructor
  · intro h
    apply Units.ext
    change (determinantNorm K n x).val = (1 : ℝ≥0)
    apply (pow_left_inj₀ zero_le zero_le (Module.finrank_pos (R := K) (M := L)).ne').mp
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, one_pow] using congrArg Units.val h
  · intro h
    rw [h, one_pow]

omit [NumberField K] [FiniteDimensional K L] in
private theorem twistedConj_adelicRational (σ : L ≃ₐ[K] L) (x δ : GeneralLinear n L) :
    twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv) (AdelicGL.rational L n x)
        (AdelicGL.rational L n δ) =
      AdelicGL.rational L n (x⁻¹ * δ * entrywiseAut σ n x) := by
  rw [twistedConj_apply, map_mul, map_mul, map_inv, AdelicGLTransport.adelicEquiv_rational]
  rfl

private theorem mem_ordinaryNormOneCentralizer_iff (g : GeneralLinear n K)
    (x : AdelicGL.determinantNormOne K n) :
    x ∈ twistedCentralizer (ContinuousMulEquiv.refl _) (adelicDeterminantNormOnePoint K n g) ↔
      Commute x.val (AdelicGL.rational K n g) := by
  let a := AdelicGL.rational K n g
  rw [mem_twistedCentralizer]
  constructor
  · intro hx
    have h := congrArg Subtype.val hx
    change x.val⁻¹ * a * x.val = a at h
    show x.val * a = a * x.val
    calc
      x.val * a = x.val * (x.val⁻¹ * a * x.val) := congrArg (x.val * ·) h.symm
      _ = a * x.val := by group
  · intro hx
    apply Subtype.ext
    change x.val⁻¹ * a * x.val = a
    rw [mul_assoc, ← hx.eq, inv_mul_cancel_left]

set_option maxHeartbeats 1400000 in
omit [FiniteDimensional K L] in
private theorem exactTwistedCentralizer_adelic
    (hcyc : IsCyclicAlgebra σ l) {g : GeneralLinear n K} (hg : IsRegularSemisimple g)
    {a : AdelicGL L n}
    (hn : cyclicNorm (adeleCoefficientAut K L σ) l a = baseChange K (Adeles L) n g) :
    (∀ x : AdelicGL K n, Commute x (AdelicGL.rational K n g) →
      twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv)
        (extendMatrixCoefficients x) a = a) ∧
    (∀ y : AdelicGL L n, twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv) y a = a →
      ∃ x : AdelicGL K n, Commute x (AdelicGL.rational K n g) ∧
        extendMatrixCoefficients x = y) := by
  let s := adeleCoefficientAut K L σ
  let f := adeleInclusionAlgHom K L
  let e := exactRegularNormCentralizerEquiv f
    (Langlands.ClassFieldTheory.Global.IdeleGaloisDescentProof.adeleInclusion_injective (K := K) (E := L))
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

set_option maxHeartbeats 1500000 in
private theorem compact_twistedCentralizer_of_matrixCoordinates {H : Type*} [Group H]
    [TopologicalSpace H] (θ : H ≃ₜ* H) (r : H) (Λ : Subgroup H)
    (e : H ≃ₜ* AdelicGL.determinantNormOne L n) (δ : GeneralLinear n L)
    (he : ∀ x : H, (e (twistedConj θ x r)).val =
      twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv) (e x).val (e r).val)
    (hr : (e r).val = AdelicGL.rational L n δ)
    (hprincipal : ∀ x : H, (e x).val ∈ (AdelicGL.rational L n).range → x ∈ Λ)
    (hcyc : IsCyclicAlgebra σ l) (hδ : IsSigmaElliptic σ l δ) :
    IsCompactTwistedCentralizerQuotient Λ θ r := by
  obtain ⟨g, ⟨q, hq⟩, hgell⟩ := hδ
  let A := AdelicGL.determinantNormOne K n
  let C₀ := twistedCentralizer (ContinuousMulEquiv.refl A) (adelicDeterminantNormOnePoint K n g)
  let Γ₀ := (adelicDeterminantNormOneRational K n).subgroupOf C₀
  let C := twistedCentralizer θ r
  let Γ := Λ.subgroupOf C
  let t := AdelicGLTransport.adelicEquiv n σ.toRingEquiv
  let a := AdelicGL.rational L n δ
  let b := AdelicGL.rational L n q
  let a' := twistedConj t b a
  have hN : cyclicNorm (adeleCoefficientAut K L σ) l a' = baseChange K (Adeles L) n g := by
    change cyclicNorm (adeleCoefficientAut K L σ) l
      (twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv) (AdelicGL.rational L n q)
        (AdelicGL.rational L n δ)) = _
    rw [twistedConj_adelicRational, cyclicNorm_adelicRational, cyclicNorm_twistedConj,
      hcyc.pow_eq_one, entrywiseAut_one_apply, hq]
    rfl
  obtain ⟨hforward, hback⟩ := exactTwistedCentralizer_adelic hcyc hgell.1 hN
  let j : AdelicGL K n →ₜ* AdelicGL L n := extendMatrixCoefficients
  let f : C₀ →* AdelicGL L n :=
    (MulAut.conj b).toMonoidHom.comp (j.toMonoidHom.comp (A.subtype.comp C₀.subtype))
  have hf (x : C₀) : f x = b * j x.val.val * b⁻¹ := rfl
  have hnorm (x : C₀) : f x ∈ AdelicGL.determinantNormOne L n := by
    have h := (extendMatrixCoefficients_mem_determinantNormOne_iff (L := L) x.val.val).2 x.val.property
    change determinantNorm L n (j x.val.val) = 1 at h
    change determinantNorm L n (f x) = 1
    rw [hf, map_mul, map_mul, map_inv, h, mul_one, mul_inv_cancel]
  let f₁ := f.codRestrict (AdelicGL.determinantNormOne L n) hnorm
  let f₂ := e.symm.toMonoidHom.comp f₁
  have heF (x : C₀) : (e (f₂ x)).val = f x := congrArg Subtype.val (e.apply_symm_apply (f₁ x))
  have hC (x : C₀) : f₂ x ∈ C := by
    change twistedConj θ (f₂ x) r = r
    apply e.injective
    apply Subtype.ext
    rw [he, heF, hr]
    apply (conj_mem_twistedCentralizer_iff t b a (f x)).mp
    change twistedConj t (b⁻¹ * f x * b) a' = a'
    rw [show b⁻¹ * f x * b = j x.val.val by rw [hf]; group]
    exact hforward x.val.val ((mem_ordinaryNormOneCentralizer_iff g x.val).mp x.property)
  let F := f₂.codRestrict C hC
  have hcont : Continuous F := by
    have hc : Continuous (fun x : C₀ => j x.val.val) :=
      j.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hf' : Continuous (fun x : C₀ => f x) := by
      simp_rw [hf]
      exact (continuous_const.mul hc).mul continuous_const
    exact (e.symm.continuous.comp (hf'.subtype_mk hnorm)).subtype_mk hC
  have hs : Function.Surjective F := by
    intro y
    let z := (e y.val).val
    have hzc : twistedConj t z a = a := by
      have hy : twistedConj θ y.val r = r := y.property
      have hz := he y.val
      rw [hy, hr] at hz
      exact hz.symm
    have hz' : twistedConj t (b⁻¹ * z * b) a' = a' :=
      (conj_mem_twistedCentralizer_iff t b a z).mpr hzc
    obtain ⟨w, hwc, hw⟩ := hback _ hz'
    have hzw : j w ∈ AdelicGL.determinantNormOne L n := by
      change j w = b⁻¹ * z * b at hw
      have hzn : determinantNorm L n z = 1 := (e y.val).property
      change determinantNorm L n (j w) = 1
      rw [hw, map_mul, map_mul, map_inv, hzn, mul_one, inv_mul_cancel]
    let v : A := ⟨w, (extendMatrixCoefficients_mem_determinantNormOne_iff w).mp hzw⟩
    let x : C₀ := ⟨v, (mem_ordinaryNormOneCentralizer_iff g v).mpr hwc⟩
    refine ⟨x, Subtype.ext (e.injective (Subtype.ext ?_))⟩
    change (e (f₂ x)).val = z
    rw [heF, hf]
    change b * j w * b⁻¹ = z
    rw [show j w = b⁻¹ * z * b from hw]
    group
  have hΓ : Γ₀.map F ≤ Γ := by
    rintro _ ⟨x, hx, rfl⟩
    change x.val.val ∈ (AdelicGL.rational K n).range at hx
    obtain ⟨v, hv⟩ := hx
    change f₂ x ∈ Λ
    apply hprincipal
    rw [heF, hf, ← hv]
    refine ⟨q * baseChange K L n v * q⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv]
    change b * AdelicGL.rational L n (baseChange K L n v) * b⁻¹ =
      b * extendMatrixCoefficients (AdelicGL.rational K n v) * b⁻¹
    rw [extendMatrixCoefficients_rational]
  have hc₀ : CompactSpace (LeftQuotient Γ₀) :=
    adelicRegularCentralizerCompactQuotient K n g hgell.2 hgell.1
  change CompactSpace (LeftQuotient Γ)
  exact @compactSpace_leftQuotient_of_surjective C₀ _ _ C _ _ F hcont hs Γ₀ Γ hΓ hc₀

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 2000 in
/-- The rational quotient of the actual norm-one twisted centralizer is compact. -/
theorem generalLinearWeilTwistedCompactQuotient :
    GeneralLinearWeilTwistedCompactQuotientStatement.{u} := by
  intro K _ _ L _ _ _ _ σ l hcyc n r δ hr hδ
  let H := normOneSubgroup K Wₙ
  let Λ := rationalNormOneSubgroup K Wₙ
  obtain ⟨e, he⟩ := (generalLinearWeilAdelicTwist K L n).1
  let en := generalLinearWeilNormOneHomeomorph K L n e he
  have hconj (x : H) : (en (twistedConj Θₙ x r.val)).val =
      twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv) (en x).val (en r.val).val :=
    generalLinearWeilNormOne_twistedConj (σ := σ) e he x r.val
  have hr' : (en r.val).val = AdelicGL.rational L n δ := (congrFun he _).trans hr
  have hp (x : H) (hx : (en x).val ∈ (AdelicGL.rational L n).range) : x ∈ Λ := by
    have hcoord : e x.val = cyclicWeilAdelicMap K L n x.val := congrFun he _
    change e x.val ∈ (AdelicGL.rational L n).range at hx
    rw [hcoord] at hx
    have hm : x.val ∈ rationalSubgroup K Wₙ := ((generalLinearWeilAdelicTwist K L n).2.2 _).mpr hx
    obtain ⟨z, hz⟩ := hm
    exact ⟨z, Subtype.ext hz⟩
  exact compact_twistedCentralizer_of_matrixCoordinates Θₙ r.val Λ en δ hconj hr' hp hcyc hδ

end Compactness

end Langlands.TraceFormula
