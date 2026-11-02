import Langlands.Algebra.NagataOpennessCriterion
import Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_isOpen_setOf_flat_localization_atPrime
import Langlands.Algebra.GenericFlatness
import Langlands.Algebra.IdealLocalFlatnessCriterion
import Langlands.Algebra.LocalFlatnessCriterion
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-! # Openness of the flat locus over a Noetherian base -/

open TensorProduct

namespace Langlands.Algebra

namespace NoetherianFlatLocus

section Transfer

variable {A : Type*} [CommRing A] (S : Submonoid A) (R' : Type*) [CommRing R'] [Algebra A R']
  [IsLocalization S R'] {X : Type*} [AddCommGroup X] [Module A X] [Module R' X]
  [IsScalarTower A R' X]

include S in
/-- Tensor injectivity for an ideal passes to its extension in a localization. -/
theorem rTensor_map_injective (J : Ideal A) (hJ : Function.Injective (J.subtype.rTensor X)) :
    Function.Injective ((J.map (algebraMap A R')).subtype.rTensor X) := by
  set I' := J.map (algebraMap A R')
  let φ : J →ₗ[A] I' :=
    { toFun := fun a => ⟨algebraMap A R' a, Ideal.mem_map_of_mem _ a.2⟩
      map_add' := fun a b => Subtype.ext (map_add _ _ _)
      map_smul' := fun r a => Subtype.ext (by simp [Algebra.smul_def]) }
  let ψ : J ⊗[A] X →ₗ[A] I' ⊗[R'] X :=
    TensorProduct.lift (((TensorProduct.mk R' I' X).restrictScalars₁₂ A A) ∘ₗ φ)
  have hψ (a : J) (x : X) : ψ (a ⊗ₜ x) = φ a ⊗ₜ x := rfl
  have hcomm (w : J ⊗[A] X) : TensorProduct.lid R' X (I'.subtype.rTensor X (ψ w)) =
      TensorProduct.lid A X (J.subtype.rTensor X w) := by
    induction w using TensorProduct.inductionOn with
    | tmul a x => simp [hψ, φ, algebraMap_smul]
    | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  have hsurj : Function.Surjective ψ := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul y x =>
      obtain ⟨⟨a, s⟩, hy⟩ := (IsLocalization.mem_map_algebraMap_iff S R').mp y.2
      refine ⟨a ⊗ₜ (IsLocalization.mk' R' (1 : A) s • x), ?_⟩
      rw [hψ, ← TensorProduct.smul_tmul]
      congr 1
      apply Subtype.ext
      change IsLocalization.mk' R' (1 : A) s * algebraMap A R' a = y
      rw [← hy, mul_comm (y : R'), ← mul_assoc, IsLocalization.mk'_spec, map_one, one_mul]
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨w₁, rfl⟩ := h₁
      obtain ⟨w₂, rfl⟩ := h₂
      exact ⟨w₁ + w₂, map_add _ _ _⟩
  intro z₁ z₂ h
  obtain ⟨w₁, rfl⟩ := hsurj z₁
  obtain ⟨w₂, rfl⟩ := hsurj z₂
  have h' := congrArg (TensorProduct.lid R' X) h
  rw [hcomm, hcomm] at h'
  rw [hJ ((TensorProduct.lid A X).injective h')]

end Transfer

section Kernel

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing B]

omit [IsNoetherianRing B] in
/-- The localized tensor inclusion `B_Q ⊗ I → B_Q ⊗ A`, compared with the global one. -/
private theorem lTensor_comp_rTensor (I : Ideal A) (Q : Ideal B) [Q.IsPrime] (w : B ⊗[A] I) :
    I.subtype.lTensor (Localization.AtPrime Q)
        (TensorProduct.AlgebraTensorModule.rTensor A I
          (Algebra.linearMap B (Localization.AtPrime Q)) w) =
      TensorProduct.AlgebraTensorModule.rTensor A A
          (Algebra.linearMap B (Localization.AtPrime Q))
        (TensorProduct.AlgebraTensorModule.lTensor B B I.subtype w) := by
  induction w using TensorProduct.inductionOn with
  | tmul b a => simp
  | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- If `I ⊗ B_Q → B_Q` is injective, then `I ⊗ B_{Q'} → B_{Q'}` is injective for all primes
`Q'` in a basic open neighbourhood of `Q`. -/
theorem exists_forall_rTensor_injective (I : Ideal A) [Module.Finite A I] (Q : Ideal B)
    [Q.IsPrime] (hQ : Function.Injective (I.subtype.rTensor (Localization.AtPrime Q))) :
    ∃ g ∉ Q, ∀ (Q' : Ideal B) [Q'.IsPrime], g ∉ Q' →
      Function.Injective (I.subtype.rTensor (Localization.AtPrime Q')) := by
  let φ := TensorProduct.AlgebraTensorModule.lTensor B B I.subtype
  let K := LinearMap.ker φ
  have hK : ∀ k : K, ∃ r ∉ Q, r • k = 0 := by
    intro k
    have hk : φ k = 0 := k.2
    have h0 : TensorProduct.AlgebraTensorModule.rTensor A I
        (Algebra.linearMap B (Localization.AtPrime Q)) (k : B ⊗[A] I) = 0 := by
      apply ((LinearMap.lTensor_inj_iff_rTensor_inj _ _).mpr hQ)
      rw [lTensor_comp_rTensor, map_zero]
      exact (congrArg _ hk).trans (map_zero _)
    obtain ⟨⟨r, hr⟩, hrk⟩ := (IsLocalizedModule.eq_zero_iff Q.primeCompl _).mp h0
    exact ⟨r, hr, Subtype.ext hrk⟩
  have hQK : (⟨Q, inferInstance⟩ : PrimeSpectrum B) ∉ Module.support B K :=
    Module.notMem_support_iff'.mpr hK
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at hQK
  obtain ⟨g, hgK, hgQ⟩ := hQK
  refine ⟨g, hgQ, fun Q' _ hgQ' => ?_⟩
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  rw [injective_iff_map_eq_zero]
  intro z hz
  let ℓ := TensorProduct.AlgebraTensorModule.rTensor A I
    (Algebra.linearMap B (Localization.AtPrime Q'))
  obtain ⟨⟨w, s⟩, hws⟩ := IsLocalizedModule.surj Q'.primeCompl ℓ z
  have h1 : TensorProduct.AlgebraTensorModule.rTensor A A
      (Algebra.linearMap B (Localization.AtPrime Q')) (φ w) = 0 := by
    rw [← lTensor_comp_rTensor]
    change I.subtype.lTensor _ (ℓ w) = 0
    have hsz := (TensorProduct.AlgebraTensorModule.lTensor B (Localization.AtPrime Q')
      I.subtype).map_smul (s : B) z
    simp only [TensorProduct.AlgebraTensorModule.coe_lTensor] at hsz
    rw [← hws, Submonoid.smul_def, hsz, hz, smul_zero]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff Q'.primeCompl _).mp h1
  have htw : (t : B) • w ∈ K := by
    change φ ((t : B) • w) = 0
    rw [map_smul]
    exact ht
  have hg : g • (⟨(t : B) • w, htw⟩ : K) = 0 := Module.mem_annihilator.mp hgK _
  have hg' : (g * t) • w = 0 := by
    rw [mul_smul]
    exact congrArg Subtype.val hg
  have hu : (g * t * s : B) ∈ Q'.primeCompl :=
    Q'.primeCompl.mul_mem (Q'.primeCompl.mul_mem hgQ' t.2) s.2
  have hz' : (⟨g * t * s, hu⟩ : Q'.primeCompl) • z = 0 := by
    rw [Submonoid.smul_def]
    change ((g * t) * (s : B)) • z = 0
    rw [mul_smul, ← Submonoid.smul_def, hws, ← map_smul, hg', map_zero]
  have hinj := ((Module.End.isUnit_iff _).mp
    (IsLocalizedModule.map_units ℓ ⟨g * t * s, hu⟩)).1
  apply hinj
  rw [map_zero]
  simpa only [Module.algebraMap_end_apply, Submonoid.smul_def] using hz'

end Kernel

section Flatness

/-- Flatness of the localization at a prime passes to the localizations at smaller primes. -/
theorem flat_atPrime_of_le {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {Q' Q : Ideal B} [Q'.IsPrime] [Q.IsPrime] (h : Q' ≤ Q)
    [Module.Flat A (Localization.AtPrime Q)] : Module.Flat A (Localization.AtPrime Q') := by
  have hle : Q.primeCompl ≤ Q'.primeCompl := fun x hx hx' => hx (h hx')
  let : Algebra (Localization.AtPrime Q) (Localization.AtPrime Q') :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ Q.primeCompl Q'.primeCompl hle
  have : IsScalarTower B (Localization.AtPrime Q) (Localization.AtPrime Q') :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  have : IsLocalization (Q'.primeCompl.map (algebraMap B (Localization.AtPrime Q)))
      (Localization.AtPrime Q') :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ _ hle
  have : Module.Flat (Localization.AtPrime Q) (Localization.AtPrime Q') :=
    IsLocalization.flat _ (Q'.primeCompl.map (algebraMap B (Localization.AtPrime Q)))
  have : IsScalarTower A (Localization.AtPrime Q) (Localization.AtPrime Q') :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q'),
        IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q),
        ← IsScalarTower.algebraMap_apply B (Localization.AtPrime Q) (Localization.AtPrime Q')]
  exact Module.Flat.trans A (Localization.AtPrime Q) (Localization.AtPrime Q')

/-- A localization of `C` at a submonoid containing `c` is flat over `R` as soon as `C[1/c]` is. -/
theorem flat_of_isLocalization_of_flat_away {R C Y : Type*} [CommRing R] [CommRing C]
    [CommRing Y] [Algebra R C] [Algebra C Y] [Algebra R Y] [IsScalarTower R C Y]
    (T : Submonoid C) [IsLocalization T Y] {c : C} (hc : c ∈ T)
    [Module.Flat R (Localization.Away c)] : Module.Flat R Y := by
  have hle : Submonoid.powers c ≤ T := Submonoid.powers_le.mpr hc
  let : Algebra (Localization.Away c) Y :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers c) T hle
  have : IsScalarTower C (Localization.Away c) Y :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  have : IsLocalization (T.map (algebraMap C (Localization.Away c))) Y :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ _ hle
  have : Module.Flat (Localization.Away c) Y :=
    IsLocalization.flat _ (T.map (algebraMap C (Localization.Away c)))
  have : IsScalarTower R (Localization.Away c) Y :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R C Y,
        IsScalarTower.algebraMap_apply R C (Localization.Away c),
        ← IsScalarTower.algebraMap_apply C (Localization.Away c) Y]
  exact Module.Flat.trans R (Localization.Away c) Y

set_option backward.isDefEq.respectTransparency false in
/-- If `((A ⧸ p) ⊗[A] B)[1/a]` is flat over `A ⧸ p` and `a ∉ Q'`, then `(A ⧸ p) ⊗[A] B_{Q'}` is
flat over `A ⧸ p`. -/
theorem flat_quotient_tensor_atPrime {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (a : A)
    [Module.Flat (A ⧸ p)
      (Localization.Away (algebraMap (A ⧸ p) ((A ⧸ p) ⊗[A] B) (Ideal.Quotient.mk p a)))]
    (Q' : Ideal B) [Q'.IsPrime] (ha : algebraMap A B a ∉ Q') :
    Module.Flat (A ⧸ p) ((A ⧸ p) ⊗[A] Localization.AtPrime Q') := by
  let φ := Algebra.TensorProduct.map (AlgHom.id (A ⧸ p) (A ⧸ p))
    (IsScalarTower.toAlgHom A B (Localization.AtPrime Q'))
  let instCY : Algebra ((A ⧸ p) ⊗[A] B) ((A ⧸ p) ⊗[A] Localization.AtPrime Q') :=
    φ.toRingHom.toAlgebra
  have : IsScalarTower (A ⧸ p) ((A ⧸ p) ⊗[A] B) ((A ⧸ p) ⊗[A] Localization.AtPrime Q') :=
    IsScalarTower.of_algHom φ
  have := IsLocalization.tensorProduct_tensorProduct_right A (A ⧸ p) Q'.primeCompl
    (Localization.AtPrime Q') (by ext x; simp [instCY, φ, RingHom.algebraMap_toAlgebra])
  refine flat_of_isLocalization_of_flat_away
    (Q'.primeCompl.map (Algebra.TensorProduct.includeRight (R := A) (A := A ⧸ p)))
    (c := algebraMap (A ⧸ p) ((A ⧸ p) ⊗[A] B) (Ideal.Quotient.mk p a)) ?_
  refine Submonoid.mem_map.mpr ⟨algebraMap A B a, ha, ?_⟩
  rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_eq_smul_one a, ← TensorProduct.smul_tmul, Algebra.algebraMap_self,
    RingHom.id_apply, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]

/-- The local flatness criterion at `Q'`: tensor injectivity for an ideal `p ≤ Q' ∩ A` and
flatness of `(A ⧸ p) ⊗[A] B_{Q'}` over `A ⧸ p` give flatness of `B_{Q'}` over `A`. -/
theorem flat_atPrime_of_rTensor_injective {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] (p : Ideal A) (Q' : Ideal B) [Q'.IsPrime]
    (hp : p ≤ Q'.comap (algebraMap A B))
    (hinj : Function.Injective (p.subtype.rTensor (Localization.AtPrime Q')))
    [Module.Flat (A ⧸ p) ((A ⧸ p) ⊗[A] Localization.AtPrime Q')] :
    Module.Flat A (Localization.AtPrime Q') := by
  have hinj' : Function.Injective
      ((Q'.comap (algebraMap A B)).subtype.rTensor (Localization.AtPrime Q')) :=
    idealTensor_injective_of_quotient_flat p _ hp hinj
  let : Algebra (Localization.AtPrime (Q'.comap (algebraMap A B))) (Localization.AtPrime Q') :=
    (Localization.localRingHom (Q'.comap (algebraMap A B)) Q' (algebraMap A B) rfl).toAlgebra
  have : IsLocalHom (algebraMap (Localization.AtPrime (Q'.comap (algebraMap A B)))
      (Localization.AtPrime Q')) :=
    Localization.isLocalHom_localRingHom _ Q' (algebraMap A B) rfl
  have : IsScalarTower A (Localization.AtPrime (Q'.comap (algebraMap A B)))
      (Localization.AtPrime Q') :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map,
        IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q')]
  have hm := rTensor_map_injective (Q'.comap (algebraMap A B)).primeCompl
    (Localization.AtPrime (Q'.comap (algebraMap A B))) _ hinj'
  rw [Localization.AtPrime.map_eq_maximalIdeal] at hm
  have : Module.Flat (Localization.AtPrime (Q'.comap (algebraMap A B)))
      (Localization.AtPrime Q') :=
    localFlatnessCriterion _ (Localization.AtPrime Q') (Localization.AtPrime Q') hm
  have : Module.Flat A (Localization.AtPrime (Q'.comap (algebraMap A B))) :=
    IsLocalization.flat _ (Q'.comap (algebraMap A B)).primeCompl
  exact Module.Flat.trans A (Localization.AtPrime (Q'.comap (algebraMap A B)))
    (Localization.AtPrime Q')

end Flatness

end NoetherianFlatLocus

open NoetherianFlatLocus in
/-- Openness of the flat locus over a Noetherian base, assuming generic flatness of the fibres
`A ⧸ p → (A ⧸ p) ⊗[A] B`. -/
theorem isOpen_flatLocus_of_generic {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (hgen : ∀ p : Ideal A, p.IsPrime → ∃ a ∉ p, Module.Flat (A ⧸ p)
      (Localization.Away (algebraMap (A ⧸ p) ((A ⧸ p) ⊗[A] B) (Ideal.Quotient.mk p a)))) :
    IsOpen {Q : PrimeSpectrum B | Module.Flat A (Localization.AtPrime Q.asIdeal)} := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  apply isOpen_of_stableUnderGeneralization_of_forall_exists
  · intro x y hyx hx
    have : Module.Flat A (Localization.AtPrime x.asIdeal) := hx
    exact flat_atPrime_of_le ((PrimeSpectrum.le_iff_specializes y x).mpr hyx)
  · intro Q hQ
    have : Module.Flat A (Localization.AtPrime Q.asIdeal) := hQ
    obtain ⟨g, hgQ, hg⟩ := exists_forall_rTensor_injective (Q.asIdeal.comap (algebraMap A B))
      Q.asIdeal (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
    obtain ⟨a, haQ, ha⟩ := hgen (Q.asIdeal.comap (algebraMap A B)) inferInstance
    refine ⟨algebraMap A B a * g, Q.2.mul_notMem haQ hgQ, fun Q' hQQ' hf => ?_⟩
    have haQ' : algebraMap A B a ∉ Q'.asIdeal := fun h => hf (Q'.asIdeal.mul_mem_right _ h)
    have hgQ' : g ∉ Q'.asIdeal := fun h => hf (Q'.asIdeal.mul_mem_left _ h)
    have := flat_quotient_tensor_atPrime (Q.asIdeal.comap (algebraMap A B)) a Q'.asIdeal haQ'
    exact flat_atPrime_of_rTensor_injective _ Q'.asIdeal (Ideal.comap_mono hQQ') (hg _ hgQ')

open GenericFlatness in
/-- Generic flatness of the fibres: for a prime `p` of a Noetherian ring `A` and a finite type
`A`-algebra `B`, some `a ∉ p` makes `((A ⧸ p) ⊗[A] B)[1/a]` flat over `A ⧸ p`. -/
theorem exists_flat_away_quotient_tensor {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FiniteType A B] (p : Ideal A) [p.IsPrime] :
    ∃ a ∉ p, Module.Flat (A ⧸ p)
      (Localization.Away (algebraMap (A ⧸ p) ((A ⧸ p) ⊗[A] B) (Ideal.Quotient.mk p a))) := by
  obtain ⟨d, hd, hflat⟩ :=
    genFlat_of_finiteType (A := A ⧸ p) ((A ⧸ p) ⊗[A] B) ((A ⧸ p) ⊗[A] B)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
  refine ⟨a, fun ha => hd (Ideal.Quotient.eq_zero_iff_mem.mpr ha), ?_⟩
  have hloc : IsLocalizedModule (Submonoid.powers (Ideal.Quotient.mk p a))
      (IsScalarTower.toAlgHom (A ⧸ p) ((A ⧸ p) ⊗[A] B) (Localization.Away
        (algebraMap (A ⧸ p) ((A ⧸ p) ⊗[A] B) (Ideal.Quotient.mk p a)))).toLinearMap := by
    rw [isLocalizedModule_iff_isLocalization, Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact Localization.isLocalization
  have := hflat _ dvd_rfl
  exact (flat_localizedModule_iff _ (IsScalarTower.toAlgHom (A ⧸ p) ((A ⧸ p) ⊗[A] B)
    (Localization.Away (algebraMap (A ⧸ p) ((A ⧸ p) ⊗[A] B)
      (Ideal.Quotient.mk p a)))).toLinearMap).mp this

end Langlands.Algebra
