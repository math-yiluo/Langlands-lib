import Langlands.AlgebraicGeometry.GroupoidCoactionSupport
import Mathlib.Algebra.Module.FinitePresentation

/-! # Hom modules of coactions -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {G M : Type v} [AddCommGroup G] [Module B G]
  [AddCommGroup M] [Module B M]

namespace GroupoidCoaction

section HomBaseChange

variable (B) (S : Type u) [CommRing S] [Algebra B S] [Module.Flat B S]
variable (G M) [Module.FinitePresentation B G]

/-- Flat base change of Hom from a finitely presented module. -/
noncomputable def homTensorEquiv :
    S ⊗[B] (G →ₗ[B] M) ≃ₗ[S] (S ⊗[B] G →ₗ[S] S ⊗[B] M) :=
  (Module.FinitePresentation.isBaseChange_map B G M S).equiv

@[simp]
lemma homTensorEquiv_tmul_apply (c d : S) (f : G →ₗ[B] M) (g : G) :
    homTensorEquiv (B := B) (S := S) (G := G) (M := M) (c ⊗ₜ f) (d ⊗ₜ g) = (c * d) ⊗ₜ f g := by
  simp [homTensorEquiv, smul_tmul', smul_eq_mul]

end HomBaseChange

section HomMap

variable [Module.Flat B C] [Module.FinitePresentation B G]
variable (hE : RingEtaleEquivalenceRelation t)
variable (θG : GroupoidCoaction t G) (θM : GroupoidCoaction t M)

/-- Conjugation of an extended linear map by the two reversal operators. -/
noncomputable def homConjugate (f : G →ₗ[B] M) :
    C ⊗[B] G →ₗ[C] C ⊗[B] M where
  toFun x := reverseTensor hE θM (f.baseChange C (reverseTensor hE θG x))
  map_add' x y := by simp
  map_smul' c x := by
    simp only [reverseTensor_smul, LinearMap.map_smul,
      hE.reversal_involutive c, RingHom.id_apply]

/-- The additive Hom coaction before verification of its laws. -/
noncomputable def homCoactionMap : (G →ₗ[B] M) →+ C ⊗[B] (G →ₗ[B] M) where
  toFun f := (homTensorEquiv (B := B) (S := C) (G := G) (M := M)).symm (homConjugate hE θG θM f)
  map_zero' := by
    apply (homTensorEquiv (B := B) (S := C) (G := G) (M := M)).injective
    ext x
    simp [homConjugate]
  map_add' f f' := by
    apply (homTensorEquiv (B := B) (S := C) (G := G) (M := M)).injective
    ext x
    simp [homConjugate]

lemma homCoactionMap_smul (b : B) (f : G →ₗ[B] M) :
    homCoactionMap hE θG θM (b • f) =
      t b • homCoactionMap hE θG θM f := by
  apply (homTensorEquiv (B := B) (S := C) (G := G) (M := M)).injective
  simp only [homCoactionMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    LinearEquiv.apply_symm_apply, LinearEquiv.map_smul]
  apply LinearMap.ext
  intro x
  change homConjugate hE θG θM (b • f) x =
    (t b • homConjugate hE θG θM f) x
  change reverseTensor hE θM ((b • f).baseChange C (reverseTensor hE θG x)) = _
  rw [LinearMap.baseChange_smul, LinearMap.smul_apply,
    ← IsScalarTower.algebraMap_smul C b]
  change reverseTensor hE θM
    ((algebraMap B C b) • f.baseChange C (reverseTensor hE θG x)) = _
  rw [reverseTensor_smul]
  have hb := congrArg (fun k : B →+* C => k b) hE.reversal_comp_source
  exact congrArg
    (fun c : C => c • reverseTensor hE θM (f.baseChange C (reverseTensor hE θG x))) hb

lemma homCoactionMap_eval (f : G →ₗ[B] M) (g : G) :
    homTensorEquiv (B := B) (S := C) (G := G) (M := M) (homCoactionMap hE θG θM f) (θG.coaction g) =
      θM.coaction (f g) := by
  simp [homCoactionMap, homConjugate, reverseTensor_coaction]

end HomMap

section Spanning

variable (hE : RingEtaleEquivalenceRelation t) (θG : GroupoidCoaction t G)
variable {S : Type u} [CommRing S] [Algebra B S]
variable {N : Type*} [AddCommGroup N] [Module S N]

include hE in
/-- Specialized coaction values generate the source extension of a module. -/
lemma linearMap_ext_coaction (φ : C →ₐ[B] S)
    {F H : S ⊗[B] G →ₗ[S] N}
    (h : ∀ g : G, F (LinearMap.rTensor G φ.toLinearMap (θG.coaction g)) =
      H (LinearMap.rTensor G φ.toLinearMap (θG.coaction g))) : F = H := by
  have hrev : ∀ x : C ⊗[B] G,
      F (LinearMap.rTensor G φ.toLinearMap (reverseTensor hE θG x)) =
        H (LinearMap.rTensor G φ.toLinearMap (reverseTensor hE θG x)) := by
    intro x
    induction x with
    | tmul c g =>
      rw [reverseTensor_tmul, rTensor_algHom_smul, LinearMap.map_smul,
        LinearMap.map_smul, h g]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hone (g : G) : F ((1 : S) ⊗ₜ g) = H ((1 : S) ⊗ₜ g) := by
    simpa only [reverseTensor_involutive hE θG (1 ⊗ₜ g), LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, map_one] using hrev (reverseTensor hE θG (1 ⊗ₜ g))
  apply LinearMap.ext
  intro x
  induction x with
  | tmul s g =>
    have hh := congrArg (fun x : N => s • x) (hone g)
    rw [← F.map_smul, ← H.map_smul, smul_tmul', smul_eq_mul, mul_one] at hh
    exact hh
  | add x y hx hy => simp only [map_add, hx, hy]

end Spanning

section HomNaturality

variable [Module.Flat B C] [Module.FinitePresentation B G]
variable {S : Type u} [CommRing S] [Algebra B S] [Module.Flat B S]

lemma homTensorEquiv_naturality (φ : C →ₐ[B] S)
    (x : C ⊗[B] (G →ₗ[B] M)) (y : C ⊗[B] G) :
    homTensorEquiv (B := B) (S := S) (G := G) (M := M) (LinearMap.rTensor _ φ.toLinearMap x)
      (LinearMap.rTensor _ φ.toLinearMap y) =
        LinearMap.rTensor M φ.toLinearMap (homTensorEquiv (B := B) (S := C) (G := G) (M := M) x y) := by
  induction x with
  | tmul c f =>
    induction y with
    | tmul d g => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

lemma homCoactionMap_eval_specialize (hE : RingEtaleEquivalenceRelation t)
    (θG : GroupoidCoaction t G) (θM : GroupoidCoaction t M)
    (φ : C →ₐ[B] S) (f : G →ₗ[B] M) (g : G) :
    homTensorEquiv (B := B) (S := S) (G := G) (M := M)
      (LinearMap.rTensor _ φ.toLinearMap (homCoactionMap hE θG θM f))
      (LinearMap.rTensor _ φ.toLinearMap (θG.coaction g)) =
        LinearMap.rTensor _ φ.toLinearMap (θM.coaction (f g)) := by
  rw [homTensorEquiv_naturality, homCoactionMap_eval]

end HomNaturality

section HomLaws

variable [Module.Flat B C] [Module.FinitePresentation B G]
variable (hE : RingEtaleEquivalenceRelation t)
variable (θG : GroupoidCoaction t G) (θM : GroupoidCoaction t M)
variable {S : Type u} [CommRing S] [Algebra B S] [Module.Flat B S]

lemma homCoactionMap_counit (φ : C →ₐ[B] S)
    (hφ : (φ : C →+* S).comp t = algebraMap B S) (f : G →ₗ[B] M) :
    LinearMap.rTensor _ φ.toLinearMap (homCoactionMap hE θG θM f) =
      (1 : S) ⊗ₜ f := by
  apply (homTensorEquiv (B := B) (S := S) (G := G) (M := M)).injective
  apply linearMap_ext_coaction hE θG φ
  intro g
  rw [homCoactionMap_eval_specialize, θG.counit S φ hφ,
    homTensorEquiv_tmul_apply, θM.counit S φ hφ]
  simp

lemma homCoactionMap_compose_eval (φ₁ : C →+* S) (φ₂ : C →ₐ[B] S)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* S).comp t)
    (x : C ⊗[B] (G →ₗ[B] M)) (y : C ⊗[B] G) :
    homTensorEquiv (B := B) (S := S) (G := G) (M := M)
      (coactionCompose t _ (homCoactionMap hE θG θM)
        (homCoactionMap_smul hE θG θM) φ₁ φ₂ h x)
      (coactionCompose t _ θG.coaction θG.map_smul φ₁ φ₂ h y) =
        coactionCompose t _ θM.coaction θM.map_smul φ₁ φ₂ h
          (homTensorEquiv (B := B) (S := C) (G := G) (M := M) x y) := by
  induction x with
  | tmul c f =>
    induction y with
    | tmul d g =>
      change homTensorEquiv (B := B) (S := S) (G := G) (M := M)
        (φ₁ c • LinearMap.rTensor _ φ₂.toLinearMap (homCoactionMap hE θG θM f))
        (φ₁ d • LinearMap.rTensor _ φ₂.toLinearMap (θG.coaction g)) = _
      rw [LinearEquiv.map_smul, LinearMap.smul_apply, LinearMap.map_smul,
        homCoactionMap_eval_specialize, homTensorEquiv_tmul_apply]
      change φ₁ c • φ₁ d • LinearMap.rTensor _ φ₂.toLinearMap (θM.coaction (f g)) =
        φ₁ (c * d) • LinearMap.rTensor _ φ₂.toLinearMap (θM.coaction (f g))
      rw [map_mul, mul_smul]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

lemma homCoactionMap_coassoc (φ₁ : C →+* S) (φ₂ φ₃ : C →ₐ[B] S)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* S).comp t)
    (h₃ : (φ₃ : C →+* S).comp t = φ₁.comp t) (f : G →ₗ[B] M) :
    LinearMap.rTensor _ φ₃.toLinearMap (homCoactionMap hE θG θM f) =
      coactionCompose t _ (homCoactionMap hE θG θM)
        (homCoactionMap_smul hE θG θM) φ₁ φ₂ h (homCoactionMap hE θG θM f) := by
  apply (homTensorEquiv (B := B) (S := S) (G := G) (M := M)).injective
  apply linearMap_ext_coaction hE θG φ₃
  intro g
  rw [homCoactionMap_eval_specialize, θG.coassoc S φ₁ φ₂ φ₃ h h₃,
    homCoactionMap_compose_eval, homCoactionMap_eval,
    θM.coassoc S φ₁ φ₂ φ₃ h h₃]

end HomLaws

section Hom

variable [Module.FinitePresentation B G]

/-- Hom from a finitely presented coaction, with its conjugation coaction. -/
noncomputable def hom (hE : RingEtaleEquivalenceRelation t)
    (θG : GroupoidCoaction t G) (θM : GroupoidCoaction t M) :
    GroupoidCoaction t (G →ₗ[B] M) := by
  letI : Module.Flat B C := (RingHom.flat_algebraMap_iff).mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  refine ofUniversal hE (homCoactionMap hE θG θM) (homCoactionMap_smul hE θG θM) ?_ ?_
  · exact homCoactionMap_counit hE θG θM hE.identity hE.identity_comp_t
  · let := hE.composable_flat
    exact homCoactionMap_coassoc hE θG θM
      (RingEtaleEquivalenceRelation.composableFirst t)
      (RingEtaleEquivalenceRelation.composableSecond t) hE.composableComposite
      (RingEtaleEquivalenceRelation.composable_compat t) hE.composableComposite_comp_t

lemma hom_coaction [Module.Flat B C] (hE : RingEtaleEquivalenceRelation t)
    (θG : GroupoidCoaction t G) (θM : GroupoidCoaction t M) (f : G →ₗ[B] M) :
    (hom hE θG θM).coaction f = homCoactionMap hE θG θM f := rfl

lemma mem_hom_invariants_iff (hE : RingEtaleEquivalenceRelation t)
    (θG : GroupoidCoaction t G) (θM : GroupoidCoaction t M) (f : G →ₗ[B] M) :
    f ∈ (hom hE θG θM).invariants ↔ θG.IsHom θM f := by
  let : Module.Flat B C := (RingHom.flat_algebraMap_iff).mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  change homCoactionMap hE θG θM f = (1 : C) ⊗ₜ f ↔ θG.IsHom θM f
  constructor
  · intro hf g
    have hh := congrArg
      (fun x => homTensorEquiv (B := B) (S := C) (G := G) (M := M) x (θG.coaction g)) hf
    rw [homCoactionMap_eval] at hh
    simpa [homTensorEquiv, LinearMap.baseChange_eq_ltensor] using hh
  · intro hf
    apply (homTensorEquiv (B := B) (S := C) (G := G) (M := M)).injective
    apply linearMap_ext_coaction hE θG (AlgHom.id B C)
    intro g
    simp only [show (AlgHom.id B C).toLinearMap = (LinearMap.id : C →ₗ[B] C) from rfl,
      LinearMap.rTensor_id_apply]
    rw [homCoactionMap_eval]
    simpa [homTensorEquiv, LinearMap.baseChange_eq_ltensor] using hf g

lemma homTensorEquiv_eval_one [Module.Flat B C] (g : G)
    (x : C ⊗[B] (G →ₗ[B] M)) :
    homTensorEquiv (B := B) (S := C) (G := G) (M := M) x ((1 : C) ⊗ₜ g) =
      LinearMap.lTensor C (LinearMap.applyₗ (R := B) (M₂ := M) g) x := by
  induction x with
  | tmul c f => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- Evaluation at an invariant element is equivariant. -/
lemma hom_eval_isHom (hE : RingEtaleEquivalenceRelation t)
    (θG : GroupoidCoaction t G) (θM : GroupoidCoaction t M)
    (g : G) (hg : g ∈ θG.invariants) :
    (hom hE θG θM).IsHom θM (LinearMap.applyₗ (R := B) (M₂ := M) g) := by
  let : Module.Flat B C := (RingHom.flat_algebraMap_iff).mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  intro f
  change θM.coaction (f g) = LinearMap.lTensor C (LinearMap.applyₗ (R := B) (M₂ := M) g)
    (homCoactionMap hE θG θM f)
  rw [← homTensorEquiv_eval_one, ← show θG.coaction g = (1 : C) ⊗ₜ g from hg]
  exact (homCoactionMap_eval hE θG θM f g).symm

end Hom

end GroupoidCoaction

end Langlands.AlgebraicGeometry
