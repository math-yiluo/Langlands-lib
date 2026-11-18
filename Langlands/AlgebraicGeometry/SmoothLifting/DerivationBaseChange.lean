import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor

/-! # Derivations into an extended ideal under flat base change

Let `A → P → C` be ring maps with `P` formally smooth and essentially of finite type over `A`, let
`J` be an ideal of `C` and let `T` be a flat `C`-algebra. Then `A`-derivations `P → J T` are the
base change to `T` of `A`-derivations `P → J`.
-/

noncomputable section

universe u

open TensorProduct

namespace Langlands.AlgebraicGeometry.SmoothLifting

variable {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
  [Algebra A P] [Algebra P C] [Algebra A C] [IsScalarTower A P C]

section Hom

variable (A P C) (M : Type u) [AddCommGroup M] [Module C M] [Module P M] [Module A M]
  [IsScalarTower P C M] [IsScalarTower A P M] [IsScalarTower A C M]

/-- The universal property of differentials, as a `C`-linear equivalence. -/
def kaehlerEquivC : Derivation A P M ≃ₗ[C] (Ω[P⁄A] →ₗ[P] M) where
  toFun d := (KaehlerDifferential.linearMapEquivDerivation A P).symm d
  invFun f := KaehlerDifferential.linearMapEquivDerivation A P f
  left_inv d := (KaehlerDifferential.linearMapEquivDerivation A P).apply_symm_apply d
  right_inv f := (KaehlerDifferential.linearMapEquivDerivation A P).symm_apply_apply f
  map_add' d d' := map_add _ d d'
  map_smul' c d := by
    apply (KaehlerDifferential.linearMapEquivDerivation A P).injective
    rw [LinearEquiv.apply_symm_apply]
    ext p
    simp only [Derivation.smul_apply, RingHom.id_apply,
      KaehlerDifferential.linearMapEquivDerivation_apply_apply, LinearMap.smul_apply]
    congr 1
    exact (Derivation.liftKaehlerDifferential_comp_D d p).symm

/-- Derivations into a `C`-module are `C`-linear maps from the base-changed differentials
`C ⊗[P] Ω[P⁄A]`. -/
def derivationEquivHom : Derivation A P M ≃ₗ[C] (C ⊗[P] Ω[P⁄A] →ₗ[C] M) :=
  (kaehlerEquivC A P C M).trans (LinearMap.liftBaseChangeEquiv C)

omit [IsScalarTower A P C] in
theorem derivationEquivHom_one_tmul (d : Derivation A P M) (p : P) :
    derivationEquivHom A P C M d (1 ⊗ₜ KaehlerDifferential.D A P p) = d p := by
  change LinearMap.liftBaseChange C _ (1 ⊗ₜ _) = d p
  rw [LinearMap.liftBaseChange_tmul, one_smul]
  exact Derivation.liftKaehlerDifferential_comp_D d p

omit [IsScalarTower A P C] in
theorem derivationEquivHom_symm_apply (h : C ⊗[P] Ω[P⁄A] →ₗ[C] M) (p : P) :
    (derivationEquivHom A P C M).symm h p = h (1 ⊗ₜ KaehlerDifferential.D A P p) := rfl

end Hom

section BaseChange

variable {T : Type u} [CommRing T] [Algebra C T] [Algebra P T] [IsScalarTower P C T]
  (J : Ideal C) (J' : Ideal T) (hJ : J.map (algebraMap C T) = J')

variable (P) in
/-- Extension of ideal elements from `J` to `J T`, as a `P`-linear map. -/
def idealMapP : J →ₗ[P] J' where
  toFun j := ⟨algebraMap C T j, by rw [← hJ]; exact Ideal.mem_map_of_mem _ j.2⟩
  map_add' j j' := Subtype.ext (map_add (algebraMap C T) _ _)
  map_smul' p j := by
    apply Subtype.ext
    change algebraMap C T (p • (j : C)) = p • algebraMap C T j
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply P C T]

omit [IsScalarTower A P C] in
@[simp] theorem idealMapP_val (j : J) : (idealMapP P J J' hJ j : T) = algebraMap C T j := rfl

variable [Algebra A T] [IsScalarTower A P T] [IsScalarTower A C T]

variable (A P) in
/-- Extension of the values of a derivation from `J` to `J T`. -/
def derMap : Derivation A P J →ₗ[C] Derivation A P J' where
  toFun d := (idealMapP P J J' hJ).compDer d
  map_add' d d' := map_add _ d d'
  map_smul' c d := by
    ext p
    change algebraMap C T (c • (d p : C)) = c • (algebraMap C T (d p))
    rw [smul_eq_mul, Algebra.smul_def, map_mul]

@[simp] theorem derMap_apply_val (d : Derivation A P J) (p : P) :
    (derMap A P J J' hJ d p : T) = algebraMap C T (d p) := rfl

/-- **Flat base change of derivations into an ideal.** -/
theorem isBaseChange_derMap [Module.Flat C T] [Algebra.FormallySmooth A P]
    [Algebra.EssFiniteType A P] : IsBaseChange T (derMap A P J J' hJ) := by
  let e1 := derivationEquivHom A P C J
  let e4 := derivationEquivHom A P C J'
  have hB := Module.FinitePresentation.isBaseChange_map C (C ⊗[P] Ω[P⁄A]) J T
  let iJ : T ⊗[C] J ≃ₗ[T] J' :=
    (Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor.idealTensorEquiv J).trans
      (LinearEquiv.ofEq _ _ hJ)
  let G : T ⊗[C] Derivation A P J ≃ₗ[T] (C ⊗[P] Ω[P⁄A] →ₗ[C] J') :=
    ((e1.baseChange C T _ _).trans hB.equiv).trans
      ((LinearEquiv.congrRight iJ).trans (LinearMap.liftBaseChangeEquiv T).symm)
  let Φ := LinearMap.liftBaseChange T (derMap A P J J' hJ)
  have hF : ∀ x, Φ x = e4.symm (G x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul t d =>
      ext p
      rw [LinearMap.liftBaseChange_tmul, derivationEquivHom_symm_apply]
      simp only [G, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
        IsBaseChange.equiv_tmul, LinearMap.liftBaseChangeEquiv_symm_apply,
        LinearMap.smul_apply, LinearMap.baseChangeHom_apply, map_smul]
      rw [Derivation.smul_apply, Submodule.coe_smul, Submodule.coe_smul, derMap_apply_val]
      congr 1
      change _ = ((iJ (LinearMap.baseChange T (e1 d)
        (1 ⊗ₜ (1 ⊗ₜ KaehlerDifferential.D A P p)))) : T)
      rw [LinearMap.baseChange_tmul, derivationEquivHom_one_tmul]
      simp [iJ,
        Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor.idealTensorEquiv_tmul]
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  have hbij : Function.Bijective Φ := by
    rw [show ⇑Φ = e4.symm ∘ G from funext hF]
    exact e4.symm.bijective.comp G.bijective
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ hbij) fun d => ?_
  change Φ (1 ⊗ₜ d) = _
  rw [LinearMap.liftBaseChange_tmul, one_smul]

end BaseChange

end Langlands.AlgebraicGeometry.SmoothLifting
