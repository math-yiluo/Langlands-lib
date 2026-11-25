/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-!
# The canonical affine tilde tensor comparison on stalks

## References

* Stacks Project, Schemes, Tag 01I8(1), second proof
* Stacks Project, Schemes, Tag 01I8(1), second proof, with Tags 01HV(7), 00DL and Modules 01CB
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison is bijective on each stalk. -/
theorem affine_tilde_tensor_stalk_bijective (R : CommRingCat.{u})
    (M N : ModuleCat.{u} R)
    (α : tilde (ModuleCat.of R (M ⊗[R] N)) ⟶ tilde M ⊗ tilde N)
    (hα : ∀ (m : M) (n : N),
      α.val.app (op ⊤) (tilde.toOpen (ModuleCat.of R (M ⊗[R] N)) ⊤ (m ⊗ₜ[R] n)) =
        Scheme.Modules.tmulSection (tilde.toOpen M ⊤ m) (tilde.toOpen N ⊤ n))
    (x : Spec R) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      α.mapPresheaf) := by
  classical
  let A := (Spec R).presheaf.stalk x
  let S := x.asIdeal.primeCompl
  let Q := ModuleCat.of R (M ⊗[R] N)
  let LM := (tilde M).presheaf.stalk x
  let LN := (tilde N).presheaf.stalk x
  let LQ := (tilde Q).presheaf.stalk x
  let f := (tilde.toStalk M x).hom
  let g := (tilde.toStalk N x).hom
  let q := (tilde.toStalk Q x).hom
  let : IsLocalizedModule S q :=
    tilde.instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk
      Q x
  let : Algebra R A :=
    inferInstanceAs (Algebra R ((Spec.structureSheaf R).presheaf.stalk x))
  let : IsLocalization S A :=
    inferInstanceAs (IsLocalization.AtPrime ((Spec.structureSheaf R).presheaf.stalk x) x.asIdeal)
  let : IsScalarTower R A LM := .of_algebraMap_smul fun _ _ ↦ rfl
  let : IsScalarTower R A LN := .of_algebraMap_smul fun _ _ ↦ rfl
  let t := (IsLocalization.moduleTensorEquiv S A LM LN).symm.restrictScalars R
  let v := t.toLinearMap ∘ₗ TensorProduct.map f g
  have hv : IsLocalizedModule S v := inferInstance
  obtain ⟨Φ, hΦ, _⟩ := SheafOfModules.stalkTensorIso (Spec R).toRingedSpace x
  let ψ : (tilde M ⊗ tilde N).presheaf.stalk x ≃ₗ[A] LM ⊗[A] LN :=
    (Φ (tilde M) (tilde N)).toLinearEquiv
  let h := ψ.toLinearMap ∘ₗ α.stalkLinearMap x
  let : IsScalarTower R A LQ := .of_algebraMap_smul fun _ _ ↦ rfl
  let hR := h.restrictScalars R
  have hcomm : hR ∘ₗ q = v := by
    ext m n
    change ψ (α.stalkLinearMap x (q (m ⊗ₜ[R] n))) = v (m ⊗ₜ[R] n)
    change ψ (α.stalkLinearMap x ((tilde Q).presheaf.germ ⊤ x (by simp)
      (tilde.toOpen Q ⊤ (m ⊗ₜ[R] n)))) = _
    rw [Scheme.Modules.Hom.stalkLinearMap_germ]
    change ψ ((tilde M ⊗ tilde N).presheaf.germ ⊤ x (by simp)
      (α.val.app (op ⊤) (tilde.toOpen Q ⊤ (m ⊗ₜ[R] n)))) = _
    rw [hα m n]
    exact hΦ (tilde M) (tilde N) ⊤ (by simp) (tilde.toOpen M ⊤ m) (tilde.toOpen N ⊤ n)
  have : IsLocalizedModule S (hR ∘ₗ q) := hcomm ▸ hv
  have hh : Function.Bijective hR := by
    rw [← IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp S q hR]
    exact (IsLocalizedModule.linearEquiv S q (hR ∘ₗ q)).bijective
  exact (Function.Bijective.of_comp_iff' ψ.bijective (α.stalkLinearMap x)).mp hh

end AlgebraicGeometry
