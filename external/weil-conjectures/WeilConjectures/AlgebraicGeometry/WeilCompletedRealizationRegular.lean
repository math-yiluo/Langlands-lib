/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplete
public import WeilConjectures.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
public import WeilConjectures.CategoryTheory.RingedKoszulSystem

set_option linter.privateModule false

/-! # The regular module under completed constant realization

Source: Stacks Project, Modules on Sites, Tags 03D8 and 03EK,
lemma-adjointness-tensor-restrict, and Tag 0GMW, lemma-sheafification-tensor.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem completedOne_isIso
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : ProEtaleAdicCoefficientDatum A) : IsIso (completedKoszulOne X d) := by
  let M := (adicLisseConstantModules X A).obj (ModuleCat.of A A)
  let α := adicDatumScalar X d
  let adj := adicDatumOrdinaryAdjunction X α
  let e (N : adicDatumModules X d) :
      ((completedKoszulConstant X d).obj (ModuleCat.of A A) ⟶ N) ≃ N.sections :=
    ((adj.homEquiv M N).trans
      (PresheafOfModules.sheafificationHomEquiv (adicLisseConstantUnit X A))).trans
        (PresheafOfModules.unitHomEquiv _)
  have he (N : adicDatumModules X d)
      (f : (completedKoszulConstant X d).obj (ModuleCat.of A A) ⟶ N) :
      e N f = N.unitHomEquiv (completedKoszulOne X d ≫ f) := by
    apply PresheafOfModules.sections_ext
    intro U
    dsimp only [e, Equiv.trans_apply]
    change ((PresheafOfModules.sheafificationHomEquiv (adicLisseConstantUnit X A))
      (adj.homEquiv M N f)).app U (1 : A) =
        f.val.app U ((completedKoszulOne X d).val.app U
          (1 : (adicDatumRing X d).obj.obj U))
    rw [Adjunction.homEquiv_unit]
    change f.val.app U ((adj.unit.app M).val.app U
      (completedConstantGenerator X A (ModuleCat.of A A) U 1)) =
        f.val.app U ((completedKoszulOne X d).val.app U (1 : (adicDatumRing X d).obj.obj U))
    have hu : adj.unit.app M = adicDatumOrdinaryUnit X α M :=
      (adicDatumOrdinaryAdjunction_exists X α).choose_spec M
    rw [hu]
    exact congrArg (f.val.app U)
      (((adicDatumOrdinaryUnit_exists X α M).exists.choose_spec U
        (completedConstantGenerator X A (ModuleCat.of A A) U 1)).trans
          ((completedKoszulOne_exists X d).exists.choose_spec U).symm)
  apply isIso_of_coyoneda_map_bijective
  intro N
  have hf : (fun f ↦ completedKoszulOne X d ≫ f) =
      N.unitHomEquiv.symm ∘ e N := by
    funext f
    exact N.unitHomEquiv.injective (by simp [he])
  rw [hf]
  exact N.unitHomEquiv.symm.bijective.comp (e N).bijective

private theorem completedOne_scalar
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : ProEtaleAdicCoefficientDatum A) (a : A) (U : X.ProEtᵒᵖ) :
    ((completedKoszulConstant X d).map
        (ModuleCat.ofHom (LinearMap.mul A A a))).val.app U
        ((completedKoszulOne X d).val.app U (1 : (adicDatumRing X d).obj.obj U)) =
      (adicDatumScalar X d).hom.app U ((adicLisseConstantUnit X A).app U a) •
        ((completedKoszulOne X d).val.app U (1 : (adicDatumRing X d).obj.obj U)) := by
  let M := (adicLisseConstantModules X A).obj (ModuleCat.of A A)
  let adj := adicDatumOrdinaryAdjunction X (adicDatumScalar X d)
  let η := adj.unit.app M
  have hη (x : M.val.obj U) : η.val.app U x =
      adicDatumTensorSection X (adicDatumScalar X d) M U 1 x := by
    dsimp only [η]
    erw [(adicDatumOrdinaryAdjunction_exists X (adicDatumScalar X d)).choose_spec]
    exact (adicDatumOrdinaryUnit_exists X (adicDatumScalar X d) M).exists.choose_spec U x
  have hc : (completedKoszulOne X d).val.app U (1 : (adicDatumRing X d).obj.obj U) =
      η.val.app U (completedConstantGenerator X A (ModuleCat.of A A) U 1) := by
    rw [hη]
    exact (completedKoszulOne_exists X d).exists.choose_spec U
  rw [hc]
  have hn := congrArg (fun f ↦ f.val.app U
    (completedConstantGenerator X A (ModuleCat.of A A) U 1))
    (adj.unit_naturality ((adicLisseConstantModules X A).map
      (ModuleCat.ofHom (LinearMap.mul A A a))))
  have hmap : ((adicLisseConstantModules X A).map
      (ModuleCat.ofHom (LinearMap.mul A A a))).val.app U
      (completedConstantGenerator X A (ModuleCat.of A A) U 1) =
        completedConstantGenerator X A (ModuleCat.of A A) U a := by
    have hx := congrArg (fun f ↦ f.app U (1 : A))
      (toSheafify_naturality (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).map (AddCommGrpCat.ofHom
          (LinearMap.mul A A a).toAddMonoidHom)))
    change completedConstantGenerator X A (ModuleCat.of A A) U (a * 1) =
      ((adicLisseConstantModules X A).map (ModuleCat.ofHom (LinearMap.mul A A a))).val.app U
        (completedConstantGenerator X A (ModuleCat.of A A) U 1) at hx
    simpa only [mul_one] using hx.symm
  have hg : completedConstantGenerator X A (ModuleCat.of A A) U a =
      (adicLisseConstantUnit X A).app U a •
        completedConstantGenerator X A (ModuleCat.of A A) U 1 := by
    let η₀ := (PresheafOfModules.sheafificationAdjunction
      (adicLisseConstantUnit X A)).unit.app
        (PresheafOfModules.unit ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of A)))
    have h := (η₀.app U).hom.map_smul a (1 : A)
    change completedConstantGenerator X A (ModuleCat.of A A) U (a * 1) =
      (adicLisseConstantUnit X A).app U a •
        completedConstantGenerator X A (ModuleCat.of A A) U 1 at h
    simpa only [mul_one] using h
  change ((completedKoszulConstant X d).map
      (ModuleCat.ofHom (LinearMap.mul A A a))).val.app U
      (η.val.app U (completedConstantGenerator X A (ModuleCat.of A A) U 1)) =
    η.val.app U (((adicLisseConstantModules X A).map
      (ModuleCat.ofHom (LinearMap.mul A A a))).val.app U
        (completedConstantGenerator X A (ModuleCat.of A A) U 1)) at hn
  rw [hmap, hg, map_smul] at hn
  exact hn

end AlgebraicGeometry.Scheme
