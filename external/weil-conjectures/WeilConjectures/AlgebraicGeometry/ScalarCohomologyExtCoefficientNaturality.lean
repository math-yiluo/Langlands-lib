/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import Mathlib.Algebra.Homology.ConcreteCategory

/-! # ScalarCohomologyExtCoefficientNaturality

Source: Stacks Project, Cohomology, Tags 01F7, 01FD, 07MB and 0FKV.
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

attribute [local instance] Sheaf.monoidalCategory HasExt.standard

private instance : EnoughInjectives (SheafOfModules.{w} X.ringCatSheaf) :=
  (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
private instance : HasExt.{w} (SheafOfModules.{w} X.ringCatSheaf) :=
  hasExt_of_enoughInjectives.{w, w, w + 1} (SheafOfModules.{w} X.ringCatSheaf)

open Opposite in
private theorem moduleExtEquiv_map_aux
    {F G : SheafOfModules.{w} X.ringCatSheaf} (φ : F ⟶ G) (n : ℕ)
    (a : (RingedSpace.moduleCohomology X.toRingedSpace n).obj F) :
    moduleExtEquiv G n ((RingedSpace.moduleCohomology X.toRingedSpace n).map φ a) =
      (moduleExtEquiv F n a).comp.{w} (Abelian.Ext.mk₀.{w} φ) (add_zero n) := by
  let I := injectiveResolution F
  let J := injectiveResolution G
  let ψ : I.Hom J φ := ⟨InjectiveResolution.desc φ J I, by simp⟩
  let K := RingedSpace.globalSectionsComplex I
  let L := RingedSpace.globalSectionsComplex J
  let Γ := RingedSpace.globalSectionsFunctor X.toRingedSpace
  have : Γ.Additive := RingedSpace.globalSectionsFunctor_additive _
  let χ : K ⟶ L := (Γ.mapHomologicalComplex (.up ℕ)).map ψ.hom
  obtain ⟨s, hs, he⟩ := I.extMk_surjective (moduleExtEquiv F n a) (n + 1) rfl
  let x := s.val.app (op ⊤) (1 : Γ(X, ⊤))
  have hx : K.d n (n + 1) x = 0 := by
    have h := congrArg (fun t ↦ t.val.app (op ⊤) (1 : Γ(X, ⊤))) hs
    exact h
  let c : K.cycles n := K.cyclesMk x (n + 1) (by simp) hx
  have hc : K.iCycles n c = x := K.i_cyclesMk x (n + 1) (by simp) hx
  have hI : moduleExtEquiv F n
      ((I.isoRightDerivedObj Γ n).inv (K.homologyπ n c)) = I.extMk s (n + 1) rfl hs := by
    unfold moduleExtEquiv
    exact Classical.choose_spec (exists_moduleExtEquiv F n) I c s hs hc.symm
  have ha : (I.isoRightDerivedObj Γ n).inv (K.homologyπ n c) = a :=
    (moduleExtEquiv F n).injective (hI.trans he)
  let c' : L.cycles n := HomologicalComplex.cyclesMap χ n c
  have hc' : (s ≫ ψ.hom.f n).val.app (op ⊤) (1 : Γ(X, ⊤)) = L.iCycles n c' := by
    have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i χ n) c
    simp only [ConcreteCategory.comp_apply, hc] at h
    exact h.symm
  have hJ : moduleExtEquiv G n
      ((J.isoRightDerivedObj Γ n).inv (L.homologyπ n c')) =
      J.extMk (s ≫ ψ.hom.f n) (n + 1) rfl (by simp [reassoc_of% hs]) := by
    unfold moduleExtEquiv
    exact Classical.choose_spec (exists_moduleExtEquiv G n) J c'
      (s ≫ ψ.hom.f n) (by simp [reassoc_of% hs]) hc'
  have hn := ConcreteCategory.congr_hom
    (InjectiveResolution.isoRightDerivedObj_inv_naturality φ I J ψ.hom
      (by simp [ψ]) Γ n) (K.homologyπ n c)
  have hp := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality χ n) c
  simp only [ConcreteCategory.comp_apply] at hn hp
  change ((RingedSpace.moduleCohomology X.toRingedSpace n).map φ)
    ((I.isoRightDerivedObj Γ n).inv (K.homologyπ n c)) =
    (J.isoRightDerivedObj Γ n).inv
      (HomologicalComplex.homologyMap χ n (K.homologyπ n c)) at hn
  rw [ha, hp] at hn
  rw [hn, hJ, ← InjectiveResolution.extMk_comp_mk₀ s (n + 1) rfl hs ψ, he]

/-- The recorded cohomology-to-Ext comparison respects coefficient maps.
Source: Stacks Project, Cohomology, Tags 01DZ and 01F7.
(blueprint: lem-sc-scalar-cohomology-ext-coefficient-naturality).

Proof: Lift a coefficient morphism to a comparison map of injective resolutions.
The right-derived-functor coefficient map is induced by the global-sections map
of this comparison. Evaluation at 1 identifies the global-sections complex with
Hom from the structure sheaf, naturally in the resolution: every O-linear
comparison map takes the image of 1 to the image of the corresponding section.
The cocycle formula specifying moduleExtEquiv therefore intertwines the derived
coefficient map with postcomposition by the degree-zero Ext class of the
coefficient morphism. Every cohomology class has a cocycle representative, so
this proves naturality of moduleExtEquiv. Exact restriction to scalar sheaves
preserves Yoneda composition and sends the degree-zero coefficient map to
scalarHom. Precompose by scalarUnitMorphism and use associativity of Yoneda
composition. This gives naturality of scalarCohomologyExtMap, hence of its
AddEquiv.ofBijective wrapper scalarCohomologyExtEquiv. This argument applies
also in degree zero and for zero coefficients or the empty scheme.
-/
theorem scalarCohomologyExtEquiv_map
    (f : X ⟶ Spec (CommRingCat.of k)) {F G : X.Modules}
    (φ : F ⟶ G) (n : ℕ) (a : scalarCohomology f F n) :
    scalarCohomologyExtEquiv f G n (scalarCohomologyMap f φ n a) =
      (scalarCohomologyExtEquiv f F n a).comp
        (Abelian.Ext.mk₀ (scalarHom f φ)) (add_zero n) := by
  unfold scalarCohomologyExtEquiv
  change scalarCohomologyExtMap f G n (scalarCohomologyMap f φ n a) =
    (scalarCohomologyExtMap f F n a).comp
      (Abelian.Ext.mk₀ (scalarHom f φ)) (add_zero n)
  unfold scalarCohomologyExtMap scalarExtMap
  change (Abelian.Ext.mk₀ (scalarUnitMorphism f)).comp
    ((moduleExtEquiv G n
      ((RingedSpace.moduleCohomology X.toRingedSpace n).map φ a)).mapExactFunctor
        (scalarFunctor f)) (zero_add n) = _
  rw [moduleExtEquiv_map_aux φ n a, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀]
  exact (Abelian.Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by simp)).symm

end
end AlgebraicGeometry.Scheme.Modules
