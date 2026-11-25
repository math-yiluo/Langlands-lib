/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.Residue.ResidueStalkHomologyMapComparison
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Nonzero residue coefficient detected by derived homology

## References

* Stacks Project, Tag 0E62, residue-field argument, with Tag 0BCD
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem mono_component_of_mono_homology
    {R : Type u} [Ring R] {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K ⟶ L) (hout : K.d 0 1 = 0) (hin : K.d (-1) 0 = 0)
    [Mono (HomologicalComplex.homologyMap f 0)] : Mono (f.f 0) := by
  have := K.isIso_iCycles 0 1 (by simp) hout
  have := K.isIso_homologyπ (-1) 0 (by simp) hin
  have : Mono (HomologicalComplex.cyclesMap f 0 ≫ L.homologyπ 0) := by
    rw [← HomologicalComplex.homologyπ_naturality]
    infer_instance
  have : Mono (HomologicalComplex.cyclesMap f 0) :=
    mono_of_mono (HomologicalComplex.cyclesMap f 0) (L.homologyπ 0)
  have : Mono (K.iCycles 0 ≫ f.f 0) := by
    rw [← HomologicalComplex.cyclesMap_i]
    infer_instance
  rw [show f.f 0 = (asIso (K.iCycles 0)).inv ≫ (K.iCycles 0 ≫ f.f 0) by simp]
  infer_instance

private theorem residue_coefficient_ne_zero_of_mono
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (σ : M ≃ₗ[R] R) (τ : N ≃ₗ[R] R)
    [Mono ((ModuleCat.extendScalars (IsLocalRing.residue R)).map f)] :
    IsLocalRing.residue R (τ (f.hom (σ.symm 1))) ≠ 0 := by
  let k := IsLocalRing.ResidueField R
  let := (IsLocalRing.residue R).toAlgebra
  let F := ModuleCat.extendScalars (IsLocalRing.residue R)
  let g : ModuleCat.of R R ⟶ ModuleCat.of R R :=
    σ.toModuleIso.inv ≫ f ≫ τ.toModuleIso.hom
  have : Mono (F.map g) := by
    dsimp only [g]
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  have hg (r : R) : g.hom r = g.hom 1 • r := by
    simpa only [smul_eq_mul, mul_one, mul_comm] using g.hom.map_smul r (1 : R)
  intro h
  have hc : IsLocalRing.residue R (g.hom 1) = 0 := h
  have hz : F.map g = 0 := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro r
    change (1 : k) ⊗ₜ[R] (g.hom r) = 0
    rw [hg, TensorProduct.tmul_smul]
    change (IsLocalRing.residue R (g.hom 1) * (1 : k)) ⊗ₜ[R] r = 0
    rw [hc, zero_mul, TensorProduct.zero_tmul]
  have : Mono (0 : F.obj (ModuleCat.of R R) ⟶ F.obj (ModuleCat.of R R)) := by
    rw [← hz]
    infer_instance
  have hzero := (CategoryTheory.Limits.IsZero.of_mono_zero
    (F.obj (ModuleCat.of R R)) (F.obj (ModuleCat.of R R)))
  have ht : (1 : k) ⊗ₜ[R] (1 : R) = 0 := by
    have : Subsingleton (TensorProduct R k R) :=
      ModuleCat.isZero_iff_subsingleton.mp hzero
    exact Subsingleton.elim _ _
  have he := congrArg (TensorProduct.rid R k) ht
  simp at he

/-- In linear coordinates on the source and target stalks, the degree-zero
coefficient of a connective perfect chain representative has nonzero residue. -/
theorem residue_ne_zero_rankOne_stalk_coefficient (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ x : S, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory S)
    (a : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit S.ringCatSheaf) ⟶ E) (s : S)
    (U : S.Opens) (hs : s ∈ U)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ)
    (hP : Scheme.IsStrictlyPerfect S U P)
    (hnegative : ∀ i : ℤ, i < 0 → IsZero (P.X i))
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P)
    (ha : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
        ((derivedPullback (S.fromSpecResidueField s)).map a)))
    (c : (SheafOfModules.overFunctor.{u}
        (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
          (SheafOfModules.unit S.ringCatSheaf)) ≅
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
            ((SheafOfModules.overFunctor.{u}
              (moduleRings S.toRingedSpace) U).obj (SheafOfModules.unit S.ringCatSheaf))))
    (α : (CochainComplex.singleFunctor
        (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
          ((SheafOfModules.overFunctor.{u}
            (moduleRings S.toRingedSpace) U).obj (SheafOfModules.unit S.ringCatSheaf)) ⟶ P)
    (hα : DerivedCategory.Q.map α = c.inv ≫
      (SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U).mapDerivedCategory.map a ≫
        e.hom)
    (σ : ((RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨s, hs⟩).obj
      ((Scheme.Modules.overEquiv U).functor.obj
        (((CochainComplex.singleFunctor
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
            ((SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U).obj
              (SheafOfModules.unit S.ringCatSheaf))).X 0))) ≃ₗ[
                U.toScheme.presheaf.stalk ⟨s, hs⟩] U.toScheme.presheaf.stalk ⟨s, hs⟩)
    (τ : ((RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨s, hs⟩).obj
      ((Scheme.Modules.overEquiv U).functor.obj (P.X 0))) ≃ₗ[
        U.toScheme.presheaf.stalk ⟨s, hs⟩] U.toScheme.presheaf.stalk ⟨s, hs⟩) :
    IsLocalRing.residue (U.toScheme.presheaf.stalk ⟨s, hs⟩)
      (τ (((RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨s, hs⟩).map
        ((Scheme.Modules.overEquiv U).functor.map (α.f 0))).hom (σ.symm 1))) ≠ 0 := by
  classical
  -- Only the vanishing differentials of the single source are needed below.
  have _negative := hnegative
  let T := RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace ⟨s, hs⟩
  let V := (Scheme.Modules.overEquiv U).functor
  let R := U.toScheme.presheaf.stalk ⟨s, hs⟩
  let B := ModuleCat.extendScalars (IsLocalRing.residue R)
  have : V.Additive := Functor.additive_of_preserves_binary_products _
  have : T.PreservesZeroMorphisms :=
    RingedSpace.moduleStalkFunctor_preservesZeroMorphisms _ _
  have : B.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  have : (V ⋙ T ⋙ B).PreservesZeroMorphisms :=
    { map_zero := by
        intro M N
        simp only [Functor.comp_map]
        repeat rw [Functor.map_zero] }
  let F := (V ⋙ T ⋙ B).mapHomologicalComplex (ComplexShape.up ℤ)
  have : IsIso (HomologicalComplex.homologyMap (F.map α) 0) :=
    isIso_residue_stalk_homologyMap S E a s U hs P hP e ha c α hα
  let A := (CochainComplex.singleFunctor
    (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) 0).obj
      ((SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U).obj
        (SheafOfModules.unit S.ringCatSheaf))
  have hout : (F.obj A).d 0 1 = 0 := by
    change (V ⋙ T ⋙ B).map _ = 0
    simp only [A, CochainComplex.singleFunctor_obj_d,
      Functor.map_zero]
  have hin : (F.obj A).d (-1) 0 = 0 := by
    change (V ⋙ T ⋙ B).map _ = 0
    simp only [A, CochainComplex.singleFunctor_obj_d,
      Functor.map_zero]
  have hmono := mono_component_of_mono_homology (F.map α) hout hin
  have : Mono (B.map (T.map (V.map (α.f 0)))) := hmono
  exact residue_coefficient_ne_zero_of_mono (T.map (V.map (α.f 0))) σ τ

end AlgebraicGeometry
