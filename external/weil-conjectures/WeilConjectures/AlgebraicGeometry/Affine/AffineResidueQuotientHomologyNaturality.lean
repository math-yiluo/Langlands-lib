/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.GroupTheory.QuotientGroup.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris

/-! # The natural quotient-to-homology comparison for affine residue complexes

Source: Stacks Project, Tag 010V; Mathlib's concrete module homology API.
(blueprint: new-affine-residue-quotient-homology-naturality)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

noncomputable section

variable (W : Scheme.{v}) (U : W.Opens) (p : Ideal Γ(W, U)) [p.IsPrime]

private abbrev sectionsFunctor :
    SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) :=
  SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))

private instance sectionsFunctor_additive : (sectionsFunctor W U).Additive :=
  inferInstanceAs ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)

private abbrev residueFunctor :=
  ModuleCat.extendScalars.{v, v, v} (algebraMap Γ(W, U) p.ResidueField)

private instance residueFunctor_additive : (residueFunctor W U p).Additive :=
  (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive

private abbrev residueComplexFunctor :=
  ((sectionsFunctor W U ⋙ residueFunctor W U p).mapHomologicalComplex (.up ℤ))

private def termIso
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) (j : ℤ) :
    affineResidueTerm W U p K j ≃+ ((residueComplexFunctor W U p).obj K).X j :=
  let a : p.ResidueField ≃ₗ[Γ(W, U)]
      (ModuleCat.restrictScalars (algebraMap Γ(W, U) p.ResidueField)).obj
        (ModuleCat.of p.ResidueField p.ResidueField) :=
    { AddEquiv.refl p.ResidueField with map_smul' := fun r x ↦ Algebra.smul_def r x }
  (TensorProduct.congr a
    (LinearEquiv.refl Γ(W, U) ((sectionsFunctor W U).obj (K.X j)))).toAddEquiv

private theorem termIso_d
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (i j : ℤ) (x : affineResidueTerm W U p K i) :
    termIso W U p K j (affineResidueDifferential W U p K i j x) =
      ((residueComplexFunctor W U p).obj K).d i j (termIso W U p K i x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem termIso_map
    {K C : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ}
    (φ : K ⟶ C) (j : ℤ) (x : affineResidueTerm W U p K j) :
    termIso W U p C j (affineResidueComponent φ j x) =
      ((residueComplexFunctor W U p).map φ).f j (termIso W U p K j x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private def cycleIso
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :
    affineResidueCycles W U p K ≃+
      LinearMap.ker (((residueComplexFunctor W U p).obj K).sc' 0 1 2).g.hom where
  toFun x := ⟨termIso W U p K 1 x.val, by
    change ((residueComplexFunctor W U p).obj K).d 1 2 (termIso W U p K 1 x.val) = 0
    rw [← termIso_d, x.property, map_zero]⟩
  invFun x := ⟨(termIso W U p K 1).symm x.val, by
    apply (termIso W U p K 2).injective
    rw [termIso_d, (termIso W U p K 1).apply_symm_apply, map_zero]
    exact x.property⟩
  left_inv x := Subtype.ext ((termIso W U p K 1).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((termIso W U p K 1).apply_symm_apply x.val)
  map_add' x y := Subtype.ext ((termIso W U p K 1).map_add x.val y.val)

private theorem boundaries_map
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :
    (affineResidueBoundaries W U p K).map (cycleIso W U p K).toAddMonoidHom =
      (((residueComplexFunctor W U p).obj K).sc' 0 1 2).moduleCatToCycles.range.toAddSubgroup := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz⟩ := hy
    refine ⟨termIso W U p K 0 z, ?_⟩
    apply Subtype.ext
    change ((residueComplexFunctor W U p).obj K).d 0 1 (termIso W U p K 0 z) =
      termIso W U p K 1 y.val
    rw [← termIso_d, hz]
    rfl
  · rintro ⟨y, hy⟩
    refine ⟨(cycleIso W U p K).symm x, ?_, (cycleIso W U p K).apply_symm_apply x⟩
    refine ⟨(termIso W U p K 0).symm y, ?_⟩
    change affineResidueDifferential W U p K 0 1 ((termIso W U p K 0).symm y) =
      (termIso W U p K 1).symm x.val
    apply (termIso W U p K 1).injective
    rw [termIso_d, (termIso W U p K 1).apply_symm_apply,
      (termIso W U p K 0).apply_symm_apply]
    exact congrArg Subtype.val hy

-- Comparing the quotient and categorical homology instances expands the tensor carriers.
private def quotientIso
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :
    affineResidueCycleHomology W U p K ≃+
      ((residueComplexFunctor W U p).obj K).homology 1 :=
  let C := (residueComplexFunctor W U p).obj K
  let S := C.sc' 0 1 2
  let q := QuotientAddGroup.congr (affineResidueBoundaries W U p K)
    S.moduleCatToCycles.range.toAddSubgroup (cycleIso W U p K) (boundaries_map W U p K)
  q.trans ((S.moduleCatHomologyIso.symm ≪≫
    (C.homologyIsoSc' 0 1 2 (by simp) (by simp)).symm).toLinearEquiv.toAddEquiv)

private theorem quotientIso_class
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (x : affineResidueCycles W U p K) :
    quotientIso W U p K (affineResidueCycleClass W U p K x) =
      (((residueComplexFunctor W U p).obj K).homologyIsoSc'
        0 1 2 (by simp) (by simp)).inv
          ((((residueComplexFunctor W U p).obj K).sc' 0 1 2).homologyπ
            ((((residueComplexFunctor W U p).obj K).sc' 0 1 2).moduleCatCyclesIso.inv
              (cycleIso W U p K x))) := by
  let C := (residueComplexFunctor W U p).obj K
  let S := C.sc' 0 1 2
  change (C.homologyIsoSc' 0 1 2 (by simp) (by simp)).inv
      (S.moduleCatHomologyIso.inv
        ((QuotientAddGroup.mk' S.moduleCatToCycles.range.toAddSubgroup)
          (cycleIso W U p K x))) = _
  apply congrArg ((C.homologyIsoSc' 0 1 2 (by simp) (by simp)).inv)
  symm
  exact ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_π (cycleIso W U p K x)

private def abstractCycle
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (x : affineResidueCycles W U p K) : ((residueComplexFunctor W U p).obj K).cycles 1 :=
  (((residueComplexFunctor W U p).obj K).cyclesIsoSc'
    0 1 2 (by simp) (by simp)).inv
      ((((residueComplexFunctor W U p).obj K).sc' 0 1 2).moduleCatCyclesIso.inv
        (cycleIso W U p K x))

private theorem abstractCycle_i
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (x : affineResidueCycles W U p K) :
    ((residueComplexFunctor W U p).obj K).iCycles 1 (abstractCycle W U p K x) =
      termIso W U p K 1 x.val := by
  let C := (residueComplexFunctor W U p).obj K
  let S := C.sc' 0 1 2
  have h₁ := ConcreteCategory.congr_hom
    (C.cyclesIsoSc'_inv_iCycles 0 1 2 (by simp) (by simp))
      (S.moduleCatCyclesIso.inv (cycleIso W U p K x))
  have h₂ := ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_iCycles
    (cycleIso W U p K x)
  exact h₁.trans h₂

private theorem quotientIso_class_abstract
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (x : affineResidueCycles W U p K) :
    quotientIso W U p K (affineResidueCycleClass W U p K x) =
      ((residueComplexFunctor W U p).obj K).homologyπ 1 (abstractCycle W U p K x) := by
  rw [quotientIso_class]
  exact ConcreteCategory.congr_hom
    (((residueComplexFunctor W U p).obj K).π_homologyIsoSc'_inv
      0 1 2 (by simp) (by simp))
        ((((residueComplexFunctor W U p).obj K).sc' 0 1 2).moduleCatCyclesIso.inv
          (cycleIso W U p K x))

private theorem abstractCycle_naturality
    {K C : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ}
    (φ : K ⟶ C) (x : affineResidueCycles W U p K) :
    HomologicalComplex.cyclesMap ((residueComplexFunctor W U p).map φ) 1
        (abstractCycle W U p K x) =
      abstractCycle W U p C (affineResidueCycleMap φ x) := by
  apply (ModuleCat.mono_iff_injective
    (((residueComplexFunctor W U p).obj C).iCycles 1)).1 inferInstance
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i ((residueComplexFunctor W U p).map φ) 1)
      (abstractCycle W U p K x)
  calc
    _ = ((residueComplexFunctor W U p).map φ).f 1
        (((residueComplexFunctor W U p).obj K).iCycles 1
          (abstractCycle W U p K x)) := h
    _ = ((residueComplexFunctor W U p).map φ).f 1 (termIso W U p K 1 x.val) :=
      congrArg _ (abstractCycle_i W U p K x)
    _ = termIso W U p C 1 (affineResidueComponent φ 1 x.val) :=
      (termIso_map W U p φ 1 x.val).symm
    _ = _ := (abstractCycle_i W U p C (affineResidueCycleMap φ x)).symm

-- The statement compares tensor-product and quotient module structures.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The explicit residue quotient computes tensor homology naturally in all chain maps.
No perfectness, affinity or derived-category hypothesis is required for this algebraic step.
Source: Stacks Project, Tag 010V; Mathlib's concrete module homology API.
(blueprint: new-affine-residue-quotient-homology-naturality)

Proof: Identify the ordinary residue tensor with scalar extension on each term.
Restrict this natural term comparison to the kernels of the outgoing differentials.
The image of the incoming differential corresponds to the incoming boundary
submodule. Descend the kernel isomorphism to the quotient and use the canonical
module homology isomorphism. Naturality of homology projections and the term
comparison proves the equation first on cycle classes. Surjectivity of the
cycle-class projection proves it on every homology class. -/
theorem affine_residue_quotient_homology_naturality :
    let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
        ModuleCat.{v} Γ(W, U) := SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
    letI : F.Additive := inferInstanceAs
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
    let T := ModuleCat.extendScalars.{v, v, v} (algebraMap Γ(W, U) p.ResidueField)
    letI : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
    let G := (F ⋙ T).mapHomologicalComplex (.up ℤ)
    ∃ e : ∀ K, affineResidueCycleHomology W U p K ≃+ (G.obj K).homology 1,
      ∀ K C (φ : K ⟶ C) z,
        e C (affineResidueCycleHomologyMap φ z) =
          HomologicalComplex.homologyMap (G.map φ) 1 (e K z) := by
  dsimp only
  refine ⟨quotientIso W U p, ?_⟩
  intro K C φ
  -- Work on cycle classes without substituting through the quotient structures.
  refine (affineResidueCycleClass_surjective_kernel W U p K).1.forall.2 ?_
  intro x
  calc
    _ = ((residueComplexFunctor W U p).obj C).homologyπ 1
        (abstractCycle W U p C (affineResidueCycleMap φ x)) :=
      quotientIso_class_abstract W U p C (affineResidueCycleMap φ x)
    _ = ((residueComplexFunctor W U p).obj C).homologyπ 1
        (HomologicalComplex.cyclesMap ((residueComplexFunctor W U p).map φ) 1
          (abstractCycle W U p K x)) :=
      congrArg (((residueComplexFunctor W U p).obj C).homologyπ 1)
        (abstractCycle_naturality W U p φ x).symm
    _ = HomologicalComplex.homologyMap ((residueComplexFunctor W U p).map φ) 1
        (((residueComplexFunctor W U p).obj K).homologyπ 1 (abstractCycle W U p K x)) :=
      (ConcreteCategory.congr_hom
        (HomologicalComplex.homologyπ_naturality ((residueComplexFunctor W U p).map φ) 1)
          (abstractCycle W U p K x)).symm
    _ = _ := congrArg
      (HomologicalComplex.homologyMap ((residueComplexFunctor W U p).map φ) 1)
      (quotientIso_class_abstract W U p K x).symm

end
end AlgebraicGeometry.Scheme
