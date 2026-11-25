/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Single-module transposes for the pinned derived adjunction

Source: Stacks Project, Tags 079W and 0FP1.
(blueprint: lem-pc-canonical-single-adjunction-transpose).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section

private theorem single_complex_transpose
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D] {L : C ⥤ D} {R : D ⥤ C}
    [L.Additive] [R.Additive] (adj : L ⊣ R) (N : C) (M : D) (b : L.obj N ⟶ M) :
    (adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv _ _
      ((HomologicalComplex.singleMapHomologicalComplex L (ComplexShape.up ℤ) 0).hom.app N ≫
        (CochainComplex.singleFunctor D 0).map b) =
      (CochainComplex.singleFunctor C 0).map (adj.homEquiv _ _ b) ≫
        (HomologicalComplex.singleMapHomologicalComplex R (ComplexShape.up ℤ) 0).inv.app M := by
  rw [Adjunction.homEquiv_apply]
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i = 0
  · subst i
    simp [Adjunction.homEquiv_apply, CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self,
      Category.assoc]
  · apply (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N i hi).eq_of_src

private theorem single_homotopy_transpose
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D]
    [(HomotopyCategory.quotient C (ComplexShape.up ℤ)).IsLocalization
      (HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ))]
    [(HomotopyCategory.quotient D (ComplexShape.up ℤ)).IsLocalization
      (HomologicalComplex.homotopyEquivalences D (ComplexShape.up ℤ))]
    {L : C ⥤ D} {R : D ⥤ C}
    [L.Additive] [R.Additive] (adj : L ⊣ R) (N : C) (M : D) (b : L.obj N ⟶ M) :
    (adj.mapHomotopyCategory (ComplexShape.up ℤ)).homEquiv _ _
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex L (ComplexShape.up ℤ) 0).hom.app N ≫
          (CochainComplex.singleFunctor D 0).map b)) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((CochainComplex.singleFunctor C 0).map (adj.homEquiv _ _ b) ≫
          (HomologicalComplex.singleMapHomologicalComplex R (ComplexShape.up ℤ) 0).inv.app M) := by
  rw [Adjunction.homEquiv_apply]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  change (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map _ ≫
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map _ = _
  rw [← Functor.map_comp]
  exact congrArg ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map)
    (single_complex_transpose adj N M b)

namespace AlgebraicGeometry.Scheme.Modules

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The pinned derived adjunction transposes the ordinary single-module comparison.
Source: Stacks Project, Tags 079W and 0FP1; the factorization defining
`exists_schemeDerivedAdjunction`.
(blueprint: lem-pc-canonical-single-adjunction-transpose).

Proof: Let ε be the selected left-derived counit and t the unique isomorphism
from tensor pullback to ordinary pullback preserving their common right adjoint.
Represent a by the homotopy-category single map after the single-map comparison
for tensor pullback and t. Apply the factorization in
`Classical.choose_spec (exists_schemeDerivedAdjunction ...)` to this morphism.
Naturality of the single-map comparison identifies its underived transpose with
the single map of the tensor adjunction transpose. The unit law for
`leftAdjointUniq` identifies this transpose with the ordinary adjunction transpose.
The inverse single-map comparison for direct image followed by the specified
right-derived unit is exactly `canonicalSingleDirectImageMap`. Reassociate the
result to obtain the equality. No invertibility of a pullback comparison is used;
zero modules and empty schemes satisfy the same naturality and counit identities. -/
theorem canonicalSingleAdjunctionTranspose {X S : Scheme.{u}} (f : X ⟶ S)
    (N : S.Modules) (M : X.Modules) (a : (pullback f).obj N ⟶ M) :
    (Classical.choose (exists_schemeDerivedAdjunction f
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f))).homEquiv _ _
      (canonicalSinglePullbackMap f N ≫ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map a) =
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
        ((pullbackPushforwardAdjunction f).homEquiv _ _ a) ≫
      canonicalSingleDirectImageMap f M := by
  let := canonicalTensorPullbackAdditive f
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f
  let hε := (Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition))) f
  let adj := Classical.choose (exists_tensorPullbackAdjunction f)
  let t := adj.leftAdjointUniq (pullbackPushforwardAdjunction f)
  let b := t.hom.app N ≫ a
  have hb : adj.homEquiv _ _ b = (pullbackPushforwardAdjunction f).homEquiv _ _ a := by
    dsimp only [b, t]
    rw [adj.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
      Adjunction.homEquiv_apply]
  let k := (HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorPullback f) (ComplexShape.up ℤ) 0).hom.app N ≫
          (CochainComplex.singleFunctor _ 0).map b)
  have hk : (adj.mapHomotopyCategory (ComplexShape.up ℤ)).homEquiv
      ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj N)
      ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M) k =
      (HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (ComplexShape.up ℤ)).map
          ((CochainComplex.singleFunctor _ 0).map
              ((pullbackPushforwardAdjunction f).homEquiv _ _ a) ≫
            (HomologicalComplex.singleMapHomologicalComplex
              (pushforward f) (ComplexShape.up ℤ) 0).inv.app M) :=
    (single_homotopy_transpose adj N M b).trans
      (congrArg (fun c : N ⟶ (pushforward f).obj M ↦
        (HomotopyCategory.quotient
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (ComplexShape.up ℤ)).map
            ((CochainComplex.singleFunctor _ 0).map c ≫
              (HomologicalComplex.singleMapHomologicalComplex
                (pushforward f) (ComplexShape.up ℤ) 0).inv.app M)) hb)
  have h := Classical.choose_spec (exists_schemeDerivedAdjunction f ε hε)
    ((HomotopyCategory.singleFunctor _ 0).obj N)
    ((HomotopyCategory.singleFunctor _ 0).obj M) k
  have h' := h.trans (congrArg (fun z => DerivedCategory.Qh.map z ≫
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app
      ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M)) hk)
  simp only [canonicalSinglePullbackMap, canonicalSingleDirectImageMap, cast_eq, k, b, ε, t, adj,
    DerivedCategory.singleFunctor, DerivedCategory.singleFunctors,
    HomotopyCategory.singleFunctor, HomotopyCategory.singleFunctors,
    SingleFunctors.postcomp, Functor.comp_map, Functor.comp_obj,
    Functor.map_comp, Category.assoc] at h' ⊢
  convert h' using 1 <;> rfl

end AlgebraicGeometry.Scheme.Modules
