/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-!

# Functors preserving flat objects send flat resolutions to K-flat complexes

Let `F : C ⥤ D` be a functor between abelian monoidal categories which sends flat objects
to flat objects (`CategoryTheory.Functor.PreservesFlat`). Applied degreewise, `F` sends a
bounded above complex of flat objects to a bounded above complex of flat objects, which is
K-flat by `CochainComplex.kFlat_of_isStrictlyLE_of_flat`. If `F` also commutes with
colimits indexed by `ℤ`, then `F` sends `ℤ`-indexed colimits of such complexes to K-flat
complexes, by `CochainComplex.closedUnderColimitsOfShape_kFlat`.

The functorial flat resolution `Λ.resolutionFunctor.obj K` of a complex `K` is such a
colimit (`CategoryTheory.Abelian.LeftResolution.colimitOfShapeFlatResolutionFunctorObj`),
so `F` sends it to a K-flat complex. This is what is needed to compute the left derived
functor of `F` together with derived tensor products on flat resolutions, without asking
`F` to preserve all K-flat complexes.

## Main definitions and results

- `CategoryTheory.Functor.PreservesFlat`: `F` sends flat objects to flat objects.
- `CategoryTheory.Functor.preservesFlat_of_isEquivalence`: a monoidal equivalence preserves
  flat objects.
- `CategoryTheory.Functor.kFlat_mapHomologicalComplex_obj_of_colimitsOfShape`: `F` sends
  `ℤ`-indexed colimits of bounded above complexes of flat objects to K-flat complexes.
- `CategoryTheory.Functor.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj`: `F`
  sends functorial flat resolutions to K-flat complexes.

-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]

/-- A functor `F : C ⥤ D` between monoidal categories preserves flat objects if `F.obj X`
is flat (`CategoryTheory.ObjectProperty.flat`) for every flat `X`. -/
class PreservesFlat (F : C ⥤ D) : Prop where
  flat_obj {X : C} (hX : ObjectProperty.flat X) : ObjectProperty.flat (F.obj X)

section

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- A monoidal functor which is an equivalence of categories preserves flat objects: tensoring
with `F(X)` is, up to isomorphism, the composite of `F⁻¹`, tensoring with `X` and `F`. -/
lemma preservesFlat_of_isEquivalence (F : C ⥤ D) [F.Monoidal] [F.IsEquivalence] :
    F.PreservesFlat where
  flat_obj {X} hX := by
    have := hX.tensorLeft.preservesFiniteLimits
    have := hX.tensorLeft.preservesFiniteColimits
    have := hX.tensorRight.preservesFiniteLimits
    have := hX.tensorRight.preservesFiniteColimits
    refine ⟨(exactFunctor _ _).prop_of_iso
      ((Functor.leftUnitor _).symm ≪≫ isoWhiskerRight F.asEquivalence.counitIso.symm _ ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft F.inv (Monoidal.commTensorLeft F X)).symm
      ((exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩),
      (exactFunctor _ _).prop_of_iso
      ((Functor.leftUnitor _).symm ≪≫ isoWhiskerRight F.asEquivalence.counitIso.symm _ ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft F.inv (Monoidal.commTensorRight F X)).symm
      ((exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩)⟩

end

variable [Abelian C] [Abelian D] (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesFlat]

/-- Applied degreewise, a functor preserving flat objects sends bounded above complexes of
flat objects to bounded above complexes of flat objects. -/
lemma cochainComplexMinus_flat_mapHomologicalComplex_obj {K : CochainComplex C ℤ}
    (hK : ObjectProperty.flat.cochainComplexMinus K) :
    ObjectProperty.flat.cochainComplexMinus ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  obtain ⟨hK, n, hn⟩ := hK
  exact ⟨fun i ↦ PreservesFlat.flat_obj (hK i),
    n, (CochainComplex.isStrictlyLE_iff _ n).2
      fun i hi ↦ F.map_isZero (CochainComplex.isZero_of_isStrictlyLE K n i hi)⟩

variable [MonoidalPreadditive D]
  [∀ (j : ℤ), HasColimitsOfShape
    (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j})) D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]

/-- A functor preserving flat objects and colimits indexed by `ℤ` sends `ℤ`-indexed
colimits of bounded above complexes of flat objects to K-flat complexes. -/
lemma kFlat_mapHomologicalComplex_obj_of_colimitsOfShape
    [HasColimitsOfShape ℤ C] [PreservesColimitsOfShape ℤ F] {K : CochainComplex C ℤ}
    (hK : ObjectProperty.flat.cochainComplexMinus.colimitsOfShape ℤ K) :
    (HomologicalComplex.quasiIso D (.up ℤ)).kFlat ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  obtain ⟨p⟩ := hK
  exact ObjectProperty.prop_of_isColimit _
    (isColimitOfPreserves (F.mapHomologicalComplex (.up ℤ)) p.isColimit)
    (fun j ↦ CochainComplex.cochainComplexMinus_flat_le_kFlat D _
      (F.cochainComplexMinus_flat_mapHomologicalComplex_obj (p.prop_diag_obj j)))

variable [HasColimitsOfShape ℤ C]
  {C' : Type*} [Category C'] [Preadditive C'] [HasZeroObject C'] [HasFiniteCoproducts C']
  {ι : C' ⥤ C} [ι.Full] [ι.Faithful] [ι.Additive]
  (Λ : Abelian.LeftResolution ι) [Λ.F.PreservesZeroMorphisms]

/-- A functor preserving flat objects and colimits indexed by `ℤ` sends the functorial flat
resolution `Λ.resolutionFunctor.obj K` of a complex `K` to a K-flat complex. -/
lemma kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj [PreservesColimitsOfShape ℤ F]
    (hι : ι.essImage ≤ ObjectProperty.flat) (K : CochainComplex C ℤ) :
    (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
      ((F.mapHomologicalComplex (.up ℤ)).obj (Λ.resolutionFunctor.obj K)) :=
  F.kFlat_mapHomologicalComplex_obj_of_colimitsOfShape
    (Λ.colimitOfShapeFlatResolutionFunctorObj hι K).colimitsOfShape

end CategoryTheory.Functor
