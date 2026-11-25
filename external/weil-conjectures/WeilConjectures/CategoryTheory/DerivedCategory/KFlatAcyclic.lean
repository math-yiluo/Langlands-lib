/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs

/-!
# Acyclic K-flat complexes

Let `C` be a Grothendieck abelian closed braided monoidal category with functorial flat
resolutions. An acyclic K-flat complex `P` stays acyclic after tensoring termwise with any object
`F` (`CochainComplex.acyclic_tensorRight_of_kFlat`): `P ⊗ F` represents the derived tensor product
`P ⊗ᴸ F[0]`, which vanishes with `P` [Stacks, Tag 064K].

A functor which sends acyclic K-flat complexes to acyclic complexes preserves the
quasi-isomorphisms between K-flat complexes (`CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'`),
since the mapping cone of a quasi-isomorphism between K-flat complexes is K-flat and acyclic.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory ZeroObject

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A complex is zero in the derived category if and only if it is acyclic. -/
lemma isZero_Q_obj_iff (K : CochainComplex C ℤ) : IsZero (Q.obj K) ↔ K.Acyclic := by
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ((homologyFunctor C n).map_isZero h).of_iso
      ((homologyFunctorFactors C n).app K).symm
  · have : QuasiIso (0 : K ⟶ 0) :=
      ⟨fun n ↦ (quasiIsoAt_iff_exactAt' _ n (by
        rw [HomologicalComplex.exactAt_iff]
        exact ShortComplex.exact_of_isZero_X₂ _
          ((HomologicalComplex.eval _ _ n).map_isZero (isZero_zero _)))).2 (h n)⟩
    exact (Q.map_isZero (isZero_zero _)).of_iso (asIso (Q.map (0 : K ⟶ 0)))

/-- A morphism of complexes is a quasi-isomorphism if and only if its mapping cone is
acyclic. -/
lemma quasiIso_iff_acyclic_mappingCone {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← isZero_Q_obj_iff, ← isIso_Q_map_iff_quasiIso]
  exact ((Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)).isZero₃_iff_isIso₁
    (mappingCone_triangle_distinguished f)).symm

end DerivedCategory

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

/-- **An acyclic K-flat complex stays acyclic after tensoring with an object.** If `P` is K-flat
and acyclic, then so is the complex `P ⊗ F` obtained by tensoring each term with an object `F`:
it represents the derived tensor product `P ⊗ᴸ F[0]`, which vanishes since `P` does
[Stacks, Tag 064K]. -/
lemma acyclic_tensorRight_of_kFlat (P : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) (hP' : P.Acyclic) (F : C) :
    (((tensorRight F).mapHomologicalComplex _).obj P).Acyclic := by
  rw [← DerivedCategory.isZero_Q_obj_iff]
  refine IsZero.of_iso ?_ (DerivedCategory.QObjTensorSingleFunctorObjIso P hP F).symm
  have h := (DerivedCategory.isZero_Q_obj_iff P).2 hP'
  rw [IsZero.iff_id_eq_zero, ← id_whiskerRight, h.eq_of_src (𝟙 _) 0,
    MonoidalPreadditive.zero_whiskerRight]

end CochainComplex

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type*} [Category D] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (F : C ⥤ D) [F.Additive]

/-- A functor which sends acyclic K-flat complexes to acyclic complexes preserves the
quasi-isomorphisms between K-flat complexes: the mapping cone of such a quasi-isomorphism is
K-flat and acyclic. -/
lemma PreservesKFlatQuasiIso.mk'
    (hF : ∀ (K : CochainComplex C ℤ), (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K →
      K.Acyclic → ((F.mapHomologicalComplex _).obj K).Acyclic) :
    F.PreservesKFlatQuasiIso where
  quasiIso_map {K L} hK hL f hf := by
    let := HasDerivedCategory.standard C
    let := HasDerivedCategory.standard D
    have hK' := (HomotopyCategory.kFlat_quotient_obj_iff K).2 hK
    have hL' := (HomotopyCategory.kFlat_quotient_obj_iff L).2 hL
    have h₃ : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
        ((HomotopyCategory.quotient C (.up ℤ)).obj (CochainComplex.mappingCone f)) :=
      (HomotopyCategory.quasiIso C (.up ℤ)).kFlat.ext_of_isTriangulatedClosed₃
        (CochainComplex.mappingCone.triangleh f)
        (HomotopyCategory.mappingCone_triangleh_distinguished f) hK' hL'
    have hcone := (HomotopyCategory.kFlat_quotient_obj_iff _).1 h₃
    rw [DerivedCategory.quasiIso_iff_acyclic_mappingCone] at hf ⊢
    exact (hF _ hcone hf).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso f F)

end CategoryTheory.Functor
