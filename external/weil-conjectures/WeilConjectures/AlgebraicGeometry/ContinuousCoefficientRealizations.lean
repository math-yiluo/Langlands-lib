/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization

import all WeilConjectures.AlgebraicGeometry.IntegralScalarContractive

/-! # Canonical continuous coefficient realizations

The coefficient comparisons are actual adjoints of composition with the profinite test
projection. They are monoid homomorphisms, are isomorphisms for totally disconnected
coefficients, and commute with continuous ring maps.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Compose a profinite coefficient function with the canonical profinite test projection.
Source: the continuous coefficient realization of Bhatt--Scholze, Section 6.8.
(auxiliary; not a blueprint node) -/
noncomputable def chartComparisonAdjoint (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] : Profinite.continuousMapRingObj E ⟶
      (pointLowerStar.obj ((lowerStar AddCommGrpCat.{u + 1} (toSpecZ X)).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
            (continuousMapRingSheaf X E)))) :=
  ⟨{ app := fun S ↦ AddCommGrpCat.ofHom
        { toFun := fun f ↦ ULift.up (f.down.comp (profiniteTestProjection X S.unop))
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
     naturality := by
       intro S T f
       apply ConcreteCategory.hom_ext
       intro g
       apply ULift.ext
       change (g.down.comp f.unop.hom.hom).comp (profiniteTestProjection X T.unop) =
         (g.down.comp (profiniteTestProjection X S.unop)).comp
           ((profiniteToProEtOf X).map f.unop).left.base.hom
       simp only [ContinuousMap.comp_assoc]
       erw [profiniteTestProjection_natural] }⟩

/-- The actual adjoint comparison from condensed to continuous ring coefficients.
Source: Bhatt--Scholze, Section 6.8, coefficient realization.
(auxiliary; not a blueprint node) -/
noncomputable def chartComparison (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    condensedRingObj (Profinite.continuousMapRingObj E) X ⟶
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousMapRingSheaf X E)) :=
  ((pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv _ _).symm
      (chartComparisonAdjoint X E)

private noncomputable def chartComparisonAdjointRing (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    Profinite.continuousMapRingSheaf E ⟶
      (profiniteToProEt.sheafPushforwardContinuous RingCat.{u + 1}
        (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).obj
        (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).sheafPushforwardContinuous
          RingCat.{u + 1} (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X)).obj
            (continuousMapRingSheaf X E)) :=
  ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (((ContinuousMap.compRightAlgHom ℤ E (profiniteTestProjection X S.unop)).toRingHom).comp
            ULift.ringEquiv.toRingHom))
     naturality := by
       intro S T f
       apply ConcreteCategory.hom_ext
       intro g
       apply ULift.ext
       change (g.down.comp f.unop.hom.hom).comp (profiniteTestProjection X T.unop) =
         (g.down.comp (profiniteTestProjection X S.unop)).comp
           ((profiniteToProEtOf X).map f.unop).left.base.hom
       simp only [ContinuousMap.comp_assoc]
       erw [profiniteTestProjection_natural] }⟩

private lemma chartComparisonAdjoint_isMonHom (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    IsMonHom (chartComparisonAdjoint X E) := by
  let F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology specZ.{u}
  let L := Scheme.ProEt.topology X
  let R := continuousMapRingSheaf X E
  have h₁ := pushforwardRingMonObj F K L R
  have h₂ := pushforwardRingMonObj profiniteToProEt J K
    ((F.sheafPushforwardContinuous RingCat.{u + 1} K L).obj R)
  change @IsMonHom _ _ _ _ _ _
    ((profiniteToProEt.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K).monObjObj
      (((F.sheafPushforwardContinuous AddCommGrpCat.{u + 1} K L).obj
        ((sheafCompose L (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj R)))) _
  erw [← h₁, ← h₂]
  exact Sheaf.isMonHom_sheafCompose_map J (chartComparisonAdjointRing X E)

instance chartComparison_isMonHom (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    IsMonHom (chartComparison X E) := by
  have := chartComparisonAdjoint_isMonHom X E
  let a := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
  let f : Mon.mk (Profinite.continuousMapRingObj E) ⟶
      ((lowerStar AddCommGrpCat.{u + 1} (toSpecZ X)) ⋙ pointLowerStar).mapMon.obj
        (Mon.mk ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousMapRingSheaf X E))) := Mon.ofHom (chartComparisonAdjoint X E)
  let g := (a.mapMon.homEquiv _ _).symm f
  change IsMonHom g.hom
  exact g.isMonHom_hom

/-- The canonical continuous coefficient realization commutes with continuous ring maps.

Source: Bhatt--Scholze, Section 6.8, continuous coefficient realization.
(auxiliary; not a blueprint node)

Proof: apply the inverse-image/direct-image adjunction to the two composites.
Naturality of its Hom equivalence reduces the assertion to the explicit profinite test
maps. On every section, both sides first compose with the test projection and then apply
the coefficient ring map. These operations commute pointwise. -/
lemma chartComparison_naturality (X : Scheme.{u})
    (E F : Type) [TopologicalSpace E] [Ring E] [IsTopologicalRing E]
    [TopologicalSpace F] [Ring F] [IsTopologicalRing F]
    (φ : E →+* F) (hφ : Continuous φ) :
    (upperStarFromPoint X).map
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (Profinite.continuousMapRingSheafMap φ hφ)) ≫ chartComparison X F =
      chartComparison X E ≫ (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (continuousMapRingSheafMap X φ hφ) := by
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  apply (adj.homEquiv _ _).injective
  dsimp only [upperStarFromPoint]
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [chartComparison, adj, Equiv.apply_symm_apply]
  ext S f
  rfl

instance chartComparison_isIso (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] [TotallyDisconnectedSpace E] :
    IsIso (chartComparison X E) := by
  exact integralComparison_isIso X E

instance integralChartComparison_isIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u}) :
    IsIso (chartComparison X (CondensedRing.continuousIntegers ℓ E)) := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  infer_instance

end AlgebraicGeometry.ProEtale
