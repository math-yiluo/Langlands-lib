/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteHypercoverCohomologyTruncation
/-! # Canonical maps for a hypercover pulled back along a cone -/
@[expose] public section
universe u' u
open CategoryTheory Limits Opposite AlgebraicTopology
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
variable {S : Scheme.{u}} {I : Type u} [SmallCategory I] (D : I ⥤ Over S)
  [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
  (c : Cone D) [CompactSpace c.pt.left] [QuasiSeparatedSpace c.pt.left]

/-- The underlying scheme map of a cone leg, with its vertex made explicit. -/
abbrev coneProjection (i : I) : c.pt.left ⟶ (D.obj i).left := (c.π.app i).left

/-- Inverse-image composition identifies the stage pullback with the limit coefficients. -/
noncomputable def coneCoefficientMap (F : Sheaf S.smallEtaleTopology A) (i : I) :
    (Etale.upperStar A (coneProjection D c i)).obj
        ((Etale.upperStar A (D.obj i).hom).obj F) ⟶
      (Etale.upperStar A c.pt.hom).obj F :=
  (Etale.upperStarComp A (coneProjection D c i) (D.obj i).hom c.pt.hom
    (Over.w (c.π.app i)).symm).inv.app F

/-- The stage-to-limit map on full hypercover cohomology.
Source: blueprint étale cohomology continuity, detailed proof paragraph 2.
Use the inverse of inverse-image composition to identify pullback of each stage coefficient sheaf
with the cone coefficient sheaf. Apply hypercover pullback with this coefficient map. Mapping the
unit and the coefficient map to short complexes gives the single-hypercover comparison;
functoriality of homology proves its injection formula. For a tail object j→i, base change the
initial hypercover along D_j→D_i. The canonical pullback-pasting morphism refines its limit
pullback from the initial limit pullback. Compose the cone comparison with this refinement. The
finite-refinement colimit relation gives the tail injection formula.
(auxiliary; not a blueprint node) -/
noncomputable def coneHypercoverMap (F : Sheaf S.smallEtaleTopology A) (q : ℕ) (i : I) :
    hypercoverCohomology A ((Etale.upperStar A (D.obj i).hom).obj F) q ⟶
      hypercoverCohomology A ((Etale.upperStar A c.pt.hom).obj F) q :=
  hypercoverPullback A (coneProjection D c i) _ _ (coneCoefficientMap A D c F i) q

/-- The cochain map underlying the stage-to-limit map on a single hypercover. -/
noncomputable def coneCochainMap (F : Sheaf S.smallEtaleTopology A) (q : ℕ) (i : I)
    (V : FiniteSplitEtaleHypercover (D.obj i).left) :
    sectionShortComplex A ((Etale.upperStar A (D.obj i).hom).obj F) V q ⟶
      sectionShortComplex A ((Etale.upperStar A c.pt.hom).obj F)
        (V.baseChange (coneProjection D c i)) q :=
  (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℕ) q).map
    (baseChangeCochainMap A V (coneProjection D c i) _ ≫
      (alternatingCofaceMapComplex A).map
        (Functor.whiskerLeft (V.baseChange (coneProjection D c i)).simplicial.rightOp
          (coneCoefficientMap A D c F i).hom))

/-- The canonical cochain map agrees with the previously constructed colimit map. -/
theorem coneCochainMap_homology_comp_ι (F : Sheaf S.smallEtaleTopology A) (q : ℕ) (i : I)
    (V : FiniteSplitEtaleHypercover (D.obj i).left) :
    ShortComplex.homologyMap (coneCochainMap A D c F q i V) ≫
        hypercoverCohomologyι A ((Etale.upperStar A c.pt.hom).obj F) q
          (V.baseChange (coneProjection D c i)) =
      hypercoverCohomologyι A ((Etale.upperStar A (D.obj i).hom).obj F) q V ≫
        coneHypercoverMap A D c F q i := by
  rw [coneHypercoverMap, hypercoverCohomologyι_comp_pullback]
  dsimp only [coneCochainMap, baseChangeCohomologyComponent, baseChangeCohomologyMap]
  rw [Functor.map_comp, ShortComplex.homologyMap_comp, Category.assoc]
  rfl

/-- Pull the initial stage hypercover to a later object of its over category. -/
noncomputable def tailHypercover (i : I) (V : FiniteSplitEtaleHypercover (D.obj i).left)
    (j : Over i) : FiniteSplitEtaleHypercover (D.obj j.left).left :=
  V.baseChange (D.map j.hom).left

/-- Pullback pasting identifies the limit hypercover with the iterated pullback. -/
noncomputable def tailLimitRefinement (i : I)
    (V : FiniteSplitEtaleHypercover (D.obj i).left) (j : Over i) :
    (V.baseChange (coneProjection D c i)).Refinement
      ((tailHypercover D i V j).baseChange (coneProjection D c j.left)) :=
  Functor.whiskerLeft V.simplicial
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      (coneProjection D c j.left) (D.map j.hom).left (coneProjection D c i)
      (congrArg (fun t ↦ t.left) (c.w j.hom)).symm).hom

/-- Comparison from a tail stage's cochain terms to those of the initial limit pullback. -/
noncomputable def tailCochainMap (F : Sheaf S.smallEtaleTopology A) (q : ℕ) (i : I)
    (V : FiniteSplitEtaleHypercover (D.obj i).left) (j : Over i) :
    sectionShortComplex A ((Etale.upperStar A (D.obj j.left).hom).obj F)
        (tailHypercover D i V j) q ⟶
      sectionShortComplex A ((Etale.upperStar A c.pt.hom).obj F)
        (V.baseChange (coneProjection D c i)) q :=
  coneCochainMap A D c F q j.left (tailHypercover D i V j) ≫
    finiteRefinementShortComplexMap A ((Etale.upperStar A c.pt.hom).obj F) q
      ((SimplicialObject.truncation (q + 1)).map (tailLimitRefinement D c i V j))

/-- Each tail comparison factors, after homology, through the appropriate stage object. -/
theorem tailCochainMap_homology_comp_ι
    (F : Sheaf S.smallEtaleTopology A) (q : ℕ) (i : I)
    (V : FiniteSplitEtaleHypercover (D.obj i).left) (j : Over i) :
    ShortComplex.homologyMap (tailCochainMap A D c F q i V j) ≫
        hypercoverCohomologyι A ((Etale.upperStar A c.pt.hom).obj F) q
          (V.baseChange (coneProjection D c i)) =
      hypercoverCohomologyι A ((Etale.upperStar A (D.obj j.left).hom).obj F) q
          (tailHypercover D i V j) ≫ coneHypercoverMap A D c F q j.left := by
  rw [tailCochainMap, ShortComplex.homologyMap_comp, Category.assoc,
    finiteRefinement_homology_comp_ι, coneCochainMap_homology_comp_ι]

end AlgebraicGeometry.FiniteSplitEtaleHypercover
