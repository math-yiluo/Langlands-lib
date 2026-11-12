import Langlands.Representation.Plancherel.AvailableRenardCartanStatement
import Langlands.Representation.Plancherel.RenardDominantComparisonProof
import Langlands.GroupScheme.Rational.CentralizerRootSupport
import Langlands.GroupScheme.SimplyConnected.CoverPreimageToolkit
import Langlands.GroupScheme.SubgroupFunctor.IntersectionNormalizer

/-! # Algebraic factors and lattice conclusions for the Renard Cartan comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.Cartan

namespace Langlands.Plancherel.RenardCartan

section Algebraic

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
  (J : Set (characterLattice S)) (j : Z ⟶ G)
  (hj : (torusCentralizer i).IsRepresentedBy j)

/-- The whole ambient centralizer factors through the fixed actual standard Levi. -/
def standardLeviCentralizerFactor : Z ⟶ Standard.leviScheme i ν J :=
  (Standard.isRepresentedBy_leviHom i ν J).factorHom j
    (by rw [hj.2]; exact torusCentralizer_le_standardLevi i ν J)

@[simp]
theorem standardLeviCentralizerFactor_comp :
    standardLeviCentralizerFactor i ν J j hj ≫ Standard.leviHom i ν J = j :=
  (Standard.isRepresentedBy_leviHom i ν J).factorHom_comp _ _

/-- Closedness is reflected by the closed Levi inclusion. -/
theorem isClosedSubgroup_standardLeviCentralizerFactor (hjc : IsClosedSubgroup j) :
    IsClosedSubgroup (standardLeviCentralizerFactor i ν J j hj) :=
  IsClosedSubgroup.of_comp (Standard.isClosedSubgroup_leviHom i ν J)
    (by rw [standardLeviCentralizerFactor_comp]; exact hjc)

/-- The factor represents the whole centralizer of the same torus inside the Levi. -/
theorem isRepresentedBy_standardLeviCentralizerFactor :
    (torusCentralizer (Standard.leviTorusHom i ν J)).IsRepresentedBy
      (standardLeviCentralizerFactor i ν J j hj) := by
  have : Mono (Standard.leviHom i ν J).hom.hom :=
    (Standard.isRepresentedBy_leviHom i ν J).1
  have : Mono j.hom.hom := hj.1
  have hf : (standardLeviCentralizerFactor i ν J j hj).hom.hom ≫
      (Standard.leviHom i ν J).hom.hom = j.hom.hom := by
    rw [← Grp.comp_hom_hom, standardLeviCentralizerFactor_comp]
  refine ⟨mono_of_mono_fac hf, ?_⟩
  rw [SubgroupFunctor.range_eq_comap_of_range_comp_eq_inf
    (standardLeviCentralizerFactor i ν J j hj) (Standard.leviHom i ν J)
    (torusCentralizer i) (by
      rw [standardLeviCentralizerFactor_comp, hj.2,
        (Standard.isRepresentedBy_leviHom i ν J).2]
      apply SubgroupFunctor.ext
      intro U
      ext z
      exact ⟨fun hz => ⟨torusCentralizer_le_standardLevi i ν J U hz, hz⟩,
        And.right⟩)]
  simpa only [Standard.leviTorusHom_comp] using
    torusCentralizer_comp_comap_of_mono
      (Standard.leviTorusHom i ν J) (Standard.leviHom i ν J)

/-- The same map from the split torus factors through the centralizer in every Levi. -/
theorem comp_standardLeviCentralizerFactor (s : S.toGrp ⟶ Z) (hs : s ≫ j = i) :
    s ≫ standardLeviCentralizerFactor i ν J j hj = Standard.leviTorusHom i ν J := by
  have : Mono (Standard.leviHom i ν J).hom.hom :=
    (Standard.isRepresentedBy_leviHom i ν J).1
  apply Grp.hom_ext
  apply (cancel_mono (Standard.leviHom i ν J).hom.hom).mp
  simp only [← Grp.comp_hom_hom, Category.assoc,
    standardLeviCentralizerFactor_comp, Standard.leviTorusHom_comp, hs]

/-- Roots in a closed Levi are ambient roots; positivity uses the unchanged cocharacter. -/
theorem positiveRelativeRoots_standardLevi_subset :
    haveI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
      (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
    positiveRelativeRoots (Standard.leviTorusHom i ν J) ν ⊆
      positiveRelativeRoots i ν := by
  let : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  intro α hα
  exact ⟨relativeRoots_subset_of_factor
    (Standard.isRepresentedBy_leviHom i ν J) (Standard.leviTorusHom i ν J)
    (Standard.leviTorusHom_comp i ν J) hα.1, hα.2⟩

end Algebraic

section Lattice

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
  (ν : cocharacterLattice S) (s : S.toGrp ⟶ Z)
  (h : Function.Bijective (restrictionEvaluation s))

include hi

/-- The published lattice comparison needs no additional building premise. -/
theorem dominantLattice_of_maximalSplitTorus :
    DominantCentralizerLatticeConclusions i ν s h := by
  have hS := hi.isSplitSubtorus.1
  exact dominantCentralizerLatticeConclusions_of_latticeComparison s h i ν
    (hS.finite_positiveRelativeRoots i ν)
    (finiteIndex_splitValuationImage_of_comparison s h hS)
    (bijOn_C0_splitValuationImage_of_comparison s h hS)

/-- In a standard Levi the same lattice and valuation meet only a different root chamber. -/
theorem dominantLattice_standardLevi (J : Set (characterLattice S)) :
    haveI : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
      (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
    DominantCentralizerLatticeConclusions (Standard.leviTorusHom i ν J) ν s h := by
  let : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom
  have hS := hi.isSplitSubtorus.1
  exact dominantCentralizerLatticeConclusions_of_latticeComparison s h
    (Standard.leviTorusHom i ν J) ν
    ((hS.finite_positiveRelativeRoots i ν).subset
      (positiveRelativeRoots_standardLevi_subset i ν J))
    (finiteIndex_splitValuationImage_of_comparison s h hS)
    (bijOn_C0_splitValuationImage_of_comparison s h hS)

end Lattice

end Langlands.Plancherel.RenardCartan
