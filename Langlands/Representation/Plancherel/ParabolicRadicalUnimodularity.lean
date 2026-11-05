import Langlands.GroupScheme.Rational.ParabolicRootRadicals
import Langlands.Representation.Aubert.General.DynamicInductionNormalization

/-! # Unimodularity of a supplied geometric parabolic radical -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe u

/-- The supplied radical has trivial inner Haar modulus in the canonical
rational-point topology. The comparison uses the complete compatible root
presentation, without assuming existence of further geometric radicals. -/
theorem parabolicRadical_isUnimodular
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (rationalPoints G)]
      [NonarchimedeanGroup (rationalPoints G)]
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      (M P U : GroupScheme (Spec (CommRingCat.of F)))
      (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M) (n : U ⟶ P)
      (_r : ParabolicRootPresentation p l a)
      (_hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (hU : IsClosed (((SubgroupFunctor.range (n ≫ p)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))) : Set (rationalPoints G))),
      Aubert.General.IsUnimodularModulus
        ((SubgroupFunctor.range (n ≫ p)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hU := by
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro _ _ A M P U p l a n r hn hU
  have hUdyn : IsClosed (((Dynamic.unipotent
      (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of F))))) : Set (rationalPoints G)) := by
    simpa only [r.range_comp_radical_eq hn] using hU
  have hδ := Aubert.General.DynamicNormalization.dynamicUnipotent_isUnimodular
    F G hG (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p) hUdyn
  simpa only [r.range_comp_radical_eq hn] using hδ

end Langlands.Plancherel
