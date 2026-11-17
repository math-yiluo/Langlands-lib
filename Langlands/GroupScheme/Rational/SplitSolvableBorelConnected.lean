import Langlands.GroupScheme.Rational.SplitSolvableQuotientLifting
import Langlands.GroupScheme.Rational.SplitSolvableBorelConjugacyStatement
import Langlands.GroupScheme.ParabolicQuotientProperProof
import Langlands.GroupScheme.SplitSolvableFixedPointProof
import Langlands.GroupScheme.ProperPseudoComplete
import Langlands.GroupScheme.SplitTorusIntoPseudoParabolicReduction

/-! # Split-solvable containment in a split Borel of a connected group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The containment part of Milne 17.105 for a connected ambient group. -/
theorem splitSolvable_borel_containment_connected
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G)
    (hb : IsGeometricBorelSubgroup b) (hB : IsSplitSolvableGroupScheme B)
    (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G)
    (hh : IsClosedSubgroup h) (hH : IsSplitSolvableGroupScheme H) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      SubgroupFunctor.range h ≤ SubgroupFunctor.range (b ≫ (G.innerIso g).hom) := by
  obtain ⟨Q, q, hQsep, hQlft, hQqc, hqsm, hqsurj, hqqc, hfib⟩ :=
    smoothSubgroupQuotientExistence k G B b hb.1.isClosedSubgroup hb.1.smooth
  let : IsProper Q.hom := parabolicSubgroupQuotientProper k G inferInstance
    B b hb.isParabolicSubgroup Q q hQsep hQlft hQqc hqsm hqsurj hqqc hfib
  let : Smooth q.left := hqsm
  let : Surjective q.left := hqsurj
  let : QuasiCompact q.left := hqqc
  obtain ⟨x, hx⟩ := splitSolvablePseudoCompleteFixedPoint k H hH Q
    (isPseudoComplete_of_isProper Q) ⟨quotientIdentityPoint q⟩
    ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range b) q hfib).restrict h)
  obtain ⟨g, rfl⟩ := exists_rationalLift_of_splitSolvable b hb.1.isClosedSubgroup hB q hfib x
  let : IsClosedImmersion b.hom.hom.left := hb.1.isClosedSubgroup
  let : IsClosedImmersion h.hom.hom.left := hh
  let : Mono b.hom.hom := Over.mono_of_mono_left _
  let : Mono h.hom.hom := Over.mono_of_mono_left _
  have hcoset := fixedCoset_of_isFixed (SubgroupFunctor.range b) q hfib h g hx
  let f := factorOfFixedCoset h b q hfib g hcoset
  have hf : f ≫ b = h ≫ (G.innerIso g).inv := by
    simpa only [G.innerIso_inv_hom] using
      factorOfFixedCoset_comp h b q hfib g hcoset
  refine ⟨g, SubgroupFunctor.range_le_of_factor f ?_⟩
  rw [← Category.assoc, hf, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Langlands.GroupScheme
