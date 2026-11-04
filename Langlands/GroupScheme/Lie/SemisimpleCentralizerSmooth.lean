import Langlands.GroupScheme.Lie.ConjugationGeometric
import Langlands.GroupScheme.Lie.ElementCentralizerQuotient
import Langlands.GroupScheme.Lie.ElementCentralizerRepresentability
import Langlands.GroupScheme.Lie.SemisimpleCentralizerSmoothStatement
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Smooth representatives of actual semisimple Lie-element centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Lie

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

section Representative

variable [LocallyOfFiniteType G.X.hom] (X : lieKernel G k)

/-- A chosen actual closed group scheme representing the Lie-element
centralizer on all test schemes. -/
def elementCentralizerGroup : GroupScheme (Spec (CommRingCat.of k)) :=
  Classical.choose (elementCentralizer_isClosedRepresentable G X)

/-- The closed inclusion of the chosen Lie-element centralizer. -/
def elementCentralizerGroupι : elementCentralizerGroup G X ⟶ G :=
  Classical.choose (Classical.choose_spec (elementCentralizer_isClosedRepresentable G X))

/-- The chosen inclusion represents the original all-test centralizer. -/
theorem elementCentralizerGroup_isRepresentedBy :
    (elementCentralizer G X).IsRepresentedBy (elementCentralizerGroupι G X) :=
  (Classical.choose_spec
    (Classical.choose_spec (elementCentralizer_isClosedRepresentable G X))).1

/-- The chosen representative is a closed subgroup of the original group. -/
theorem isClosedSubgroup_elementCentralizerGroupι :
    IsClosedSubgroup (elementCentralizerGroupι G X) :=
  (Classical.choose_spec
    (Classical.choose_spec (elementCentralizer_isClosedRepresentable G X))).2

instance isAffineHom_elementCentralizerGroup :
    IsAffineHom (elementCentralizerGroup G X).X.hom := by
  have : IsClosedImmersion (elementCentralizerGroupι G X).hom.hom.left :=
    isClosedSubgroup_elementCentralizerGroupι G X
  rw [← Over.w (elementCentralizerGroupι G X).hom.hom]
  infer_instance

end Representative

variable [Smooth G.X.hom]

/-- Geometric eigenspace decomposition and faithfully flat descent make the
actual conjugation-image quotient smooth over the original field. -/
theorem smooth_elementCentralizerQuotient_of_isSemisimple
    {X : lieKernel G k} (hX : IsSemisimpleElement G X) :
    Smooth (elementCentralizerQuotient G X).hom := by
  have : Algebra.Smooth (CommRingCat.of k) (coordinateAlgebra G) :=
    (DynamicSmooth.smooth_algSpec_iff _).1
      (smooth_of_over_iso (coordinateIso G) inferInstance)
  apply (DynamicSmooth.smooth_algSpec_iff
    (elementCentralizerQuotientAlgebra G X)).2
  change Algebra.Smooth k (coordinateAlgebra G ⧸ conjugationIdeal G X)
  rw [conjugationIdeal_eq_imageIdeal]
  exact Langlands.Algebra.SemisimpleDerivation.smooth_quotient_imageIdeal_of_eigenBaseChange
    (AlgebraicClosure k) (conjugationDerivation G X)
    (hX.hasEigenDecomposition_conjugation_baseChange G)

/-- Every closed representative of the actual centralizer of a semisimple Lie
element is smooth, over any field and without a connectedness hypothesis. -/
theorem smooth_elementCentralizer_of_isSemisimple
    {X : lieKernel G k} (hX : IsSemisimpleElement G X)
    {C : GroupScheme (Spec (CommRingCat.of k))} (j : C ⟶ G)
    (hrep : (elementCentralizer G X).IsRepresentedBy j)
    (hj : IsClosedSubgroup j) :
    Smooth C.X.hom := by
  obtain ⟨e, _⟩ := exists_elementCentralizerQuotientIso_of_isClosedSubgroup G X j hrep hj
  exact smooth_of_over_iso e (smooth_elementCentralizerQuotient_of_isSemisimple G hX)

/-- The chosen actual Lie-element centralizer is smooth for a semisimple
element. -/
theorem smooth_elementCentralizerGroup
    {X : lieKernel G k} (hX : IsSemisimpleElement G X) :
    Smooth (elementCentralizerGroup G X).X.hom :=
  smooth_elementCentralizer_of_isSemisimple G hX (elementCentralizerGroupι G X)
    (elementCentralizerGroup_isRepresentedBy G X)
    (isClosedSubgroup_elementCentralizerGroupι G X)

/-- The universe-general smooth-centralizer proposition follows from the
stronger result without connectedness. -/
theorem semisimpleCentralizerSmooth : SemisimpleCentralizerSmoothStatement.{u} := by
  intro k _ G _ _ _ X hX C j hrep hj
  exact smooth_elementCentralizer_of_isSemisimple G hX j hrep hj

end Langlands.GroupScheme.Lie
