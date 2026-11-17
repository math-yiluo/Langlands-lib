import Langlands.GroupScheme.Reductive.AffinePinnedTorusCorrection
import Langlands.GroupScheme.Reductive.AffinePinnedExistenceAssembly
import Langlands.GroupScheme.Reductive.BasedPinningCharacters

/-! # Actual fppf pinned corrections of arbitrary comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace AffinePinnedModel

/-- The affine based-correction input follows from the actual inverse-unit
torus correction, with its all-test pinning equations. -/
theorem hasAffineBasedPinnedCorrections : HasAffineBasedPinnedCorrections.{u} := by
  intro M N A _ _ _ d
  obtain ⟨W, p, z, hf, hs, hl, hp⟩ :=
    exists_fppf_pinnedCorrection_of_aligned M N A
      d.commTorusIso d.groupIso d.commTorusIso_square
      d.simpleEquiv d.simpleCharacter_congr d.cocharacter_comp
  exact ⟨{
    space := W
    map := p
    flat := hf
    surjective := hs
    locallyOfFinitePresentation := hl
    section_ := z
    pinned := hp
  }⟩

/-- Every actual comparison of arbitrary-scheme pullbacks admits a single
fppf cover and an actual target section making it concretely locally pinned. -/
def fppfPinnedCorrection {M N : AffinePinnedModel.{u}} {T : Scheme.{u}}
    {f : T ⟶ M.base} {g : T ⟶ N.base} (e : Comparison f g) :
    FppfPinnedCorrection e :=
  FppfPinnedCorrection.ofAffineBasedInput hasAffineBasedPinnedCorrections e

end AffinePinnedModel

/-- Unconditional geometric local normalization, retaining the exact actual
source-conjugator equation over arbitrary common schemes. -/
theorem fppfLocalPinnedNormalizationExistence :
    FppfLocalPinnedNormalizationExistenceStatement.{u} :=
  fppfLocalPinnedNormalization_of_affineBasedPinnedCorrections
    AffinePinnedModel.hasAffineBasedPinnedCorrections

end Langlands.GroupScheme
