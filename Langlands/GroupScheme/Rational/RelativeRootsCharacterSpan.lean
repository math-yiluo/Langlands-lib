import Langlands.GroupScheme.Rational.SplitCentralDirectionsConstruction
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityProof
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Rational.RelativeCharacterComplementReduction
import Langlands.GroupScheme.Rational.RelativeWeylFaithfulness

/-! # Joint spanning by relative roots and restricted rational characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Restriction to any actual split component is surjective after rationalization.
Only the finite-index part of integral character restriction is needed. -/
theorem IsSplitComponent.rationalCharacterRestrictRat_surjective
    (hG : IsConnectedReductive G) {a : A.toGrp ⟶ G} (ha : IsSplitComponent a) :
    Function.Surjective (rationalCharacterRestrictRat a) :=
  rationalization_surjective_of_finiteIndex (characterRestrict a)
    (ha.finiteIndex_range_characterRestrict hG)

/-- The root span and restricted rational characters together fill the full
rational character space of an actual maximal split torus. -/
theorem IsConnectedReductive.relativeRootSpan_sup_restrictionRange_eq_top
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) :
    haveI := hG.isAffineHom
    relativeRootSpan i ⊔ (rationalCharacterRestrictRat i).range = ⊤ := by
  let := hG.isAffineHom
  let := hG.smooth
  let := hG.connectedSpace
  let := hi.isSplitSubtorus.mono
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k G hG).1
  obtain ⟨f, hf, _, _⟩ := ha.exists_commFactor_of_isMaximalSplitTorus hi
  have hker := (ha.restriction_kernels_eq_relativeRootSpans
    rootAnnihilatorCentrality hi.1.1 f hf).1
  rw [← hker]
  apply codisjoint_iff.mp
  rw [Submodule.codisjoint_iff_exists_add_eq]
  intro x
  obtain ⟨y, hy⟩ := ha.rationalCharacterRestrictRat_surjective hG
    (rationalCharacterRestrictRat (CommGroupScheme.groupHom f) x)
  rw [← hf, rationalCharacterRestrictRat_comp, LinearMap.comp_apply] at hy
  refine ⟨x - rationalCharacterRestrictRat i y, rationalCharacterRestrictRat i y,
    ?_, LinearMap.mem_range_self _ y, sub_add_cancel _ _⟩
  change rationalCharacterRestrictRat (CommGroupScheme.groupHom f)
    (x - rationalCharacterRestrictRat i y) = 0
  rw [map_sub, hy, sub_self]

/-- Over every field, the actual relative roots together with restrictions of
actual rational characters span the rational character space of a maximal split torus. -/
def RelativeRootsRestrictedCharactersSpanStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G), IsMaximalSplitTorus i →
    haveI := hG.isAffineHom
    Submodule.span ℚ
      (toRat '' (relativeRoots i ∪ Set.range (torusCharacterRestrict i))) = ⊤

/-- Unconditional joint spanning, with no character-complement or root-system
realization premise. -/
theorem relativeRootsRestrictedCharactersSpan :
    RelativeRootsRestrictedCharactersSpanStatement.{u} := by
  intro k _ G hG T i hi
  let := hG.isAffineHom
  rw [← relativeRootSpan_sup_restrictionRange]
  exact hG.relativeRootSpan_sup_restrictionRange_eq_top i hi

end Langlands.GroupScheme
