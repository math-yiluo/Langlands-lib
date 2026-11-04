import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.RelativeWeylSpanFiniteness
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # Faithfulness and finiteness of actual reductive relative Weyl groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The actual relative Weyl quotient acts faithfully on the rational root span
of every maximal split torus in a connected reductive group. -/
theorem IsConnectedReductive.relativeWeylAction_injective
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) :
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    Function.Injective (relativeWeylAction i) := by
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  exact hi.1.1.relativeWeylAction_injective_of_span i
    (relativeRootsRestrictedCharactersSpan k G hG T i hi)

/-- The action of the actual quotient on the actual roots is faithful. -/
theorem IsConnectedReductive.relativeWeylRootPermutation_injective
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) :
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    Function.Injective (relativeWeylRootPermutation i) := by
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  exact hi.1.1.relativeWeylRootPermutation_injective_of_span i
    (relativeRootsRestrictedCharactersSpan k G hG T i hi)

/-- Identify the actual quotient with its image on the actual rational root span,
using the unconditional reductive faithfulness theorem. -/
def IsConnectedReductive.relativeWeylEquivRootActionRange
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) :
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    relativeWeylGroup i ≃* (relativeWeylAction i).range := by
  letI := hG.isAffineHom
  letI := hi.isSplitSubtorus.mono
  exact MonoidHom.ofInjective (hG.relativeWeylAction_injective i hi)

/-- The relative Weyl quotient of a maximal split torus is finite. -/
theorem IsConnectedReductive.finite_relativeWeylGroup
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) : Finite (relativeWeylGroup i) := by
  let := hG.isAffineHom
  let := hG.smooth
  let := hi.isSplitSubtorus.mono
  exact hi.1.1.finite_relativeWeylGroup_of_span i
    (relativeRootsRestrictedCharactersSpan k G hG T i hi)

/-- Root-span faithfulness for a split maximal torus, in the maximal-torus
convention used by absolute-root statements. -/
theorem IsConnectedReductive.relativeWeylAction_injective_of_isMaximalTorus
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp) :
    haveI := hG.isAffineHom
    haveI := hi.2.1.mono
    Function.Injective (relativeWeylAction i) :=
  hG.relativeWeylAction_injective i (hi.isMaximalSplitTorus hT)

/-- Root-permutation faithfulness for a split maximal torus. -/
theorem IsConnectedReductive.relativeWeylRootPermutation_injective_of_isMaximalTorus
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp) :
    haveI := hG.isAffineHom
    haveI := hi.2.1.mono
    Function.Injective (relativeWeylRootPermutation i) :=
  hG.relativeWeylRootPermutation_injective i (hi.isMaximalSplitTorus hT)

/-- Finiteness of the actual relative Weyl quotient for a split maximal torus. -/
theorem IsConnectedReductive.finite_relativeWeylGroup_of_isMaximalTorus
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp) :
    Finite (relativeWeylGroup i) :=
  hG.finite_relativeWeylGroup i (hi.isMaximalSplitTorus hT)

end Langlands.GroupScheme
