import Langlands.Representation.CompactCoefficient.AmbientProjector
import Langlands.Representation.Category.Subquotients

/-!
# A smooth summand of a restriction, from an invariant subspace

For a subgroup `H` of a topological group `G` and a smooth complex representation `π`
of `G`, an invariant subspace `W` of the restriction of `π` to `H` defines a smooth
representation of `H` with the carrier universe of `π`, together with an injective
equivariant map into the published restriction `SmoothRep.restrictSubgroup H π`; it is
irreducible when `W` is. This turns the irreducible subrepresentation supplied by the
first clause of Renard VI.3.2(i) (`RationalNormKernelOrbitStatement`, with
`H = rationalCommonNormKernel G`) into the pair `(ρ, j)` that the VI.4.1 and VI.4.4
statements quantify over.
-/

noncomputable section

open CategoryTheory

namespace Langlands.CuspidalSupport

universe uF uV

section Summand

variable {G : Type uF} [Group G] [TopologicalSpace G] (H : Subgroup G)
  (π : SmoothRep.{0, uF, uV} ℂ G)

/-- The smooth representation of `H` on an invariant subspace `W` of the restriction
of `π` to `H`, with the carrier of `π` (Mathlib's subrepresentation). -/
def restrictionSummand (W : Subrepresentation (π.representation.comp H.subtype)) :
    SmoothRep.{0, uF, uV} ℂ H :=
  SmoothRep.subrepresentation (SmoothRep.restrictSubgroup H π) W

/-- The inclusion of `restrictionSummand H π W` into the restriction of `π` to `H`. -/
def restrictionSummandι (W : Subrepresentation (π.representation.comp H.subtype)) :
    restrictionSummand H π W ⟶ SmoothRep.restrictSubgroup H π :=
  SmoothRep.subtype (SmoothRep.restrictSubgroup H π) W

theorem restrictionSummandι_injective
    (W : Subrepresentation (π.representation.comp H.subtype)) :
    Function.Injective (SmoothRep.hom (restrictionSummandι H π W)) :=
  SmoothRep.subtype_injective (SmoothRep.restrictSubgroup H π) W

theorem restrictionSummand_isIrreducible
    (W : Subrepresentation (π.representation.comp H.subtype))
    (hW : W.toRepresentation.IsIrreducible) : (restrictionSummand H π W).IsIrreducible :=
  hW

end Summand

end Langlands.CuspidalSupport
