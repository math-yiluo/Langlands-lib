# Commuting finite adelic and differential actions

This internal construction uses the actual function spaces and differential
operators in `EnvelopingAction` and `DifferentialCenterFinite`. It applies to
every number field `K : Type u` and every natural rank, including zero, with
complex coefficients. The finite adelic group keeps its existing topology.

`finiteSmoothFiniteRightAction` restricts actual right translation to the
finite adelic factor on `FiniteSmoothRationalFunctions`. Its infinite slice
at `b` is the original slice at `b*d`. Since every genuine enveloping
operator acts on each infinite slice independently, this reindexing commutes
with that operator. Injectivity of the family of slice maps transfers the
pointwise identity back to actual adelic functions.

`finiteSmoothFiniteCenterIntertwiner` specializes this commutation to the
enveloping center. The existing injective slice-family criterion and
finite-vector image theorem then prove preservation of simultaneous center
finiteness. Moreover, `centerFamilyAnnihilator_finiteRightAction` proves
equality of the two common annihilator ideals. Reindexing all finite slices
by the bijection `b ↦ b*d` preserves exactly the condition that one central
operator kills every slice; using `b*d⁻¹` proves the reverse implication.

`centerFiniteFiniteSmoothSubrepresentation` and
`centerFiniteFiniteSmoothRightAction` restrict this finite adelic action to
the already constructed `CenterFiniteFiniteSmoothRationalFunctions`.
`CenterFiniteFiniteAction` abbreviates its representation type. The action
is smooth in the established open-stabilizer sense: the same open finite
subgroup fixing an ambient function fixes it in the invariant subspace.
No compactness theorem is required for this claim.

On this space, finite right translation commutes with the existing
`centerFiniteEnvelopingAction`. Thus
`centerFiniteDifferentialFiniteIntertwiner` bundles each actual differential
operator as an intertwiner for the smooth finite adelic representation.
`centerFiniteFiniteSmoothInclusion` is an injective equivariant inclusion
into the finite-smooth ambient space. It also respects the genuine
enveloping action. The evaluation formula remains
`(R(d)f)(x) = f(x * ofFinite d)`.

The provenance is internal: the finite/infinite product multiplication,
the published exact differential slice formula, faithful slice extraction,
and the existing finite-vector criterion prove every construction obligation.
There is no supplied commutation or stability certificate. These results
combine actions on a concrete existing space; they do not yet impose
growth, compact-type finiteness, or cuspidality, or construct a Hecke action
or the full automorphic representation category.
