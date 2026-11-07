# Coherence of actual common-closure operations

This internal derived unit concerns the existing common-closure induction and
trace pullback operations in `Langlands.LocalFactor.CommonClosure`. It retains
every prime, `F : PadicField.{uF} p`, the independent representation universe `uV`,
the actual finite intermediate fields of the common algebraic closure, ordinary
continuity and the exact Grothendieck quotient. No reciprocity family or
local-constant system is an argument.

The self-induction identity is imported from the published
`CommonClosure.induce_self` from the module `CommonClosureInductionTwist`.
That existing theorem applies to every proof of a self inclusion.

For inclusions `h : E.field ≤ L.field` and `h' : L.field ≤ M.field`,
`inducedRepresentationTransEquiv F E L M h h' A` identifies induction from `M`
to `L` and then to `E` with direct induction from `M` to `E`. On the actual
equivariant-function carriers its forward map is
`f ↦ (g ↦ f(g)(1))`. Its inverse is `f ↦ (g ↦ (l ↦ f(ι(l) * g)))`, where
`ι` is the actual inclusion of the subgroup fixing `L` into the subgroup fixing
`E`. The two nested subgroup restrictions and their rebracketing equivalences
are exactly the ones in `CommonClosure.inducedRepresentation`. Equivariance
proves that these formulas are inverse linear intertwiners.

The theorem `induce_trans` has the orientation
`induce F E L h (induce F L M h' x) = induce F E M (h.trans h') x`
for every actual virtual class `x`. The tower induction theorem follows by equality
on genuine representation generators: the representation equivalences give
equal classes, and the existing generator extensionality theorem identifies the
integer-linear maps on the exact quotient. This proof does not use semisimplicity.

`traceCharacter_self F E ψ` says that trace pullback along the self inclusion is
`ψ`. The inclusion algebra is identified with the identity algebra, and the
identity follows from `Algebra.trace_self_apply`.
`traceCharacter_trans F E L M h h' ψ` identifies direct trace pullback from `E`
to `M` with pullback first to `L` and then to `M`. The proof installs the algebra
structures of the actual intermediate-field inclusions and their scalar towers.
Finiteness over the original base field gives finiteness of each step. Character
extensionality and `Algebra.trace_trace` then give the result. These are the
existing nontrivial unitary additive characters in the canonical topologies;
no additional topology or character hypotheses are imposed.

The provenance is internal and derived: the function formulas verify the
coherence of the published induction construction directly, and the trace
identities specialize Mathlib's actual field trace laws. There is no new
literature claim. This supporting unit does not discharge the arithmetic Brauer
kernel identity or the full local-constant existence target.
