# Transport of actual representation filtrations

This internal construction connects the existing filtration interface with
precomposition of functors and the existing scalar-character twist functor.
It is intended for assembling the fixed support filtration of normalized
induction and character localization. It does not define a modulus, assume
exactness, or identify any geometric-lemma graded piece.

Let `F` be a functor from a category `C` to representations of a group `G`
over a commutative ring `R`. A `RepSubfunctor F` specifies actual invariant
submodules, preserved by the actual maps of `F`.

`RepSubfunctor.precomp S J`, for a functor `J : D ⥤ C`, evaluates the same
submodules at `J.obj X`. The subfunctor condition is the original condition
applied to `J.map f`. `RepFunctorFiltration.precomp` applies this operation
to every step and reuses the original monotonicity and endpoint proofs at
`J.obj X`. The finite index set and its order are unchanged.

For an existing `Induction.SmoothCharacter R G`, `RepSubfunctor.twist` uses
the published `twistSubrepresentation` construction. Its underlying submodule
is exactly the original one. The ambient action is multiplied by the character,
and the existing twist functor leaves each underlying linear map unchanged.
Consequently the original subfunctor condition proves naturality.

`RepFunctorFiltration.twist` retains those same submodules at every index.
Order preservation follows from unchanged membership. The zero and full
endpoints follow from the published order isomorphism
`twistSubrepresentationOrderIso`. The explicit submodule equality lemmas
record that no support subspace or index changes during twisting.

The coefficient, group, carrier, and both source categories' object and
morphism universes are independent. Precomposition uses no topology. The twist
interface uses the existing character with an open kernel on the given
topological group; this module imports its functor rather than introducing
another scalar-twist construction. The representation-valued functors here
take values in `Rep`; no smoothness assertion for their objects is required.

Provenance is internal: these are direct transports of already defined data.
The motivation is Bernstein--Zelevinsky, *Induced representations of reductive
p-adic groups I* (1977), sections 5.3–5.4, printed page 461 (PDF page 22), where
the support subspaces are assembled with normalized localization. The present
generic transport statements are not attributed as separate theorems of that
source. The actual normalized character and concrete covariance functor must
be supplied by their independently constructed interfaces in that application.

Imported project constructions:

- `Filtration.Definitions`: actual subfunctors and finite filtrations.
- `Induction.Definitions`: `SmoothCharacter` and its actual twist functor.
- `Twist.SubquotientDefinitions`: the unchanged invariant submodule and its
  order isomorphism under scalar twisting.

Author: Worker 14.
