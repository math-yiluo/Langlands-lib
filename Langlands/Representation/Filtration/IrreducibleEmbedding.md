# Irreducible embeddings into actual filtration layers

Author: Worker 494.

This internal algebraic supporting unit concerns a supplied finite
`ObjectRepFiltration A n`. The coefficient ring, acting monoid, ambient
carrier, and source carrier have independent universes. No topology,
smoothness, finite dimension, or simple-factor hypothesis is used.

`mapToStep` restricts an actual intertwiner's codomain to a supplied
filtration step containing its entire image. `mapToGraded` composes this
restriction to step `i.succ` with the existing actual `gradedProjection i`.
The kernel membership law `mapToGraded_eq_zero_iff` states that a source
vector maps to zero precisely when its original image lies in step
`i.castSucc`. These constructions work over any commutative ring.

`exists_mapToGraded_ne_zero` also works over a commutative ring. For a
nonzero intertwiner `f`, the image is not contained in the initial zero
step and is contained in the final full step. Finite induction produces
adjacent steps such that the upper step contains the image and the lower
step does not. The corresponding actual graded map cannot be zero by the
kernel membership law. Repeated steps and length zero need no separate
assumptions: at length zero the endpoint conditions contradict the
nonzero-map premise.

Over a field, `exists_injective_mapToGraded` additionally assumes that the
source representation is irreducible. Mathlib's algebraic Schur lemma
makes the nonzero graded map injective. Its conclusion retains the index
and containment witness, so the map is precisely the restriction and
projection of the original intertwiner. `exists_injective_graded` accepts
an injective original intertwiner instead of its nonvanishing. An
irreducible source is nonzero; injectivity therefore implies that the map
is nonzero. The theorem returns an actual injective intertwiner into one
of the supplied filtration's actual graded representations.

This is a derived elementary construction, not a translated literature
assertion. It supplies the embedding-to-a-layer algebra needed for a
future linked-segment reduction. It does not construct a segment-product
filtration, prove a composition-factor identity, or prove any segment or
multisegment classification result. The only project dependency is
`Filtration.SubsingletonProof` and its actual filtration definitions;
source irreducibility is used through Mathlib's group-algebra Schur lemma.
No p-adic classification theorem enters the argument.
