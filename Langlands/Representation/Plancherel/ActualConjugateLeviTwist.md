# Actual unramified twists under rational conjugation

This internal adapter supplies an elementary prerequisite for Waldspurger
(2003), V.3 formula (1), printed p.295 / PDF p.61, registered as
`waldspurger-2003-plancherel`. It identifies the inducing representation
obtained by conjugating a full unramified twist with the corresponding
full unramified twist of the canonical conjugate representation. The
construction is derived from the published actual centralizer scheme
isomorphism and its point comparison; it is not an analytic continuation
or a normalized standard intertwining operator.

Work over any nonarchimedean local field `F`, with an affine locally
finite type group scheme `G/F`, a cocharacter `χ` and a rational point `g`.
The representation carrier universe is independent of the field universe.
All point topologies are the canonical ones. No connected reductivity,
splitness, characteristic zero, admissibility or irreducibility assumption
is needed for this elementary identification.

`conjugateParameter χ g` transports characters along the inverse of the
actual scheme isomorphism `parameterConjugationIso χ g`. Its domain and
codomain retain every rational-character norm on the respective actual
centralizer schemes. `conjugateParameter_apply` proves that, after the
published `parameterTransport` identifications with the literal Levis,
the resulting character at `m` is the source character at
`(leviConjugation χ g).symm m`.

The implemented proof first evaluates character transport along an
abstract affine group scheme isomorphism, using the published inverse
restriction identity. It then combines
`parameterHomeomorph_parameterConjugationIso` with the inverse identities
of the actual point homeomorphisms. This gives the displayed literal-Levi
character identity without any additional comparison premise.

`conjugateTwistEquiv χ g z A` is an actual representation equivalence
from the canonical conjugate of `A` twisted by
`(parameterTransport χ z).val.toMonoidHom` to the canonical conjugate
of `A` twisted by
`(parameterTransport (χ ≫ (G.innerIso g).hom) (conjugateParameter χ g z)).val.toMonoidHom`.
Both twists use the published unramified-character open-kernel proof.
Its underlying linear equivalence is the identity on `A`. The proof
constructs the identity equivalence for an abstract pullback and two
pointwise corresponding open-kernel characters, then specializes it
using the proved literal-Levi character identity. In particular, this
unit introduces no scalar, Haar measure or formal-degree renormalization.
The actual translated forward/inverse-reverse-dual coefficient tensor
and its substantive extension properties are separate constructions.
