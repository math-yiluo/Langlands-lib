# The algebraic fundamental group from maximal tori and derived covers

This module constructs a chosen presentation of the algebraic fundamental group
of an actual connected reductive group scheme over a field. Its sources are
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Construction 11.3.1
and Definition 11.3.2, printed p. 427 (PDF p. 458). The November 2024 corrections
do not change these passages.

`Choice k G` contains an actual maximal torus inclusion and an actual simply
connected cover of the full derived subgroup. `nonempty_choice` uses the Library's
proved maximal-torus and derived-cover existence theorems, so `chosenChoice`
requires only connected reductivity of `G`.

For each choice, `scPreimage` is the actual scheme-theoretic pullback of the
maximal torus along the derived-cover map. The published derived-cover preimage
theorem proves it is a torus; `scTorus` equips that same group scheme with its
resulting commutative structure. `scToTorus` is the pullback projection.
`corootMap` is postcomposition with its base change on the actual cocharacter
lattices. `corootImage` is its image submodule, and `atChoice` is the integral
quotient by that image. No root lattice or abstract abelian group is supplied as
data. Injectivity and maximality are stated separately in the companion statement
module and are not needed to form the image quotient.

The coefficient extension `E/k` is explicit. For the geometric fundamental group
one takes a separable closure; the quotient constructions themselves work for
any field extension. `fundamentalGroup k G E hG` chooses the presentation above.
It represents KP's limit/colimit definition using the canonical comparisons in
the companion statement, whose proof remains an obligation.

The representation `galoisRepresentation` descends the Library's actual Galois
action on cocharacters. The implemented proof of stability uses naturality of
cocharacter transport under the actual torus morphism. The identity and
composition laws of the descended action follow on quotient representatives
from those of the original action. `fundamentalGroupGalois` is this action for
the chosen presentation.

`IsConjugationComparison` requires that a torus isomorphism is the restriction
of conjugation by an actual geometric point of `G`. `IsCanonicalComparison`
requires existence of such a point and isomorphism and their specified action
on all quotient representatives. `comparison` selects a linear map by this
condition using epsilon. Its helper `comparison_spec` proves only that existence
implies the selection law. The companion unconditional statement supplies the
unproved existence, uniqueness, bijectivity, Galois equivariance, independence
of every conjugator, and coherence laws. Allowing any conjugator in `G(E)`
is equivalent to the source's derived-cover conjugators: the Weyl action on the
quotient is trivial. Neither the comparison's existence nor its independence is
assumed as a hypothesis of the definition.
