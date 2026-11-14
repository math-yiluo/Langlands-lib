# Bounded adjoint preimages in the rational norm kernel

`AdjointNormKernelBoundedPreimageStatement` is an internal prerequisite for
KP Proposition 2.2.16. It is a statement awaiting proof.

For a connected reductive group `G` over a nonarchimedean local field `F`,
let `q : G → A` be an actual adjoint quotient by the full scheme center.
For every algebraically bounded subset `B ⊆ A(F)`, the set

`q(F)⁻¹(B) ∩ rationalCommonNormKernel G`

is algebraically bounded in `G(F)`. The kernel here is the common kernel of
the norms of all actual `F`-rational characters of `G`. The subset `B` need
not be a subgroup, closed, or contained in the image of `q(F)`. No
surjectivity of the map on rational points is assumed.

This is an internal central-direction boundedness statement, motivated by
the reduction at the beginning of the proof of KP Proposition 2.2.16,
printed p. 77, PDF p. 108. The source reduces to a semisimple quotient by
the central torus using a finite isogeny and the bounded norm kernel of a
torus. The present formulation uses the quotient by the full scheme
center. A proposed proof combines `q` with the torus quotient by the
derived group. The joint map has finite kernel and is finite onto its
closed image. Its two components are bounded on the displayed set:
the first by `B`, the second by the torus norm-kernel theorem. Finite-map
pullback then gives the desired bound. Constructing these quotients and
establishing the asserted finiteness are retained proof obligations.

The source is Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
This formulation is derived for the current proof route; it is not
presented as a separately numbered assertion of the book.
