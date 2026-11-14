# Actual Lie-image weights of represented dynamic parabolics

The construction `dynamicParabolicLieWeights i ν` is the actual nonzero
differential-image support of the canonical closed representative
`Dynamic.Affine.parabolicHom` of the dynamic parabolic associated with `ν`.
It uses the existing `nonzeroLieImageWeights` construction on this actual
group-scheme inclusion, rather than defining the support by a root-sign formula.

This internal supporting result computes the existing
`nonzeroLieImageWeights i j` for an actual monomorphic representative `j` of a
dynamic parabolic associated with a cocharacter of the fixed split torus `S`.
Over any field, for an affine ambient group locally of finite type, the result is
the set of actual relative roots with nonnegative integral pairing with that
cocharacter. It is uniform in universe `u`.

The first lemma identifies the existing differential-image definition with the
nonzero part of the intrinsic conjugation-action weight support. The proof uses
`hasLieImage_of_isRepresentedBy`: monicity ensures that points lifting an
identity-kernel point also lie in the identity kernel. The actual differential
image therefore equals the intrinsic tangent submodule of the represented
subgroup functor. The published equality of conjugation-action and adjoint
weight spaces gives the identification.

For the dynamic parabolic, the published tangent computation identifies this
submodule with the span of all nonnegative cocharacter weight spaces. The
published semigroup-support theorem says exactly which ambient weight spaces
meet this span nontrivially: selected weight spaces are contained in it, and
unselected weight spaces are disjoint from it by independence of split-torus
weights. Removing the zero character leaves exactly the actual relative roots
with nonnegative pairing. This computation requires neither smoothness nor
connectedness.

The formula theorem applies this computation to the canonical representative,
using its published all-test representability theorem. Every monomorphic
representative of the same dynamic parabolic has the same canonical support,
as follows by applying the formula to each representative.

For a smooth connected affine ambient group, the two final lemmas identify
inclusion and equality of any two such represented parabolics with inclusion and
equality of these concrete Lie-image supports. They apply the published
root-sign inclusion criterion with the proved `dynamicConnected` theorem, then
use the weight computation; equality follows by antisymmetry. All subgroup
comparisons are on every test scheme. No inference from rational points is used.

These results are derived from the existing tangent, split-torus weight,
dynamic Lie algebra and dynamic connectedness theorems. They do not assert that
an image of a facet model is a dynamic parabolic, nor supply a torus or a
cocharacter for such an image. Those geometric identifications, and the
unramified facet parabolic bijection of Task 6318, remain separate obligations.
