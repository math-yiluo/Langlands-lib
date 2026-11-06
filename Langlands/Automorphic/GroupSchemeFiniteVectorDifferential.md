# Actual differential covariance and whole-function finite vectors

This internal construction keeps the original smooth atlas, actual identity
tangent space, finite plot-smooth rational functions, and positive right action
`R(g)f(x) = f(x*g)`. The field is an arbitrary number field, the group scheme
is affine, and the supplied smooth relative dimension is explicit. The infinite
subgroup may be any subgroup: compactness or maximality is not needed for this
preservation result.

`adelicTangentConjugation` differentiates actual inner conjugation
`h ↦ g*h*g⁻¹` at the identity. The covariance identity
`R(g) D_X f = D_(dConj(g)X) R(g)f` follows from
`groupDirectionalValue_rightTranslation` on every original finite slice.
Joint slice evaluation is injective, so this proves an identity of entire
adelic functions. No covariance premise is added.

`actualAdelicComplexDifferential` is the linear map underlying the existing
actual complex tangent Lie action, with the scalar commutator already proved
by `adelicDifferentialCommutator_of_smooth`. A pure tensor `z ⊗ X` acts as
`z` times the original real directional derivative. Its parameter space is
finite dimensional: the infinite places and coordinate directions are finite,
and each actual completion is finite dimensional over the reals. The chosen
completion scalar structures are exactly those of the original atlas.

For a whole-function finite vector `f`, the public internal lemma
`Langlands.FiniteVectors.isFiniteVector_bilinear_of_covariance` places the
translated values of `D_X f` in the image of the tensor product of the finite
complex tangent space with the original finite orbit span of `f`. That image
is finite dimensional. This proves preservation under real derivatives;
linearity and tensor induction give complex tangent preservation. The
original universal enveloping action sends a generator to this same complex
differential. Lifting an enveloping element to the tensor algebra and
inducting over scalars, generators, multiplication and addition proves
preservation under every enveloping element. The ring congruence in this
argument uses the actual `GroupLieAlgebra` bracket.

`adelicInfiniteFiniteEnvelopingAction` restricts the original actual
complex enveloping algebra homomorphism to `adelicInfiniteFiniteSubmodule`.
Its displayed value theorem is reflexive: forgetting subspace membership
returns the original function and original action. All algebra homomorphism
laws are inherited through that injective inclusion.

The construction and finite-dimensional image argument are internal
manifold-calculus and representation infrastructure, derived from the named
public constructions and proved covariance helper. This unit does not infer
global algebraic tensor rank from finite orbit dimension, does not prove
automatic uniform growth, and does not yet restrict to the full automorphic
or cuspidal form spaces. It identifies no algebraic determinant with a Haar
modulus.
