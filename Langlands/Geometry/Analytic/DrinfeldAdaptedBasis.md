# Adapted bases for ultrametric vector norms

For a finite family `b` and a `VectorNorm ν`, `IsOrthogonalFamily ν b` says
that each term of a linear combination has norm at most the norm of the
whole combination. The reverse bound by the maximum follows from the
ultrametric inequality. `IsAdaptedBasis ν b` asks for that condition on an
actual `Module.Basis`. In the coordinate representation of a vector `a`,
`IsAdaptedBasis.apply_eq_iSup` gives

`ν(a) = supᵢ ‖b.repr a i‖ · ν(b i)`.

For a nonempty finite index type this supremum is a maximum. The module
also gives the equivalent inequality against a nonnegative bound `C` by
bounding all the weighted coordinates by `C`.

## Existence and implemented proof

Over a proper nontrivially normed field, `exists_isAdaptedBasis` constructs
an adapted basis in finite dimension, with index type `Fin (finrank k E)`.
In positive dimension, `exists_isAdaptedBasis_with_first` can prescribe any
nonzero vector as the basis vector at index zero. The statements use the
Library's `VectorNorm`, so no norm, metric or topological instance on the
vector space is assumed.

In the closest-point lemma the proof temporarily equips the vector space
with the given norm and applies `FiniteDimensional.proper`. Subspaces are
closed; a closest point `w` of a subspace `W` to a vector `x` exists. If `x`
is outside `W`, write `y = x − w`. Minimality implies `ν(y) ≤ ν(u+y)` for
all `u ∈ W`. When `ν(u) ≤ ν(y)` this is the reverse of the ultrametric
upper bound, and when `ν(y) < ν(u)` the larger term dominates. In either
case `ν(u+y) = max(ν u, ν y)`. Scalar homogeneity extends this equality to
`ν(u+t • y) = max(ν u, ν(t • y))` for any `t`.

Starting with the prescribed nonzero vector, the proof uses the orthogonal
line construction to append to a finite orthogonal family while its span
is proper. The lower bound on each term in a sum shows that an orthogonal
family of nonzero vectors is linearly independent. Once its length is the
dimension, it is a basis. In dimension zero the coordinate condition is
vacuous.

## Source and scope

Rémy–Thuillier–Werner, *Bruhat-Tits buildings and analytic geometry*
(arXiv:1110.1362, 2012), Definition 1.18(i) and Proposition 1.20,
pp. 12–13, registered as
`remy-thuillier-werner-2012-bruhat-tits-analytic-geometry`, SHA-256
`f176a2657963c2e6da49a2e0282353097fff8ad67b7cf17f51c2372325591d0b`.
Their adaptedness says that the norm is a maximum of the coefficient norms
times positive weights. Evaluating on the basis vectors identifies the
weights with the vector norms used here. Their proof diagonalizes by
splitting off a line chosen by maximizing a functional-to-norm ratio on
projective space. The subspace proof above is a derived variant and also
proves the prescribed-first-vector extension. This is single-norm
adaptedness, not simultaneous diagonalization of arbitrary pairs of norms.

For the surjectivity input to `DrinfeldCoveringStatement`, the prescribed
vector can be the coefficient vector of the constant form, so adapted
coordinates still use the same affine chart. No analytic lift is constructed
in this module.
