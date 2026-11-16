# The actual projective linear action on Deligne isomorphism classes

The existing valuation-normalized general linear action descends to
Mathlib's actual projective linear group. The carrier remains the genuine
isomorphism classes of admissible Deligne four data. This construction
uses the proved triviality of every scalar, with no scalar-triviality
premise or change of the equivalence relation.

The source motivation is V. G. Drinfel'd, *Coverings of p-adic symmetric
regions* (1976), Section 2 A, printed pp.109–110 (PDF pp.3–4). The theorem
on p.109 specifies the projective action on Deligne's factor; the following
point description gives the graded four data and determinant normalization.
The registered source is `drinfeld-1976-coverings-p-adic-symmetric-regions`,
SHA256 `7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The quotient construction and its action laws here are derived
infrastructure for that action on the existing point model. They do not
assert the representability theorem or its compatibility with formal modules.

## Matrices and frame automorphisms

For any field `F` and any natural number `d`, `matrixReframeEquiv d F`
is the multiplicative equivalence from actual invertible `d` by `d`
matrices to linear automorphisms of `Fin d → F`. It composes Mathlib's
matrix-to-linear general linear equivalence with its equivalence from
linear-map units to linear equivalences. In particular, matrix products
have the same order as composition of frame automorphisms.

`matrixReframeEquiv_scalar` proves that the actual scalar matrix of
`a : Fˣ` gives `scalarReframeHom d F a`, the published scalar linear
automorphism. Its proof evaluates the diagonal matrix on a vector.
These two declarations also apply when `d = 0`.

## The descended right operation

For the remaining declarations, all coefficient carriers and schemes
have common universe `u`. Assume `O` is a commutative domain and a DVR,
`F` is its fraction field, `NeZero d`, `hpi : Irreducible pi`, a scheme
`S`, and a ring map `phi : O → Γ(S, top)`. The class type is the existing
`SheafDatum.IsoClass` with the nonzero field image of `pi` proved from
these hypotheses. Nilpotence is unnecessary for this algebraic action
on the existing admissible-class model.

Write `R_g(q)` for `normalizedReframe hpi g q`. It precomposes the frame
by `g` and shifts the degree by `-coefficientOrder(det g)`. Its published
laws give

```text
R_1(q) = q,
R_h(R_g(q)) = R_(g*h)(q).
```

Consequently `normalizedReframePermHom` is a monoid homomorphism from
linear frame automorphisms to the opposite of the permutation group of
these actual classes. The opposite group records this right-action order.
Each permutation and its inverse are those already constructed in
`DeligneValuedReframe`.

The selected definition `projectiveReframeHom` is a monoid homomorphism
from `Matrix.ProjGenLinGroup (Fin d) F` to those opposite permutations.
This is Mathlib's `GL / center`, with center equal to the range of the
actual scalar-matrix homomorphism. We compose the preceding homomorphism
with `matrixReframeEquiv` and use `Matrix.ProjGenLinGroup.lift`.
The lift's scalar condition follows from `matrixReframeEquiv_scalar`
and the published theorem `normalizedReframe_scalar`, applied to every
actual admissible class. No representative choices or extra quotient
relations are introduced.

`projectiveReframe hpi g q` evaluates the resulting permutation. The
representative formula `projectiveReframe_mk` identifies its value at
the projective class of a matrix `g` with
`normalizedReframe hpi (matrixReframeEquiv d F g) q`. The module proves
the identity, right product, and both inverse cancellation laws.
`projectiveReframeEquiv` exposes the resulting actual permutation.

## Action structures and the inverse convention

`projectiveReframeRightAction` supplies a `MulAction` of the opposite
projective group, with `op(g) • q = projectiveReframe hpi g q`.
`projectiveLeftAction` supplies the associated ordinary left action of
`PGL(d,F)`, with

```text
g • q = projectiveReframe hpi g^(-1) q.
```

The identity and multiplication laws are proved from the preceding right
product law and the inverse-of-product identity. These are explicit
instance-reducible action definitions; a caller installs the desired
one locally, supplying `hpi` and the coefficient field. The theorem
`projectiveLeftAction_mk_smul` includes this local instance and proves
that the class of a matrix `g` acts by the normalized reframe of `g⁻¹`.
Thus the ordinary left convention has correcting shift
`+coefficientOrder(det g)`. The inverse in this formula is explicit.

## Remaining scope

This module constructs projective actions on each scheme's existing
admissible-class set. Naturality under arbitrary base change, hence the
action on the complete Nilp functor, is a subsequent obligation.
Uniformizer independence, comparison of the admissibility predicate
with an independent exterior-subsheaf formulation, the comparison with
special formal modules, representability, and the Harris tower theorem
boundaries remain separate work. No representing or universal object
is input or output here.
