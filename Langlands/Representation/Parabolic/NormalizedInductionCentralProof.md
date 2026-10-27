# Scalar central action on normalized parabolic induction

Author: Worker 257.

`Langlands.Parabolic.normalizedInductionCentralClause` proves the published
proposition `Langlands.Parabolic.NormalizedInductionCentralClause.{uF,uV} F T B V`
from `Parabolic.NormalizedCompatibilityStatement`. It keeps all the
statement's parameters: every prime `p`, actual field `F : PadicField.{uF} p`,
supplied topology `T`, rank `n` (including zero), ordered block shape `B`, and
complex carrier `V : Type uV`. The two universes are independent. For every
product-Levi representation `sigma` and every group homomorphism
`omega : F units -> Complex units`, the hypothesis

`sigma((a I_(n_i))_i) v = omega(a) v` for all `a` and `v`

gives `normalizedInd(sigma)(a I_n) f = omega(a) f` for every function `f` in
the actual smooth induced space. The proof adds no hypothesis on `sigma` or
`omega`: no smoothness, admissibility, irreducibility, unitarity, open kernel,
finite dimension, or tensor factorization.

## Generic central-action lemma

`Induction.smoothInduced_central_apply` applies to any topological group `G`,
subgroup `P`, coefficient ring `R` and representation `sigma` of `P`. Let `z`
be an element of `P` that commutes in `G` with every `g`, and suppose `sigma(z)`
is multiplication by a scalar `c`. Then `smoothInduced P sigma z` is
multiplication by `c`. The induced action is right translation, so
`(z . f)(x) = f(x z)`. Since `x z = z x`, this equals `f(z x)`. The covariance
field of `f` gives `f(z x) = sigma(z) f(x)`, which is `c f(x)`. The proof
compares the underlying functions pointwise. It does not use smoothness of
`f` or of `sigma`.

## The ambient scalar in the block parabolic

These four results concern `GeneralLinear.BlockShape`.

- `index_ne_of_ne`: coordinates in different blocks have different standard
  indices. This holds because `B.indexEquiv` is injective.
- `scalar_mem_parabolic`: the scalar matrix `a I_n` lies in `B.parabolic R`.
  The published `mem_parabolic_iff` requires the block entries strictly below
  the diagonal blocks to vanish. These entries lie off the diagonal by the
  previous lemma, so the diagonal matrix `a I_n` has zero there.
- `ambientScalar`: the homomorphism `R units -> B.parabolic R`, `a ↦ a I_n`,
  formed by restricting the codomain of `GeneralLinear.scalar`.
  `coe_ambientScalar` records that its value in `GL_n(R)` is the scalar matrix
  itself (by `rfl`).
- `leviProjection_ambientScalar`: the published Levi projection of `a I_n` is
  the tuple `(a I_(n_i))_i`. The `i`th block of a matrix is its entry at the
  indices `B.index i x` and `B.index i y`. For a scalar matrix this is `a`
  when `x = y` and `0` otherwise, because `B.index i` is injective.

## Half modulus on ambient scalars

`PadicField.TopologicalData.parabolicHalfModulus_ambientScalar` proves
`T.parabolicHalfModulus B (a I_n) = 1`. By `parabolicHalfModulus_apply` the
half modulus is the Levi half modulus of the Levi projection. The previous
lemma rewrites that projection to `(a I_(n_i))_i`. The published
`T.leviModulus_scalar` makes the explicit block modulus equal to one there.
The published `T.leviHalfModulus_eq_one` then shows that its positive square
root is one.

## Assembly

The main theorem installs the topology `T.topology` and the topological-group
structure `T.generalLinearTopologicalGroup n`, as the statement does. The
representation in the clause is smooth induction from `B.parabolic F` of
`twist (T.parabolicHalfModulus B) (inflate B sigma)`. The proof applies the
generic lemma with `z = ambientScalar a` and `c = omega(a)`. Centrality is
Mathlib's `Matrix.GeneralLinearGroup.scalar_commute`. On the inducing side,
the twisted inflated action of `z` is, by definition, the half modulus of `z`
times `sigma` of the Levi projection of `z`. The two rewrites above reduce it
to `1 * sigma((a I_(n_i))_i) v`, and the hypothesis on `sigma` gives
`omega(a) v`.

## Scope and provenance

This is the direct derivation given in the statement Markdown. The scalar
matrix is central, and the left covariance of an induced function turns right
translation by it into the inducing action. The block half modulus is one on
ambient scalars. The definitions of normalized induction follow
Bernstein--Zelevinsky (1977), Sections 1.8 and 2.1--2.3 (registered original
`bernstein-zelevinsky-1977-induced-i`). The proof follows the Lean
construction and cites no further source claim.

The module imports only the statement module. It proves only this clause of
`NormalizedCompatibilityStatement`; the other four clauses remain separate
obligations. It does not construct a smooth character on the ambient center
from a Levi-center character. It makes no analytic, admissibility or
temperedness assertion.
