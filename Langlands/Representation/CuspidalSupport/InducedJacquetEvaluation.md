# Evaluation at the identity and the normalized Jacquet module

Author: Worker 241.

This module proves the easy direction of Frobenius reciprocity for normalized
parabolic induction on `GL_n` over a p-adic field, in the only form needed by
the two-block cuspidal-induction argument: a nonzero intertwiner
`f : X → i_P^G(σ)` gives a nonzero intertwiner `r_P(X) → σ` out of the
normalized Jacquet module. The closed result is
`Langlands.CuspidalSupport.exists_ne_zero_normalizedJacquet_hom`.

Here `T.normalizedParabolicInduced B σ` is the Library's normalized induction
(`Langlands.Representation.Induction.Parabolic`) and `T.normalizedJacquet B X`
is the Library's normalized Jacquet module
(`Langlands.Representation.Jacquet.Parabolic`), both using the explicit block
modulus of `Langlands.Group.GL.BlockModulus`. No statement from the literature
beyond these definitions is used; the module proves only the stated Lean
theorems and makes no claim about the converse direction of reciprocity or
about bijectivity of the correspondence `f ↦ jacquetEvaluation T B f`.

## Evaluation at the identity

`inducedEvaluation T B f : V →ₗ[ℂ] W` sends `v` to the value `f(v)(1)` of the
induced function `f v` at the identity. Linearity is linearity of `f` followed
by evaluation of the underlying functions.

- `inducedEvaluation_translate`: `f(X(g) v)(1) = f(v)(g)`. Since `f` is an
  intertwiner, `f(X(g) v)` is the right translate of `f v` by `g`, whose value
  at `1` is the value of `f v` at `1 * g = g`.
- `inducedEvaluation_parabolic`: for `q` in the standard parabolic with Levi
  part `m`, `f(X(q) v)(1) = δ_P(m)^(1/2) σ(m) f(v)(1)`. This is the
  translation formula above together with the published covariance
  `normalizedParabolicInduced_covariant` at the point `q * 1`.
- `inducedEvaluation_unipotent`: elements of the unipotent radical have Levi
  part `1`, so they act trivially after evaluation.
- `inducedEvaluation_levi`: a block-diagonal element `m` of the Levi acts by
  `T.leviHalfModulus B m • σ(m)` after evaluation. It is the parabolic case for
  the section `leviInParabolic`, using `BlockShape.leviInParabolic_val`,
  `BlockShape.leviProjection_section` and `leviHalfModulus_apply`.

## Descent to the Jacquet module

`jacquetEvaluation T B f : (T.normalizedJacquet B X).IntertwiningMap σ` is the
descent of `inducedEvaluation T B f` to the unipotent coinvariants by
`Jacquet.lift`; the invariance hypothesis is `inducedEvaluation_unipotent`.
For equivariance it suffices, by `Representation.Coinvariants.hom_ext`, to
check classes `B.jacquetMk X v`. The published
`normalizedJacquet_mk_eq_inv_halfModulus` writes the normalized action of `m`
on such a class as `δ_P(m)^(-1/2)` times the class of `X(m) v`;
`inducedEvaluation_levi` contributes the factor `δ_P(m)^(1/2) σ(m)`, and the
two half-modulus factors cancel in `ℂˣ`. The simp lemma `jacquetEvaluation_mk`
states that the descended map sends the class of `v` to `f(v)(1)`
(definitionally).

## Nonvanishing

`jacquetEvaluation_ne_zero`: if `jacquetEvaluation T B f = 0`, then for every
`v` and every `g`, `f(v)(g) = f(X(g) v)(1)` is the value of the descended map
on the class of `X(g) v`, hence `0`. So every induced function `f v` vanishes,
which gives `f = 0` by extensionality of intertwiners, subtypes and functions.
`exists_ne_zero_normalizedJacquet_hom` packages this as an existence statement.
