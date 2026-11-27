# Multiplicity one for the cuspidal spectrum of `GL_n`

`Langlands.Automorphic.GroupSchemeFunctions.generalLinearCuspidalMultiplicityOne`
proves `GeneralLinearCuspidalMultiplicityOneStatement.{u}`. For a number field
and the central split torus data in the statement, the space is the full
almost-everywhere cuspidal subspace of `L²` on the positive-central rational
quotient of `GL_n`. The data include injective character restriction with
finite-index image, the parabolic dynamic hypothesis, and right invariance
of Haar measure on the norm-one subgroup. Two irreducible closed invariant
subspaces coincide whenever a complex-linear isometric equivalence between
them intertwines the adelic right actions.

The proof applies `generalLinearCuspidalMultiplicityOne_of_summandEquivalence`.
In positive rank, `generalLinearCuspidalSummandRealizationFromDensity` uses
`generalLinearSummandFormsDense` to realize each summand as the closure of the
`L²` classes of its cusp forms. `generalLinearCuspidalSummandEquivalence`
carries the Hilbert-space intertwiner to an equivalence of the realizations
that commutes with finite adelic translations, archimedean compact
translations and the complex enveloping algebra action.
`Langlands.Automorphic.cuspidalOperatorMultiplicityOne` then gives equality of
the underlying operator realizations. Each form determines a unique `L²`
class on the quotient by injectivity of pullback along the quotient map and
almost-everywhere equality. The two class images and their closures therefore
coincide. In rank zero the quotient has at most one point, so its `L²` space
has dimension at most one. Any two nonzero subspaces of the cuspidal
subspace then coincide.

Getz–Hahn compare the two embeddings by evaluating Whittaker functions at the
identity and then using Whittaker expansion to recover the forms. In Lean,
local Whittaker uniqueness, the scalar comparison and reconstruction enter
through `cuspidalOperatorMultiplicityOne`. The passage from Hilbert summands
to their spaces of forms implements the comparison in Getz–Hahn, Theorems
6.6.4 and 9.7.3.

## Sources

- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*,
  GTM 300, Springer, 2024. Theorem 11.4.3 and its proof, p. 303 (PDF p. 314).
  Theorems 6.6.4 and 9.7.3, p. 172 (PDF p. 186) and pp. 265–267
  (PDF pp. 277–279). Registered as `getz-hahn-2024-automorphic-representations`,
  SHA-256 `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
- J. A. Shalika, *The multiplicity one theorem for GL_n*, Ann. of Math. 100
  (1974), 171–193. Theorem 5.5, p. 187 (PDF p. 18), gives multiplicity one
  with a fixed unitary central character. Registered as
  `shalika-1974-multiplicity-one`, SHA-256
  `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
