# Uniform source-carrier length bound for unequal-rank Whittaker-type data

This module defines the Prop-valued target
`Langlands.RankinSelberg.UnequalRankSourceLengthBoundStatement.{uF,uV,uW}`.
It is an **internal intermediate statement**, not a transcription of an
original-source theorem. Defining it proves nothing: the length bound,
the irreducible Lemma and Proposition of JPSS §2.11 (printed p.399), and
the full parent theorem `UnequalRankBilinearUniquenessStatement` all
remain proof obligations.

## Data and quantifier order

The arguments are `{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p`, an
arbitrary supplied `T : F.TopologicalData`, and `n r : ℕ`. Only
`T.topology` is installed locally. The statement uses
`q = T.residueCardinality` and the absolute value
`normalizedAbsoluteValue T`, both computed from the given `T`, which is
not identified with canonical topological data.

The proposition is

```text
∀ (hnr : n < r) (ψ : UnitaryAdditiveCharacter F.Carrier)
  (V : Type uV) [AddCommGroup V] [Module ℂ V]
  (W : Type uW) [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (GeneralLinear (r+1) F.Carrier) V)
  (σ : Representation ℂ (GeneralLinear (n+1) F.Carrier) W),
  IsOfWhittakerType r (standardCharacter ψ r) π →
  IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
  ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint q s ∉ E →
    Module.length ℂ
      (unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T)
        (π.comp (GeneralLinear.mirabolic r F.Carrier).subtype) σ s) ≤ 1.
```

The field universe `uF` and the two carrier universes `uV` and `uW` are
independent. All natural ranks with `n < r` are included, in particular
`n = 0` and adjacent ranks `r = n+1`, where the unipotent covariance group
is trivial. The carriers may be zero modules whenever the hypotheses
permit it.

The exceptional set `E` is chosen after `hnr`, the character `ψ`, both
carriers, both representations and both hypotheses, and before the
parameter `s` and every bilinear form. Its elements are values of
`spectralPoint q s = (q : ℂ)^(-s)`, not exponents `s`. No Whittaker
functional is quantified, so in particular `E` does not depend on any
specified coefficient model.

## The form space

`unequalRankMirabolicForms` is the published
`Submodule ℂ (V →ₗ[ℂ] W →ₗ[ℂ] ℂ)` of
`Langlands.Representation.RankinSelberg.UnequalRankBilinearForms`; no new
form space is introduced. Its forms live on the **original carriers** `V`
and `W`, not on coefficient images. The first representation is restricted
to the mirabolic subgroup only through the actual inclusion
`(GeneralLinear.mirabolic r F.Carrier).subtype`; the second representation
`σ` remains a representation of the full `GL_(n+1)`.

Membership is the published `IsUnequalRankMirabolicCovariant`, the
conjunction of the two actual laws:

- for every `g : GL_(n+1)`, acting on `V` through
  `unequalRankEmbedding hnr g = diag(g, I_(r-n))`,
  `B (π(diag(g, I)) v) (σ(g) w) = determinantWeight abv g ((r-n)/2 - s) * B v w`,
  so the determinant exponent is `(r-n)/2 - s`;
- for every `u` in the actual group `U_(n+2,r+1)`, given by the published
  predicate `IsUnequalRankCovarianceUnipotent n u` and acting through
  `unequalRankUnipotentLift`,
  `B (π(u) v) w = standardCharacter ψ r u * B v w`.

For a complex vector space, Mathlib's `Module.length_eq_rank` identifies
`Module.length` with the rank as an extended natural number. The bound
`≤ 1` therefore says that the covariant forms span a space of dimension at
most one, which may be zero.

## Hypotheses

The only representation hypotheses are the two published
`IsOfWhittakerType` propositions: admissibility, finite generation over
the complex group algebra, and a one-dimensional space of functionals for
the standard character on `π` and for the inverse standard character on
`σ`. Reducible representations are allowed. There is no irreducibility,
finite-length, central-character, generic pair-control,
mirabolic-structure, source-pairing or uniqueness premise; the eventual
proof must derive every structural input it needs from these two
hypotheses.

## Provenance and role

This is a strengthening, chosen for the existing full Whittaker-type
target `UnequalRankBilinearUniquenessStatement`, of the statement needed
immediately before coefficient-model descent. The covariance laws are
those of JPSS (2.11.2) and (2.11.4), as recorded in the Markdown of the
published form-space module, including the parameter convention: the
source's twisted-pairing parameter on p.399 is `s - (r-n)/2`.

A source-carrier bound descends to every specified pair of coefficient
models. The two actual `Whittaker.modelMap` intertwiners are surjective
onto the coefficient images, so pulling a model form back along them is
injective and preserves both covariance laws. Hence model forms embed
into the source-carrier space, and a dimension bound there gives scalar
proportionality on the models. This descent is already proved in the
published theorem
`Langlands.RankinSelberg.UnequalRankAssembly.unequalRankBilinearUniqueness_of_source_length`,
whose explicit hypothesis is exactly this proposition: a private
development check confirmed that the theorem applied to
`UnequalRankSourceLengthBoundStatement.{uF,uV,uW} F T n r` has type
`UnequalRankBilinearUniquenessStatement.{uF,uV,uW} F T n r`. Since `E` is
chosen before any functional, the source bound is stronger than what the
parent needs, whose exceptional set may depend on the specified
functionals.

The printed JPSS Lemma and Proposition on p.399 concern irreducible data:
a smooth irreducible mirabolic representation, or irreducible generic
representations. They do not directly give this bound for reducible
Whittaker-type data. The later proof is therefore expected to use a
finite-length and functional-factor argument: a finite filtration of the
mirabolic restriction of `π` and a finite composition series of `σ`,
pairwise control of the constituent pairs outside finitely many spectral
values, and the one-dimensional total Whittaker-functional spaces to show
that at most one constituent pair contributes. These ingredients are
neither assumed nor proved here. No original-source quotation is needed
for this internal statement; for the source correspondence of the
covariance itself, see the Markdown of `UnequalRankBilinearForms` and
`UnequalRankBilinearUniquenessStatement`.
