# Unequal-rank bilinear uniqueness for Whittaker-type coefficient models

This module defines the Prop-valued target
`Langlands.RankinSelberg.UnequalRankBilinearUniquenessStatement.{uF,uV,uW}`,
the fixed-data predicate `Langlands.RankinSelberg.IsUnequalRankBilinearCovariant`,
and the membership predicate
`Langlands.RankinSelberg.IsUnequalRankCovarianceUnipotent`.

The full Whittaker-type target is an **internal extension** of the
irreducible generic Proposition in JPSS §2.11, printed p.399. It is
required by the intended uniqueness route to the full Whittaker-type
scope of Theorem 2.7, not a literal restatement of that Proposition.
Establishing this extension is a separate proof obligation. Defining
these propositions proves neither uniqueness nor existence of a gamma
factor or functional equation.

## Fixed data and actual covariance

For a field `F : Type uF` with a topology and integers `n < r`, write
`R = r+1` and `t = n+1`. These are the large and small ranks, respectively.
Let `ψ : UnitaryAdditiveCharacter F`, `abv : AbsoluteValue F ℝ`,
`π : Representation ℂ (GeneralLinear (r+1) F) V`, and
`σ : Representation ℂ (GeneralLinear (n+1) F) W`. The complex module
carriers `V : Type uV` and `W : Type uW` have independent universes.
For specified functionals

```text
ℓ  : glFunctionals ψ r π
ℓ' : glInverseFunctionals ψ n σ,
```

the spaces are the actual coefficient images

```text
M  = (coefficientModel π ℓ).toSubmodule
M' = (coefficientModel σ ℓ').toSubmodule.
```

Their actions are `modelRepresentation π ℓ` and
`modelRepresentation σ ℓ'`, acting by right translation on functions.
A bilinear form is the curried linear map
`B : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ`.

The embedding used in the covariance is the expression

```text
ι(g) = GeneralLinear.reindex
         (finCongr (show n + (r-n) + 1 = r+1 by omega))
         (appendIdentity n (r-n) g).
```

The existing `appendIdentity_entry` verifies that `appendIdentity`
is exactly `diag(g,I_(r-n))`. The reindexing identifies equal
natural-number dimensions and preserves the order of the coordinates.
There is no supplied embedding or new matrix construction.

`IsUnequalRankCovarianceUnipotent n u`, for
`u : upperUnipotent (r+1) F`, requires

```text
∀ i j : Fin (r+1), i.val < n+2 → j.val < n+2 →
  u.val i j = if i = j then 1 else 0.
```

Thus it describes the actual subgroup `U_(t+1,R) = U_(n+2,r+1)`:
upper-unitriangular matrices whose leading `(n+2)`-square block
is the identity. In block notation its matrices are
`[[I_(n+2), X], [0, u₁]]`, with arbitrary top-right block `X`
and upper-unitriangular lower-right block `u₁`. This is (2.11.3)
with its first block size replaced by `t+1`, as required in
(2.11.4). When `n+2 = r+1`, every entry is fixed to the identity
matrix, so this subgroup is trivial. The module states membership
as a short proposition inside the existing unipotent group; it
does not introduce a separate abstract subgroup parameter.

`IsUnequalRankBilinearCovariant hnr ψ abv π σ ℓ ℓ' s B` is the
conjunction of the following two laws, for all indicated vectors:

```text
B (modelRepresentation π ℓ (ι g) f)
  (modelRepresentation σ ℓ' g f')
  = determinantWeight abv g (((r-n : ℕ) : ℂ)/2 - s) * B f f'
```

for every `g : GeneralLinear (n+1) F`, and

```text
B (modelRepresentation π ℓ u.val f) f'
  = (standardCharacter ψ r u : ℂ) * B f f'
```

for every `u : upperUnipotent (r+1) F` satisfying the membership
predicate. The character is the existing standard character, the
value of `ψ` on the first-superdiagonal sum; it is not a supplied
character of an unspecified group. The inverse standard character
is used for the second coefficient model. Because `ψ` is unitary,
the inverse agrees with the source's conjugate character.

## Universal uniqueness target

The arguments of `UnequalRankBilinearUniquenessStatement` are
`{p : ℕ} [Fact p.Prime]`, `F : PadicField.{uF} p`,
`T : F.TopologicalData`, and `n r : ℕ`. Only `T.topology` is
installed locally. The statement uses `q = T.residueCardinality`
and `abv = normalizedAbsoluteValue T`, without identifying `T`
with canonical topological data.

For every `hnr : n < r`, every `ψ`, every pair of independent
complex module carriers, and every `π, σ` as above, the hypotheses are

```text
IsOfWhittakerType r (standardCharacter ψ r) π
IsOfWhittakerType n (inverseStandardCharacter ψ n) σ.
```

The existing Whittaker-type predicate means admissibility, finite
generation over the complex group algebra, and a linear equivalence
of the specified functional space with `ℂ`. Admissibility includes
smoothness. This permits reducible representations and does not
assert that the representation space is finite dimensional.

For every specified `ℓ, ℓ'`, the conclusion is

```text
∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint q s ∉ E →
  ∀ B B' : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ,
    IsUnequalRankBilinearCovariant hnr ψ abv π σ ℓ ℓ' s B →
    IsUnequalRankBilinearCovariant hnr ψ abv π σ ℓ ℓ' s B' →
    B ≠ 0 → ∃ c : ℂ, B' = c • B.
```

The exceptional set is chosen after the character, representations,
and functionals, but before `s`, `B`, and `B'`. The exceptions
are values of `q^(-s)`, since `spectralPoint q s = (q : ℂ)^(-s)`;
they are not a finite set of exponents. The conclusion expresses
dimension at most one, allowing the space of covariant forms to
be zero. Functionals need not be nonzero: if either is zero,
its coefficient image is zero and the premise `B ≠ 0` is impossible.

There is no additional irreducibility, central-character,
finite-length, rational-continuation, or analytic hypothesis.
No uniqueness assertion or auxiliary unproved representation
theorem is inserted as a premise. The finite exceptional set in
the conclusion is the only generic-spectral-value restriction.

## Source correspondence and parameter shift

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics
**105** (1983), 367–464, Theorem 2.7, printed pp.390–391,
and §2.11, printed pp.398–403. Registered source:
`jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.398–403 (PDF pages 33–38) were read completely,
as were pp.390–391 (PDF pages 25–26). No registered erratum note
was found in the checked project and Library note/wiki locations.

The printed large rank `r` and small rank `t` are respectively
`R = r+1` and `t = n+1` in the Lean indexing. Equation (2.11.1)
has weight `|det g|^(s-(R-t)/2)`. Its simultaneous right-translation
covariance (2.11.2) has the negative of that exponent,
`(R-t)/2-s = (r-n)/2-s`, exactly as in the fixed-data predicate.
Equation (2.11.4) imposes the standard-character condition on
`U_(t+1,R)`, not on the larger `U_(t,R)`.

The p.399 Proposition instead uses the convention
`Bil_(G_t)(π ⊗ α^λ, σ)`, with `α(g) = |det g|`.
Invariance of this twisted pairing means that the untwisted
pairing transforms by `|det g|^(-λ)`. Thus its parameter, printed
again as `s` in the Proposition, corresponds to
`λ = s-(R-t)/2` for the integral parameter used here.
The exceptional spectral parameters transform by
`q^(-λ) = q^((R-t)/2) q^(-s)`, so the fixed nonzero rescaling
preserves finiteness. Further shifts in the induction, such as
`s+R-t` in (2.11.18), belong to that proof and are not extra
twists or assumptions in the present covariance.

The Proposition assumes that both representations are irreducible
and generic. Its lemma assumes a smooth irreducible mirabolic
representation and an irreducible admissible representation of
the smaller general linear group, distinguishing the generic
case. These are narrower hypotheses than Theorem 2.7's
Whittaker-type scope. The present formulation explicitly requests
the extension to the actual coefficient images of all
Whittaker-type representations; the printed Proposition alone
is not a proof of that extension.

The source proof reduces through finite composition series of
mirabolic restrictions and uses (1.2), (1.4), and related
mirabolic results. On pp.400–403 it represents the forms by
distributions, analyzes their support in several cases, excludes
some constituents at finitely many spectral values, and closes
the final case by Whittaker uniqueness. These are source-proof
context and possible future proof obligations, not facts proved
or assumed by this module. The source allows arbitrary
non-Archimedean local fields; this target has the requested
`PadicField` scope. Bilinearity and covariance of continued
integrals, and the rational-ratio construction of gamma factors,
remain separate tasks.
