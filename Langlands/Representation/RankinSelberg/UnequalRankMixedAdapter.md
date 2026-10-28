# Unequal-rank mirabolic covariance as mixed covariance tests

This module is an **internal adapter** between two published constructions. It
rewrites the unequal-rank mirabolic-versus-general-linear covariance of
`Langlands.Representation.RankinSelberg.UnequalRankBilinearForms` as one test
family for the general mixed covariance spaces of
`Langlands.Representation.Filtration.MixedBilinear`. It proves that the two
form spaces agree as actual submodules. Both modules are imported and left
unchanged. All declarations live in the namespace `Langlands.RankinSelberg`.

No new source theorem is stated or proved. In particular, the module contains
no source pairing lemma, no dimension or vanishing assertion, no
finite-filtration bound and no uniqueness result.

## Ranks, field and carriers

For natural numbers `n < r`, the large group is `GL_(r+1)` with its actual
mirabolic subgroup `mirabolic r F`, and the small group is
`GeneralLinear (n+1) F`. The field is `F : Type uF` with `[Field F]`. A
`[TopologicalSpace F]` is required only for the weight and the form-space
theorems, because the published unitary additive character
`ψ : UnitaryAdditiveCharacter F` enters there. The absolute value
`abv : AbsoluteValue F ℝ` is arbitrary. In the form-space theorems the carriers
`V : Type uV` and `W : Type uW` are complex modules over `AddCommGroup`. The
three universes `uF`, `uV` and `uW` are independent level parameters. Only
`n < r` is assumed, so `n = 0` and adjacent ranks `r = n+1` are included.

## The test type

`UnequalRankMixedTest n r F` is the reducible abbreviation for the sum type

```text
GeneralLinear (n+1) F ⊕ unequalRankCovarianceSubgroup n r F.
```

The second summand is the carrier of the published actual subgroup
`unequalRankCovarianceSubgroup n r F` of `GeneralLinear.upperUnipotent (r+1) F`.
Its members are the upper unipotent matrices whose leading `(n+2)`-square block
is the identity. This is `U_(n+2,r+1)`, not the larger group defined by an
`(n+1)`-square block. At adjacent ranks the published lemma
`unequalRankCovarianceSubgroup_adjacent` identifies this subgroup with `⊥`. The
summand is still the carrier of that subgroup and is not removed from the test
type.

## The test maps

The three test maps are arbitrary functions on tests, as `MixedBilinear`
requires. They are defined with `Sum.elim`. No homomorphism or multiplicativity
property is claimed for any of them, and no covariance monoid is introduced.

- `unequalRankMixedLeft hnr : UnequalRankMixedTest n r F → mirabolic r F` sends
  `Sum.inl g` to `unequalRankEmbedding hnr g`, the block matrix
  `diag(g, I_(r-n))`. It sends `Sum.inr u` to `unequalRankUnipotentLift u.val`,
  the matrix `u` itself regarded as an element of the mirabolic subgroup.
- `unequalRankMixedRight : UnequalRankMixedTest n r F → GeneralLinear (n+1) F`
  sends `Sum.inl g` to `g` and `Sum.inr u` to `1`. Its ranks `n`, `r` and its
  field are implicit. It takes no `hnr`, because that hypothesis would be
  unused.
- `unequalRankMixedWeight ψ abv s : UnequalRankMixedTest n r F → ℂ`, for
  `s : ℂ`, sends `Sum.inl g` to

  ```text
  determinantWeight abv g (((r - n : ℕ) : ℂ) / 2 - s),
  ```

  that is `|det g|^((r-n)/2 - s)` measured by `abv`. It sends `Sum.inr u` to
  `(standardCharacter ψ r u.val : ℂ)`, the published standard character of the
  upper unipotent group of `GL_(r+1)`. This map also takes no `hnr`. The exponent
  uses the natural-number difference `r - n` cast to `ℂ`, exactly as in the
  published covariance predicate.

The reduction lemmas `unequalRankMixedLeft_inl`, `unequalRankMixedLeft_inr`,
`unequalRankMixedRight_inl`, `unequalRankMixedRight_inr`,
`unequalRankMixedWeight_inl` and `unequalRankMixedWeight_inr` state these six
values. They are simp lemmas proved by `rfl`.

## Covariance equivalence

Let `ξ : Representation ℂ (mirabolic r F) V`,
`η : Representation ℂ (GeneralLinear (n+1) F) W`, `s : ℂ` and
`B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ` be arbitrary. `isCovariant_unequalRankMixed_iff`
proves

```text
MixedBilinear.IsCovariant (unequalRankMixedLeft hnr) unequalRankMixedRight
    (unequalRankMixedWeight ψ abv s) ξ η B
  ↔ IsUnequalRankMirabolicCovariant hnr ψ abv ξ η s B.
```

The `Sum.inl g` tests give the published determinant law verbatim. For the
second law, the forward direction packages a matrix `u` with its membership
proof `IsUnequalRankCovarianceUnipotent n u` as the test `Sum.inr ⟨u, hu⟩`.
It then simplifies the second action at the test value `1`, using `map_one`
and `Module.End.one_apply`. The reverse direction case-splits the test and
unpacks the subtype element into `u` and its membership proof. Both directions
of the quantified unipotent condition are therefore recovered.

## Submodule and length equalities

`forms_unequalRankMixed_eq` proves the equality of actual submodules of
`V →ₗ[ℂ] W →ₗ[ℂ] ℂ`

```text
MixedBilinear.forms (unequalRankMixedLeft hnr) unequalRankMixedRight
    (unequalRankMixedWeight ψ abv s) ξ η
  = unequalRankMirabolicForms hnr ψ abv ξ η s,
```

by extensionality and the covariance equivalence.

`length_unequalRankMixed_eq` proves

```text
MixedBilinear.length (unequalRankMixedLeft hnr) unequalRankMixedRight
    (unequalRankMixedWeight ψ abv s) ξ η
  = Module.length ℂ (unequalRankMirabolicForms hnr ψ abv ξ η s).
```

It transports module length along `LinearEquiv.ofEq` for the submodule
equality. Both sides lie in `ℕ∞`, and no finiteness is assumed or claimed.

## Compatibility with coefficient models

Let `π : Representation ℂ (GeneralLinear (r+1) F) V` and
`σ : Representation ℂ (GeneralLinear (n+1) F) W` be arbitrary ambient
representations, with functionals `ℓ : glFunctionals ψ r π` and
`ℓ' : glInverseFunctionals ψ n σ`. Let `B` be an arbitrary bilinear form on the
actual coefficient models `(coefficientModel π ℓ).toSubmodule` and
`(coefficientModel σ ℓ').toSubmodule`. `mem_forms_unequalRankMixed_restrict_iff`
proves that `B` lies in the mixed form space for the representations

```text
(modelRepresentation π ℓ).comp (mirabolic r F).subtype   and
modelRepresentation σ ℓ'
```

if and only if `IsUnequalRankBilinearCovariant hnr ψ abv π σ ℓ ℓ' s B`, the
published coefficient-model predicate. The first representation is the
coefficient-model representation restricted to the mirabolic subgroup. The
proof rewrites with `forms_unequalRankMixed_eq` and then applies the published
`mem_unequalRankMirabolicForms_restrict_iff`. Neither functional needs to be
nonzero.

## Parameters

The parameter `s` is the integral parameter, and the determinant exponent
`(r-n)/2 - s` is kept with its sign. In the source's twisted pairing space, the
twist parameter is `s - (r-n)/2`. The published Markdown of
`UnequalRankBilinearForms` records this correspondence for JPSS §2.11. This
module introduces no further source correspondence.

## Scope

There is no irreducibility, smoothness, admissibility, finite-length,
genericity, functional-uniqueness, central-character or spectral assumption on
`ξ`, `η`, `π` or `σ`. No local-field structure, `PadicField` or normalized
absolute value is used. The module makes no dimension assertion. The finite
mixed-filtration bounds, the source pairing lemma and the full unequal-rank
uniqueness `UnequalRankBilinearUniquenessStatement` belong to separate units.

## Provenance

This is an internal adapter derived only from the exact definitions of the
published `MixedBilinear.IsCovariant`, `MixedBilinear.forms`,
`MixedBilinear.length`, `unequalRankEmbedding`, `unequalRankUnipotentLift`,
`unequalRankCovarianceSubgroup`, `IsUnequalRankMirabolicCovariant`,
`unequalRankMirabolicForms`, `determinantWeight` and `standardCharacter`. Its
compatibility theorem reuses the published
`mem_unequalRankMirabolicForms_restrict_iff`. No original-literature statement
is transcribed here, so no source citation is needed beyond the provenance
already recorded in the Markdown of the two imported modules.
