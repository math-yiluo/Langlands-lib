# Unequal-rank mirabolic-versus-general-linear covariant bilinear forms

This module constructs the concrete groups, maps and form space behind the
unequal-rank covariance of JPSS §2.11, for arbitrary complex representations of
the actual mirabolic subgroup of `GL_(r+1)` and of the actual `GL_(n+1)`. All
declarations live in the namespace `Langlands.RankinSelberg`.

The general form space `unequalRankMirabolicForms` is an **internal
construction** that implements the source's covariance conditions for arbitrary
representations. It is not a proof, nor a statement, of the source's
irreducible Lemma on printed p.399, nor of the Proposition on the same page. It
makes no dimension, vanishing or spectral claim. Those results, the general
mixed-covariance filtration machinery, and the final Whittaker-type uniqueness
`UnequalRankBilinearUniquenessStatement` belong to other units.

## Ranks and data

For natural numbers `n < r`, write `R = r+1` for the large rank and `t = n+1`
for the small rank. The field is `F : Type uF` with `[Field F]`. A
`[TopologicalSpace F]` is required only where the published unitary additive
character `ψ : UnitaryAdditiveCharacter F` enters, namely in the covariance
predicate and the form space. The group constructions use no topology. The
representation carriers `V : Type uV` and `W : Type uW` have universes
independent of each other and of `uF`.

## The block embedding `GL_t → P_R`

`unequalRankBlock_mem_mirabolic hnr g` proves that, for
`g : GeneralLinear (n+1) F`, the ambient matrix

```text
GeneralLinear.reindex
  (finCongr (show n + (r-n) + 1 = r+1 by omega))
  (appendIdentity n (r-n) g)
```

lies in `GeneralLinear.mirabolic r F`. Its last row is `(0, …, 0, 1)` because
the last index lies in the identity block of `appendIdentity`.

`unequalRankEmbedding hnr : GeneralLinear (n+1) F →* mirabolic r F` is the
actual monoid homomorphism obtained by composing the existing block embedding
`appendIdentity n (r-n)` with the reindexing equivalence and restricting the
codomain to the mirabolic subgroup. No abstract map is supplied.

- `unequalRankEmbedding_val` (simp, proved by `rfl`) states that the underlying
  ambient matrix of `unequalRankEmbedding hnr g` is exactly the expression
  above, which is the embedding `ι` written in the published predicate
  `IsUnequalRankBilinearCovariant`.
- `unequalRankEmbedding_entry` states that its `(i, j)` entry is `g` at the
  corresponding indices when both `i.val` and `j.val` are below `n+1`, is zero
  when only `i.val` is below `n+1`, and is the identity-matrix entry
  `if i = j then 1 else 0` otherwise. Thus the embedding is `diag(g, I_(r-n))`.

The rank-one smaller group `n = 0` and adjacent ranks `r = n+1` are retained;
only `n < r` is assumed.

## The unipotent covariance group `U_(n+2,r+1)`

`unequalRankUnipotentLift : GeneralLinear.upperUnipotent (r+1) F →* mirabolic r F`
is the canonical inclusion `Subgroup.inclusion upperUnipotent_le_mirabolic`.
`unequalRankUnipotentLift_val` (simp, `rfl`) states that it does not change the
underlying ambient matrix.

`unequalRankCovarianceSubgroup n r F` is the actual subgroup of
`GeneralLinear.upperUnipotent (r+1) F` whose carrier is the set of `u`
satisfying the already published predicate
`IsUnequalRankCovarianceUnipotent n u`, namely that the leading
`(n+2)`-square block of `u` is the identity. Closure under products and
inverses uses a private lemma: left multiplication by such an element does not
change the leading `(n+2)`-square block of any upper unipotent matrix. This
holds because the entries outside that block in its first `n+2` rows are
multiplied by entries below the diagonal of the second factor, which vanish.

- `mem_unequalRankCovarianceSubgroup` (simp, `Iff.rfl`) identifies membership
  with `IsUnequalRankCovarianceUnipotent n u`.
- `unequalRankCovarianceSubgroup_adjacent n F` proves that at adjacent ranks
  the group is trivial: `unequalRankCovarianceSubgroup n (n+1) F = ⊥`.

This subgroup is `U_(t+1,R) = U_(n+2,r+1)`, not the larger `U_(t,R)`. The
subgroup is provided for later use; the covariance predicate below quantifies
directly over `u` satisfying the published membership predicate.

## The covariance predicate and the form space

Let `ψ : UnitaryAdditiveCharacter F`, `abv : AbsoluteValue F ℝ`,
`ξ : Representation ℂ (mirabolic r F) V`,
`η : Representation ℂ (GeneralLinear (n+1) F) W` and `s : ℂ`, where `V` and
`W` are complex modules over `AddCommMonoid` carriers. For a curried bilinear
form `B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ`,
`IsUnequalRankMirabolicCovariant hnr ψ abv ξ η s B` is the conjunction of

```text
∀ g v w,  B (ξ (unequalRankEmbedding hnr g) v) (η g w)
            = determinantWeight abv g (((r-n : ℕ) : ℂ)/2 - s) * B v w
```

and

```text
∀ u : GeneralLinear.upperUnipotent (r+1) F,
  IsUnequalRankCovarianceUnipotent n u →
  ∀ v w,  B (ξ (unequalRankUnipotentLift u) v) w
            = (standardCharacter ψ r u : ℂ) * B v w.
```

Here `determinantWeight abv g z = (abv (det g) : ℂ) ^ z` is the published
determinant weight, and `standardCharacter ψ r` is the published standard
character of the upper unipotent group of `GL_(r+1)`: the value of `ψ` on the
first-superdiagonal sum. The exponent uses the natural-number difference
`r - n`, cast to `ℂ`, which equals the integer difference because `n < r`.

`unequalRankMirabolicForms hnr ψ abv ξ η s` is the actual
`Submodule ℂ (V →ₗ[ℂ] W →ₗ[ℂ] ℂ)` with this carrier. Its zero, addition and
scalar-multiplication closure are proved directly from the linearity of the
two laws. `mem_unequalRankMirabolicForms` (`Iff.rfl`) characterizes membership
by the predicate.

There is no irreducibility, smoothness, admissibility, finite-length,
genericity, central-character, analytic or dimension assumption on `ξ` or
`η`.

## Compatibility with the published coefficient-model predicate

In this section `V` and `W` are `AddCommGroup` carriers, matching the published
predicate. Let `π : Representation ℂ (GeneralLinear (r+1) F) V`,
`σ : Representation ℂ (GeneralLinear (n+1) F) W`, `ℓ : glFunctionals ψ r π`
and `ℓ' : glInverseFunctionals ψ n σ`, and let `B` be a bilinear form on the
coefficient images `(coefficientModel π ℓ).toSubmodule` and
`(coefficientModel σ ℓ').toSubmodule`.

`isUnequalRankMirabolicCovariant_restrict_iff` proves

```text
IsUnequalRankMirabolicCovariant hnr ψ abv
    ((modelRepresentation π ℓ).comp (mirabolic r F).subtype)
    (modelRepresentation σ ℓ') s B
  ↔ IsUnequalRankBilinearCovariant hnr ψ abv π σ ℓ ℓ' s B,
```

and `mem_unequalRankMirabolicForms_restrict_iff` is the same statement for
membership in `unequalRankMirabolicForms`. Here the first representation is the
coefficient-model representation restricted to the mirabolic subgroup. Both
proofs are `Iff.rfl`: the restricted action at the embedding and at the
unipotent lift is, by definition, the model action at the ambient matrices
written in the published predicate. The functionals may be zero, and no
Whittaker-type hypothesis is assumed.

## Source correspondence and parameters

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions*, American Journal of Mathematics **105** (1983), 367–464, §2.11,
printed pp.398–403. Registered source `jpss-1983-rankin-selberg`, at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.398–403 (zero-based PDF pages 33–38) were read completely. No
erratum for this paper was found in the current project or Library notes.

The source's large rank `r` and small rank `t` are `R = r+1` and `t = n+1`
here, and its `P_r` is `mirabolic r F`. Equation (2.11.2), printed p.398, states,
except for finitely many `q^(-s)`, the simultaneous `G_t` covariance of the
integral with factor
`|det g|^((r-t)/2 - s)` in the source's notation, that is
`|det g|^((R-t)/2 - s) = |det g|^((r-n)/2 - s)` here. This is the first law,
with `G_t` acting on the first argument through `g ↦ diag(g, I)`.
Equation (2.11.3) defines `U_(t,r)` as the matrices `[[1_t, u₂], [0, u₁]]` with
`u₁` upper unitriangular, and (2.11.4), printed p.399, imposes
`θ_r(u)` covariance for `u ∈ U_(t+1,r)`. This is the second law, with
`θ_r = standardCharacter ψ r` and `U_(t+1,R) = U_(n+2,r+1)`.

The p.399 Proposition and Lemma use the space `Bil_(G_t)(ξ ⊗ α^s, π')` with
`α(g) = |det g|`. Invariance of such a twisted pairing means that the untwisted
form transforms by `|det g|^(-λ)` when the twist parameter is `λ`. Since `s` in
this module is the integral parameter, the source's twisted-pairing parameter is
`λ = s - (R-t)/2 = s - (r-n)/2`. The construction keeps the sign of the
exponent and does not move the half-rank shift into a hypothesis.

The source's Lemma assumes a smooth irreducible representation `ξ` of `P_r`
and an irreducible admissible representation `π'` of `G_t`. It asserts that
the form space is one-dimensional for the compact/generic pair and vanishes
outside finitely many `q^(-s)` otherwise. This module proves neither assertion
and assumes neither; it only constructs the space those assertions are about.

## Provenance

The subgroup, embedding, lift, predicate and form space are internal
constructions derived from JPSS (2.11.2)–(2.11.4) and from the published
`appendIdentity`, `mirabolic`, `upperUnipotent_le_mirabolic`,
`IsUnequalRankCovarianceUnipotent`, `determinantWeight` and
`standardCharacter`. The compatibility theorems relate them to the published
`IsUnequalRankBilinearCovariant`, whose Markdown records the same source
correspondence.
