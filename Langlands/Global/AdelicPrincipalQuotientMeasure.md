# The canonical Haar product on the full principal adelic quotient

The module `Langlands.Global.AdelicPrincipalQuotientMeasure` contains one
theorem, `Langlands.Global.RestrictionSplitCentre.principalQuotientProductMeasure`,
whose type is exactly
[`PrincipalQuotientProductMeasureStatement`](AdelicPrincipalQuotientProductMeasureStatement.md).

For a number field `F` and an affine, locally finite type connected
reductive `F`-group scheme `G`, it states that the measurable equivalence
`principalQuotientProductEquiv F G hG`,

\[
G(F)\backslash G(\mathbb A_F) \;\longrightarrow\; A_G\times [G],\qquad
[an]\longmapsto (a,[n]),
\]

is measure preserving. The source carries `rationalQuotientHaarMeasure F G`,
the quotient of the fixed Haar measure on `G(𝔸_F)` with counting
normalization on `G(F)`. The target carries
`(positiveCentreHaarMeasure F G hG).prod (canonicalMeasure F G)`. Neither
measure is rescaled, and no constant relates the two sides.

| Declaration | Kind | Content |
| --- | --- | --- |
| `principalQuotientProductMeasure` | theorem (proved) | `PrincipalQuotientProductMeasureStatement` |

## Proof

The proof is a single term that combines two theorems of the Library:

```
principalQuotientProductMeasure_of_productQuotientMeasure
  LeftCosetSpace.productQuotientMeasure
```

1. `Langlands.Global.LeftCosetSpace.productQuotientMeasure` (module
   `Langlands.Global.LeftCosetProductMeasureProof`) proves
   `ProductQuotientMeasureStatement` for all universes. That is the product
   law for discrete left quotients, under the following hypotheses.
   - `A`, `N` and `G` are groups with topologies and Borel measurable
     structures, and `N` and `G` are second-countable topological groups.
   - `E : A × N ≃ₜ* G` is an isomorphism of topological groups.
   - `H` is a discrete subgroup of `N` and `Γ` is a discrete subgroup of `G`.
     They correspond under `E`: `E(a, n) ∈ Γ` exactly when `a = 1` and
     `n ∈ H`.
   - `μA` and `μN` are s-finite measures on `A` and `N`.
   - `μG` is a measure on `G` that is invariant under left multiplication
     by `Γ`.

   If `E` carries `μA.prod μN` to `μG`, then the induced map
   `Γ \ G → A × H \ N` carries the count-normalized quotient of `μG` to
   `μA` times the count-normalized quotient of `μN`. Each of these quotient
   measures is defined by pushing forward the ambient measure restricted to
   a Borel fundamental domain that the Library chooses independently of the
   measure. The proof constructs a second Borel fundamental domain,
   `E(A × D)` for `Γ` in `G`, where `D` is the chosen domain for `H` in `N`.
   The left `Γ`-invariance of `μG` is what allows the quotient of `μG` to be
   computed with `E(A × D)` in place of the chosen domain
   (`discreteQuotientMeasure_eq`). Here the statement is used at universes
   `0, 0, 0`, which Lean infers from the hypothesis type of the next
   theorem.
2. `Langlands.Global.RestrictionSplitCentre.principalQuotientProductMeasure_of_productQuotientMeasure`
   (module `Langlands.Global.AdelicPrincipalQuotientProductMeasureProof`)
   derives `PrincipalQuotientProductMeasureStatement` from
   `ProductQuotientMeasureStatement.{0, 0, 0}`. Its proof applies the product
   law to the multiplication isomorphism
   `intrinsicNormOneDecomposition F G hG : A₀ × G(𝔸_F)¹ ≃ₜ* G(𝔸_F)`. Here
   `A₀` is the intrinsic positive subgroup of the canonical split central
   torus, `H` is the norm-one rational subgroup and `Γ = G(F)`. The measures
   are `intrinsicCentreHaarMeasure` and the Haar measures, related by
   `measurePreserving_intrinsicNormOneDecomposition`. The correspondence of
   the subgroups is `intrinsicNormOneDecomposition_mem_principal`, and
   discreteness is `isDiscrete_rationalNormOneSubgroup` and
   `isDiscrete_rationalSubgroup`. Instance search supplies the rest: the
   Borel structures, second countability of `G(𝔸_F)¹` and `G(𝔸_F)`,
   s-finiteness of `intrinsicCentreHaarMeasure` and of Haar measure on
   `G(𝔸_F)¹`, and invariance of Haar measure on `G(𝔸_F)` under left
   multiplication by `G(F)`. The last comes from the left invariance of Haar
   measure, restricted to the subgroup by Mathlib's
   `Subgroup.smulInvariantMeasure`. Then
   `measurePreserving_positiveCentreEquiv` identifies the first factor with
   `(A_G, positiveCentreHaarMeasure)`, and
   `measurePreserving_canonicalNormOneQuotientHomeomorph` identifies the
   second with `([G], canonicalMeasure)`.

Applying the second theorem to the first gives the statement. The proof
assumes neither finite volume of `[G]` nor unimodularity.

## Provenance

The theorem follows from the two Library theorems above and is not
numbered in the literature. The split centre `A_G`, the norm-one group
`G(𝔸_F)¹`, the decomposition `A_G G(𝔸_F)¹ = G(𝔸_F)` with
`A_G ∩ G(𝔸_F)¹ = 1` for a number field, the quotient `[G] = A_G G(F) \ G(𝔸_F)`
and the homeomorphism `G(F) \ G(𝔸_F)¹ → [G]` follow Getz–Hahn, *An
Introduction to Automorphic Representations* (2024), §2.6, (2.19)–(2.22) and
Lemma 2.6.2, printed pp. 68–69 (PDF pp. 85–86). The quotient measures, with
counting measure on `G(F)`, follow §3.6, printed p. 90 (PDF p. 106). The
exact normalization of the first factor is the Library's
`positiveCentreHaarMeasure`, the image under `positiveCentreEquiv` of
`intrinsicCentreHaarMeasure`. The product of `intrinsicCentreHaarMeasure`
with the fixed Haar measure on `G(𝔸_F)¹` is carried to the fixed Haar
measure on `G(𝔸_F)` by multiplication. The registered source is
`getz-hahn-2024-automorphic-representations` (SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`).
