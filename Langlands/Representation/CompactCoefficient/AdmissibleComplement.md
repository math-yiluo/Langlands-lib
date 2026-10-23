# Isotypic complements for compact-coefficient classes

This internal module proves that, for every compact-coefficient class `c` and
every smooth complex representation `A`, the published intrinsic subrepresentations

- `CompactCoefficientClass.isotypicSubrepresentation c A` and
- `CompactCoefficientClass.annihilatorSubrepresentation c A`

are complementary subspaces of `A`. All declarations are in namespace
`Langlands.CompactSplitting`.

## Main result

`isCompl_isotypicSubrepresentation_annihilatorSubrepresentation μ hcof c A` has
the following hypotheses.

- `G` is a topological group with a Borel measurable structure.
- `μ` is a left Haar measure (`Measure.IsHaarMeasure`). No right invariance,
  unimodularity, regularity or σ-compactness is assumed.
- `hcof`: every open subgroup of `G` contains a compact open subgroup.
- `c : CompactCoefficientClass.{uG, uV} G` is any class.
- `A : SmoothRep.{0, uG, uW} ℂ G` is any smooth complex representation. It need
  not be admissible, of finite length or finite dimensional.

The conclusion is

`IsCompl (isotypicSubrepresentation c A).toSubmodule (annihilatorSubrepresentation c A).toSubmodule`.

The group universe `uG`, the representative universe `uV` and the ambient
universe `uW` are independent. No admissibility hypothesis is needed.

The proof is induction on the quotient `c`: it reduces to
`isCompl_isotypicSubrepresentation_annihilatorSubrepresentation_of_rep μ hcof D hD A`.
That theorem takes an actual representative `D` with
`CompactCoefficientClass.ofRep D = c`. The published identities
`isotypicSubrepresentation_eq_iSup_range` and
`annihilatorSubrepresentation_eq_iInf_ker` rewrite the two intrinsic
subrepresentations as follows. The first is the supremum of the ranges of all
intertwiners `D → A`. The second is the infimum of the kernels of all
intertwiners `A → D`. Then `isCompl_isotypicPart_annihilatorPart` below applies.

`isAdmissible_of_compactCoefficients μ hcof ρ hρ hirr hc` supplies the
admissibility used there. Let `ρ` be an irreducible smooth representation with
compact smooth-dual coefficients. For an open subgroup `K`, choose a compact
open `L ≤ K`. The published `CompactCoefficientClass.finiteDimensional_fixedVectors`
makes the `L`-fixed vectors finite-dimensional. The `K`-fixed vectors form a
subspace of them.

## The complement for an admissible representative

Fix an irreducible admissible representation `ρ` with compact smooth-dual
coefficients and a smooth representation `σ`.

- `isotypicPart ρ σ` is the supremum of the ranges of all intertwiners `ρ → σ`.
- `annihilatorPart ρ σ` is the infimum of the kernels of all intertwiners
  `σ → ρ`. `mem_annihilatorPart_iff` gives its membership condition.

`isCompl_isotypicPart_annihilatorPart μ hcof ρ hρ hirr hc hσ` is the conjunction
of the following two results.

### Disjointness

`sum_eq_zero_of_mem_annihilatorPart` proves the following. Take a finite sum
`∑ i ∈ s, f i (v i)` of vectors in ranges of intertwiners `f i : ρ → σ`. If the
sum lies in the annihilator part, it is zero. The proof is induction on `s`,
generalizing the family `f`.

- Remove the first index `a`. If `f a = 0`, drop the term.
- Otherwise `f a` is injective, by irreducibility. Take the retraction `r` of
  `exists_retraction` (module `AdmissibleRetraction`). Applying `r` to the sum
  gives `v a = -r (∑ i ∈ s, f i (v i))`.
- The whole sum then equals `∑ i ∈ s, (f i - f a ∘ r ∘ f i) (v i)`. This is a
  sum over `s` alone, so the induction hypothesis applies.

`isotypicPart_inf_annihilatorPart` writes a vector of the supremum as such a
finite sum, using `Submodule.mem_iSup_iff_exists_finset` and
`Submodule.mem_iSup_finset_iff_exists_sum`.

### Exhaustion

`range_le_isotypicPart_sup_annihilatorPart μ hcof ρ hρ hirr hc σ n` is proved by
induction on `n`. It holds for every smooth representation `τ`, on a carrier in
a fixed universe `uU`, and every intertwiner `ι : τ → σ`, under two conditions:
the space `Hom(τ, ρ)` of intertwiners is finite-dimensional, and its dimension
is at most `n`. The conclusion is that the range of `ι` lies in
`isotypicPart ρ σ ⊔ annihilatorPart ρ σ`.

- If every intertwiner `τ → ρ` is zero, the range of `ι` lies in the annihilator
  part. This is `range_le_annihilatorPart_of_forall_eq_zero`.
- Otherwise a nonzero `e : τ → ρ` is surjective, by irreducibility.
  `exists_section` (module `AdmissibleLifting`) gives `s` with `e ∘ s = id`.
- Let `K = ker e`. Then `u ↦ u - s (e u)` is an intertwiner `π : τ → K` that
  fixes `K`. Precomposition with `π` embeds `Hom(K, ρ)` into `Hom(τ, ρ)`. The
  image misses `e`, because `π (s v₀) = 0` while `e (s v₀) = v₀ ≠ 0`. So the
  dimension drops strictly and the induction hypothesis applies to `ι`
  restricted to `K`.
- Finally `ι u = ι (s (e u)) + ι (π u)`. The first term lies in the range of
  `ι ∘ s : ρ → σ`, hence in the isotypic part. The second term lies in the
  range of the restriction of `ι` to `K`.

`isotypicPart_sup_annihilatorPart` applies this to the cyclic subrepresentation
`orbitSpan σ w`, the span of the orbit of `w`. `isSmooth_subrepresentation`
shows that it is smooth. By `eq_zero_of_apply_orbitSpan_eq_zero`, an
intertwiner out of it is determined by its value at `w`. Let `K` be an open
subgroup fixing `w`. That value is `K`-fixed, so evaluation at `w` embeds
`Hom(orbitSpan σ w, ρ)` into the `K`-fixed vectors of `ρ`. These are
finite-dimensional by admissibility. Thus `w`, which is the image of itself
under the subrepresentation inclusion, lies in the sum.

## Helper definitions

- The existing `Langlands.ProductFactorization.subrepresentationInclusion P`
  from [MultiplicityDefinitions](../Smooth/Factorization/MultiplicityDefinitions.md)
  supplies the inclusion of a subrepresentation as an actual intertwiner.
- `orbitSpan σ w` is the subrepresentation spanned by `{σ g w}`, and
  `mem_orbitSpan_self` shows that it contains `w`.

## Provenance

This is internal infrastructure. It supplies the complementarity input that the
published `ConditionalProjection`, `OrthogonalProjectorFamily`,
`SelectedProjector` and `NormalSubgroupDecomposition` constructions take as a
hypothesis. Compare I. N. Bernstein and A. V. Zelevinsky, *Representations of
the group GL(n,F) where F is a non-archimedean local field*, Russian Math.
Surveys 31:3 (1976) (literature ID
`bernstein-zelevinsky-1976-representations-gln`), Section 2.43 and
Theorem 2.44(a), p. 28. There the isotypic projection for an irreducible
“finite” representation is constructed by integration over a unimodular,
countable-at-infinity group. The present proof follows a different route: it
uses the lifting and retraction properties of `AdmissibleLifting` and
`AdmissibleRetraction`, finite-sum induction and dimension induction. It
assumes only a left Haar measure and the cofinality of compact open subgroups.
