# Retractions of embeddings of compact irreducible admissible representations

This internal module proves that an irreducible admissible complex
representation `ρ` with compact smooth-dual coefficients is injective among
smooth representations, in the following form. Every injective intertwiner from
`ρ` into a smooth representation has an equivariant retraction. All declarations
are in namespace `Langlands.CompactSplitting`.

The group `G` is a topological group. Carriers are complex vector spaces in
independent universes. The section `Contragredient` assumes `hcof`: every open
subgroup of `G` contains a compact open subgroup. In the Lean signatures this
hypothesis comes first, for example `exists_retraction hcof μ ρ …`.

## Averaging

`map_orbitMean_of_constant` is an algebraic lemma. Suppose a linear functional
`f` takes the constant value `c` on a finite orbit of `ρ`. Then it takes the
value `c` at the published orbit mean `Compact.orbitMean`, which is the
normalized sum over the orbit.

`averageMap_smoothDual_apply` applies this to the smooth contragredient
`smoothContragredient ρ`. Let `K` be a compact open subgroup and `u` a smooth
functional. Then the published `K`-average `Compact.averageMap` of `u` agrees
with `u` on every `K`-fixed vector `x`. Indeed, every orbit element
`k · u = u ∘ ρ(k⁻¹)` takes the value `u x` at `x`.

## The contragredient

`isIrreducible_smoothContragredient hcof ρ hρ hirr` proves that the smooth
contragredient of an irreducible admissible `ρ` is irreducible.

- It is nontrivial: `exists_smooth_functional_ne_zero` from `AdmissibleLifting`
  gives a nonzero smooth functional.
- Let `U` be a nonzero subrepresentation of the contragredient. The common
  kernel `U'` of the functionals in `U` is a subrepresentation of `ρ`. It is
  not all of `V`, because then `U = ⊥`. So `U' = ⊥` by irreducibility of `ρ`.
- Let `η` be any smooth functional. By `hcof` it is fixed by a compact open
  subgroup `K`. Admissibility makes `X = V^K` finite-dimensional. The published
  restriction `smoothDualFixedRestriction ρ K` is bijective
  (`smoothDualFixedRestriction_bijective`) from `K`-fixed smooth functionals
  onto `Module.Dual ℂ X`. Let `S` be the image of the `K`-fixed members of `U`.
  If `x ∈ X` is killed by `S`, then every `u ∈ U` kills `x`. To see this,
  average `u` over `K`. The average stays in `U` by the published
  `CompactCoefficientSemisimplicity.averageMap_mem`, is `K`-fixed, and has the
  same value at `x`. Hence `x ∈ U' = ⊥`. Thus the dual coannihilator of `S` is
  zero. Finite-dimensional duality,
  `Subspace.dualCoannihilator_dualAnnihilator_eq`, then gives `S = ⊤`.
  Injectivity of the restriction places `η` in `U`.

`hasCompactSmoothDualCoefficients_smoothContragredient hcof ρ hρ hc` proves that
the contragredient of an admissible `ρ` with compact smooth-dual coefficients
again has compact smooth-dual coefficients. Every smooth functional `Ξ` on the
smooth dual is evaluation at some `v ∈ V`, by the published
`smoothBidual_surjective_of_compact_cofinal`. The coefficient
`g ↦ Ξ (g · ξ)` is therefore `g ↦ ξ (ρ g⁻¹ v)`. This is a compactly supported
coefficient of `ρ` composed with inversion.

`smoothBidual_bijective_of_compact_cofinal hcof ρ hρ` combines the published
injectivity and surjectivity of the smooth bidual map for admissible `ρ`.

## Retractions

`exists_retraction hcof μ ρ hρ hirr hc hσ j hj` takes a left Haar measure `μ`
on a Borel group and an injective intertwiner `j : ρ → σ` into a smooth `σ`. It
returns `r : σ → ρ` with `r.comp j = id`. The proof proceeds as follows.

1. The contragredient map `contragredientMap j : σ̃ → ρ̃` is surjective by the
   published `contragredientMap_surjective_of_injective_of_compact_cofinal`.
2. The contragredient `ρ̃` is admissible by the published
   `isAdmissible_smoothContragredient_of_compact_cofinal`. By the two results
   above it is also irreducible with compact coefficients. So `exists_section`
   from `AdmissibleLifting` gives an intertwiner `t : ρ̃ → σ̃` with
   `contragredientMap j ∘ t = id`.
3. Since the bidual map of `ρ` is bijective, the published
   `contragredientMap_bijective_of_bidual` shows that every intertwiner
   `ρ̃ → σ̃` has the form `contragredientMap r`. Write `t` this way.
4. Then `contragredientMap (r.comp j) = contragredientMap j ∘ t = id`. Injectivity
   of `contragredientMap` on endomorphisms of `ρ`, from the same published
   theorem, gives `r.comp j = id`.

## Provenance

This is internal infrastructure for `AdmissibleComplement`. Compare
I. N. Bernstein and A. V. Zelevinsky, *Representations of the group GL(n,F)
where F is a non-archimedean local field*, Russian Math. Surveys 31:3 (1976)
(literature ID `bernstein-zelevinsky-1976-representations-gln`), Sections
2.42–2.43 and Theorem 2.44(a), pp. 27–28. There, irreducible “finite”
(compact-coefficient) representations split off as direct summands, using a
natural isotypic projector. The implemented route is our own: injectivity is
obtained from projectivity of the contragredient. The module assumes only a
left Haar measure, with no unimodularity.
