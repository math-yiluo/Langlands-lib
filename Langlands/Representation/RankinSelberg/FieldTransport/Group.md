# Quotient measures and Whittaker models along a group isomorphism

Author: Worker 5731. This is a supporting lemma module for the proof of
`Langlands.Global.PoleComparison.HenniartCompositeFactorStatement` (Task 5230).
It contains no new statements of published mathematics. It records standard
facts on transporting measures and Whittaker-type functionals along an
isomorphism of groups, which the later modules of
`Langlands.Representation.RankinSelberg.FieldTransport` apply to the entrywise
map `GL_n(F) → GL_n(E)` induced by an isomorphism of topological fields.

## Products of pushed-forward measures

In namespace `Langlands.QuotientIntegration`:

- `map_prod_map_measurableEquiv eα eγ μ ν` states that for measurable
  equivalences `eα : α ≃ᵐ β` and `eγ : γ ≃ᵐ δ`, the product of the pushforwards
  `(μ.map eα).prod (ν.map eγ)` is the pushforward of `μ.prod ν` along
  `Prod.map eα eγ`. Only the second measure `ν` is assumed s-finite. The proof
  evaluates both sides on a measurable set with `Measure.prod_apply` and uses
  the change of variables `lintegral_map_equiv` in the first coordinate.
  Avoiding σ-finiteness of the first factor matters because the first factor is
  later an arbitrary measure on a unipotent quotient.
- `integrable_map_prod_map_iff` is the resulting integrability criterion:
  `f` is integrable for the pushed-forward product exactly when
  `(x, y) ↦ f (eα x, eγ y)` is integrable for `μ.prod ν`.

## Right invariance

- `isMulRightInvariant_map_mulEquiv` shows that pushforward of a right-invariant
  measure along a measurable group isomorphism `e` is right invariant. Right
  translation by `h = e g` after `e` is `e` after right translation by `g`.
- `isMulRightInvariant_map_iff Θ μ` states, for a topological group isomorphism
  `Θ : G ≃ₜ* G'` between Borel groups, that `μ.map Θ` is right invariant if and
  only if `μ` is. The converse direction pushes forward along `Θ.symm`.

## Coset spaces

Fix `Θ : G ≃ₜ* G'` and subgroups `H` of `G` and `H'` of `G'` with
`hH : ∀ g, Θ g ∈ H' ↔ g ∈ H`. The coset spaces are the published
`LeftQuotient H` of `Langlands.Analysis.Local.QuotientMeasure`, i.e. the spaces
of cosets `H g`.

- `cosetHomeomorph Θ hH : LeftQuotient H ≃ₜ LeftQuotient H'` is the homeomorphism
  `H g ↦ H' (Θ g)`, obtained from `Homeomorph.Quotient.congr`. Two elements
  lie in the same coset of `H` exactly when their images lie in the same coset
  of `H'`; since `Θ` is multiplicative this is `hH` applied to `y * x⁻¹`.
  `cosetHomeomorph_mk` is its value on a coset.
- `subgroupEquiv Θ hH : H ≃ₜ* H'` is the restriction of `Θ`;
  `subgroupEquiv_apply_coe` records its value.
- `rightTranslate_cosetHomeomorph` shows that the published right translation
  `rightTranslate` of cosets commutes with `cosetHomeomorph`:
  translating the image of `q` by `Θ g` is the image of `q` translated by `g`.

## Compatible quotient measures

Now `G`, `G'`, `H`, `H'` and the two quotients carry Borel σ-algebras. The
abbreviations `leftQuotientMeasurableEquiv`, `groupMeasurableEquiv` and
`subgroupMeasurableEquiv` are the three homeomorphisms viewed as measurable
equivalences.

- `quotientAverage_cosetHomeomorph` states that, when `μH'` is the pushforward
  of the right-invariant measure `μH` along `subgroupEquiv Θ hH`, the published
  orbital average `quotientAverage H' μH' f'` at the image of `q` equals
  `quotientAverage H μH (f' ∘ Θ)` at `q`. On a coset `H x` this is the change of
  variables `integral_map_equiv` for the subgroup integral.
  `quotientAverage_comp_cosetHomeomorph` is the same identity of functions.
- `isCompatible_map_iff Θ hH μG μH μG' μH' hG hμ ν` states that, if
  `μG' = μG.map Θ` and `μH' = μH.map (subgroupEquiv Θ hH)`, then
  `ν.map (cosetHomeomorph Θ hH)` satisfies the published compatibility predicate
  `IsCompatible H' μG' μH'` exactly when `ν` satisfies `IsCompatible H μG μH`.
  The five clauses of `IsCompatible` (nonzero, regular, right invariant under
  every `rightTranslate`, integrable averages of continuous compactly supported
  test functions, and the integration formula) are checked one by one. Test
  functions on `G'` and on `G` correspond by `f' ↦ f' ∘ Θ` (continuity and
  compact support are preserved by composing with a homeomorphism), integrals
  over `G'` and over `G` correspond by `integral_map_equiv`, and averages
  correspond by the previous item. Regularity uses `Measure.Regular.map` in both
  directions; invariance uses `rightTranslate_cosetHomeomorph` and injectivity
  of pushforward along a measurable equivalence.
- `compatibleMeasureExists_iff` deduces that the published
  `CompatibleMeasureExists H' μG' μH'` holds exactly when
  `CompatibleMeasureExists H μG μH` holds, under the same hypotheses on `μG'`
  and `μH'`.
- `exists_map_eq` shows that every measure on `LeftQuotient H'` is the
  pushforward along `cosetHomeomorph Θ hH` of a measure on `LeftQuotient H`,
  namely of its pushforward along the inverse.

## Equivariant functionals and coefficient models

In namespace `Langlands.Whittaker`, fix a commutative ring `R`, a group
isomorphism `Θ : G ≃* G'`, subgroups `N` and `N'` with
`hN : ∀ g, Θ g ∈ N' ↔ g ∈ N`, and characters `θ : N →* Rˣ`, `θ' : N' →* Rˣ`
with `hθ : ∀ n, θ' (Θ n) = θ n`. The objects below are the published ones of
`Langlands.Representation.Whittaker.Algebraic`.

- `functionals_comp Θ hN hθ ρ` states that for a representation `ρ` of `G'` the
  space `functionals N θ (ρ.comp Θ.toMonoidHom)` of `(N, θ)`-equivariant
  functionals of the pulled-back representation equals the space
  `functionals N' θ' ρ`. Both are sets of linear functionals on the same space;
  every element of `N'` is `Θ n` for a unique `n ∈ N`.
- `comp_symm_mem_equivariantFunctions` and `comp_mem_equivariantFunctions` show
  that `f ↦ f ∘ Θ⁻¹` and `f ↦ f ∘ Θ` exchange the published spaces
  `equivariantFunctions N θ` and `equivariantFunctions N' θ'`. They assemble to
  the `R`-linear equivalence `equivariantEquiv Θ hN hθ`, with value lemmas
  `equivariantEquiv_apply` and `equivariantEquiv_symm_apply`.
- `functionalTransport`, `functionalTransportSymm` and
  `functionalTransportEquiv` view a functional of the pulled-back
  representation as a functional of `ρ` and back, using `functionals_comp`. The
  underlying linear map is unchanged (`functionalTransport_val`,
  `functionalTransportSymm_val`).
- `equivariantEquiv_coefficientMap` shows that `equivariantEquiv` carries the
  published coefficient function `g ↦ ℓ (ρ (Θ g) v)` of the pulled-back
  representation to the coefficient function `g' ↦ ℓ (ρ g' v)` of `ρ`.
- `mem_coefficientModel_comp_iff` deduces that `f` lies in the published
  coefficient model `coefficientModel (ρ.comp Θ.toMonoidHom) ℓ` exactly when
  `equivariantEquiv Θ hN hθ f` lies in `coefficientModel ρ` of the transported
  functional.
- `compModelEquiv Θ hN hθ ρ ℓ` is the resulting bijection of coefficient models,
  `f ↦ f ∘ Θ⁻¹`. `compModelEquiv_apply_val` records it, and
  `compModelEquiv_apply_apply` states that the transported model function takes
  at `Θ g` the value of `f` at `g`.
