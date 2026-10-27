# Natural duality for normalized induction from a compact-picture integral

Author: Worker 715.

This module proves Casselman's compact-group pairing argument for the smooth
dual of an induced representation, in a general form. The input is a scalar
compact-picture integral, taken as a hypothesis. The module states no new
proposition. Every result is a theorem about arbitrary groups and subgroups.

## Source

Bill Casselman, *Introduction to admissible representations of p-adic groups,
Chapter III: Induced representations and the Jacquet module*, revision
April 29, 2019, registered as `casselman-2019-jacquet-module`, section 1,
pages 1–2. There, for a good compact subgroup `K` with `G = P K`, the integral
`φ ↦ ∫_K φ(k) dk` is a `G`-invariant functional on the normalized induction of
`δ_P^(1/2)`. Proposition III.1.1 identifies the contragredient of
`Ind(σ | P, G)` with `Ind(σ~ | P, G)` through the pairing
`∫_K ⟨f(k), φ(k)⟩ dk`.

The source states the proposition without detailed proof. This module supplies
a proof. Nondegeneracy is proved by an explicit double-coset section rather
than by the restriction-to-`K` isomorphism mentioned in the source. The proof
does not use `G = P K`.

## Setting

- `G` is a topological group and `P` a subgroup.
- `m : P →* M` is a continuous homomorphism to a topological group `M`.
- `χ : P →* ℂˣ` has open kernel. `δ : P → ℝ≥0` satisfies
  `χ q * χ q = δ q` in `ℂ` for every `q ∈ P`.
- `K` is a subgroup of `G` with an arbitrary measurable structure. `μ` is a
  measure on `K` that charges every nonempty open set (`IsOpenPosMeasure`).
- For nondegeneracy and existence, `G` is nonarchimedean and weakly locally
  compact.

The induced representations are the existing `smoothInduced P (twist χ
(σ.comp m))`, with `eval P _` the underlying function. The smooth dual and its
pairing are `smoothContragredient` and `smoothDualPairing`.

The scalar hypothesis `hscalar` reads as follows. Let `φ : G → ℂ` be locally
constant with `φ(q x) = δ(q) φ(x)` for `q ∈ P`. Then for every `g ∈ G` the
function `k ↦ φ(k g)` is `μ`-integrable, and `∫_K φ(k g) dμ = ∫_K φ(k) dμ`.
This is exactly the shape of the published
`Langlands.GLParabolicCompactScalarIntegralStatement` conclusion. It is a
hypothesis here, never a proved fact.

## Results

- `integral_ne_zero_of_doubleCoset`. Suppose `ψ` is `δ`-covariant, takes the
  constant value `c ≠ 0` on `x₀ L` for an open subgroup `L`, and vanishes off
  `P x₀ L`. Suppose also that `k ↦ ψ(k x₀)` is integrable. Then
  `∫_K ψ(k x₀) dμ ≠ 0`. On `P x₀ L` the value is `δ(q) c` with `δ(q) ≥ 0`, so
  the integrand is `c` times a nonnegative real function. That function equals
  `1` on the open set `{k | x₀⁻¹ k x₀ ∈ L}`, which contains `1`. This set has
  positive measure because `μ` is open-positive.
- `dualPairing_covariant`. For `h` induced from the dual and `f` induced from
  `σ`, the pointwise pairing satisfies
  `⟨h(q x), f(q x)⟩ = χ(q)^2 ⟨h(x), f(x)⟩`, because the contragredient action of
  `m q` cancels the action on `σ`.
- `exists_twist_comp_fixed` and `exists_compact_conj_fixed` are smoothness
  bookkeeping. A vector fixed by an open subgroup of `M` is fixed, after
  inflation along `m` and twisting by `χ`, by an open subgroup of `P`. That
  subgroup contains `P ∩ x₀ L x₀⁻¹` for a compact open subgroup `L` inside any
  prescribed open subgroup `U` of `G`. The second lemma uses the Library's
  `compactOpenSubgroupBasis`.
- `compactDoubleCosetSection_apply_mul` and
  `compactDoubleCosetSection_mem_of_ne_zero` specialize the Library's
  `compactDoubleCosetSection`. Its value on `x₀ L` is the prescribed vector, and
  it vanishes off `P x₀ L`.
- `exists_smoothDual_ne_zero` and `exists_dual_apply_ne_zero` give separation.
  Smooth functionals separate the vectors of a smooth representation when `M`
  has cofinal compact open subgroups, by the Library's
  `smoothBidual_injective_of_compact_cofinal`. A nonzero functional is nonzero at
  some vector.
- `integral_dualPairing_right_nondegenerate`. Take a nonzero induced function
  `f` and a point `x₀` with `f(x₀) ≠ 0`. Choose a smooth functional `λ` with
  `λ(f(x₀)) ≠ 0`. Choose `L` compact open, inside the stabilizer of `f`, with
  `λ` fixed by `P ∩ x₀ L x₀⁻¹`. Let `h` be the double-coset section through `λ`
  at `x₀`. The scalar `ψ(y) = ⟨h(y), f(y)⟩` is locally constant and
  `δ`-covariant. Its value on `x₀ L` is `λ(f(x₀))`, and it vanishes off
  `P x₀ L`. Hence `∫_K ψ(k x₀) dμ ≠ 0`. Invariance under right translation by
  `x₀`, from `hscalar`, gives `∫_K ψ(k) dμ ≠ 0`.
- `integral_dualPairing_left_nondegenerate` is the symmetric statement for a
  nonzero induced function from the dual. It uses a vector `v` with
  `h(x₀)(v) ≠ 0` and a double-coset section through `v`. No cofinality of
  compact subgroups of `M` is needed in this direction.
- `exists_integralDualEquiv`. Assume the induced representation of `σ` is
  admissible. Then there is a representation equivalence `E` from its smooth
  contragredient to the induction of the smooth dual of `σ`, characterized by
  `ℓ(f) = ∫_K ⟨(E ℓ)(k), f(k)⟩ dμ` for every functional `ℓ` and every `f`. The
  pairing is the Library's `integralBilinearPairing`. Its `G`-invariance is the
  scalar hypothesis applied to the covariant pointwise pairing. The two
  nondegeneracy results above feed the Library's `smoothInvariantPairingDuality`,
  and `E` is the inverse of the equivalence it produces.
- `integralDualEquiv_natural`. Let `Eσ` and `Eτ` be any equivalences with this
  integral characterization. Let `A` and `A'` be intertwiners of the inflated,
  twisted coefficient representations that are adjoint for the dual pairings.
  Then `Eσ (contragredientMap (smoothInducedMap P A) ℓ) = smoothInducedMap P A'
  (Eτ ℓ)`. Both sides are compared after applying `Eσ.symm`. By the
  characterization, both are functionals with the same integral formula. The
  proof uses only the characterization, not nondegeneracy.

## Scope

All results are general. The GL and refined-Levi specializations are in
`Langlands.Representation.Parabolic.NaturalInductionDualityFromScalar`. This
module proves no scalar integral identity.
