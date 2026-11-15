# Fixed points in stable cosets over the maximal unramified extension

Module `Langlands.Geometry.Building.UnramifiedTraceCosetDescent`, namespace
`Langlands.Geometry.Building.MaximalUnramified`.

## Setting

`F` is a nonarchimedean local field. `K = F^ur` is the Library's `inertiaFixedField F`, and
`valuation F` is the Library's valuation on `K` (`MaximalUnramified.valuation`, module
`Langlands/Geometry/Building/MaximalUnramifiedValuation.lean`). For an intermediate field `E`
of `SeparableClosure F / F`, `LocalUnramified.integers F E` is the Library's ring of integers of
`E` (the integral closure of `𝒪[F]` in `E`). `GaloisLevel F E₀` is the finite Galois level of
module `UnramifiedFiniteGaloisLevel`: a finite Galois `E ≤ K` with a surjection
`res : Aut(K/F) → Gal(E/F)` whose kernel fixes `E₀` and has fixed field `E`.

The module is internal infrastructure for the forward direction of
`UnramifiedZeroJumpFieldComparisonStatement` (module `UnramifiedZeroJumpForwardDescent`). It
has no direct counterpart in the literature. The main lemma is the standard argument that
Hilbert 90 for a vector group still works when the coefficients are restricted to a
Galois-stable subring that contains an element of trace one.

## Declarations

### `valuation_inclusion_le_one` and `valuation_inclusion_eq_one_of_isUnit`

For `E ≤ K` (`hE : E ≤ inertiaFixedField F`) and `x` in the integer ring of `E`, the image
`IntermediateField.inclusion hE x` of `x` in `K` has `valuation F` at most one. If `x` is a unit
of the integer ring, the valuation is exactly one.

Proof: `x` is integral over `𝒪[F]`, hence so is its image in `K`. The Library lemmas
`LocalUnramified.mem_integers_iff`, `fixedFieldIntegers_eq` and `mem_valuationSubring_iff` turn
integrality over `𝒪[F]` into membership in the valuation subring of `valuation F`. For a unit
`u`, both `u` and `u⁻¹` have valuation at most one and their product has valuation one, so
neither valuation can be strictly less than one.

### `GaloisLevel.inclusion_galoisAction` and `GaloisLevel.inclusion_fixed`

For a Galois level `L` and `σ ∈ Aut(K/F)`:

- on the integer ring of `L.E`, the Library action `LocalUnramified.galoisAction F L.E (L.res σ)`
  followed by the inclusion into `K` equals the inclusion followed by `σ`;
- if `L.res σ = 1`, then `σ` fixes the image of every element of `L.E` in `K`.

Both follow from the field `res_apply` of `GaloisLevel` (compatibility of `res` with the
inclusion `E ⊆ K`).

### `exists_fixed_mul_of_unitSquare_scaling`

Data and hypotheses:

- a group `P` with an action `act : Aut(K/F) →* MulAut P`;
- a subgroup `B ≤ P` with `act σ (B) ⊆ B` for every `σ`;
- a map `e : P → K^m` (written `Fin m → K`) that on `B` is additive
  (`e (x y) = e x + e y`), injective (`e x = 0 → x = 1`) and semilinear
  (`e (act σ x) = σ (e x)` coordinatewise);
- `hsq`: for every unit `c` of `K` with `valuation F c = 1` and every `x ∈ B` there is `y ∈ B`
  with `e y = c² • e x`;
- a finite-dimensional intermediate field `E₀` of `K / F`;
- `w₀ ∈ P` fixed by every `σ` in the fixing subgroup of `E₀`, with `w₀⁻¹ · act σ w₀ ∈ B` for
  every `σ`.

Conclusion: there is `b ∈ B` such that `w₀ b` is fixed by every `σ ∈ Aut(K/F)`.

In words: the cocycle `σ ↦ w₀⁻¹ σ(w₀)` with values in `B` is a coboundary, so the coset `w₀ B`
contains a fixed point. The hypotheses do not say that `e(B)` is a `K`-subspace. They only give
stability under multiplication by squares of units of valuation one.

Proof.

1. `nonempty_galoisLevel F E₀` gives a Galois level `L`: a finite Galois `E ≤ K` with
   `res : Aut(K/F) → Gal(E/F)` surjective and `ker res` contained in the fixing subgroup of
   `E₀`. Let `ι` be the ring map from the integer ring `O_E` of `E` to `K`.
2. Let `P_ring ⊆ O_E` be the set of `l` such that for every `x ∈ B` some `y ∈ B` has
   `e y = ι(l) • e x`. Using additivity of `e` on `B`, `e 1 = 0` and `e x⁻¹ = -e x`, this is a
   subring of `O_E`.
3. `P_ring` is stable under `Gal(E/F)`. For `g = res σ` (surjectivity of `res`) and `l ∈ P_ring`,
   apply the defining property of `l` to `act σ⁻¹ x` and transport the result back with `act σ`,
   using semilinearity of `e` and `GaloisLevel.inclusion_galoisAction`.
4. `P_ring` contains the square of every unit of `O_E`: the image `c` of a unit has valuation
   one by `valuation_inclusion_eq_one_of_isUnit`, so `hsq` applies.
5. The published `LocalUnramified.exists_trace_eq_one_of_sq_mem` (module
   `Langlands/GroupScheme/GaloisStableSubringTrace.lean`) gives `θ ∈ P_ring` with
   `∑_{g ∈ Gal(E/F)} g(θ) = 1`.
6. The published `TraceCocycleDescent.exists_fixed_mul_of_trace_eq_one` (module
   `Langlands/GroupScheme/TraceCocycleDescent.lean`) is applied with `Δ = Aut(K/F)`,
   `Γ = Gal(E/F)`, the homomorphism `res` with a set-theoretic section `s`
   (`Function.surjInv`), `W = K^m` and the element `ι(θ)` of `K`. Its hypotheses hold:
   - `ι(θ)` is fixed by `ker res` (`GaloisLevel.inclusion_fixed`);
   - `∑_γ s(γ) • ι(θ) = 1` is the image of step 5 under `ι`, rewritten with
     `GaloisLevel.inclusion_galoisAction`;
   - multiplication by `σ(ι(θ))` preserves `e(B)` because `res σ (θ) ∈ P_ring` by step 3;
   - `w₀` is fixed by `ker res` because `ker res` fixes `E₀`.

   Its conclusion is the claim.

The proof needs `set_option synthInstance.maxHeartbeats 400000` to synthesize the scalar
action of `K` on `Fin m → K`.
