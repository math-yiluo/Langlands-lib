# Lifting along square-zero thickenings of affine schemes

Namespace `Langlands.AlgebraicGeometry.SmoothLifting`. This module proves the
square-zero case of `SmoothThickeningLiftingStatement`.

## The Čech argument (`exists_lift_of_charts`)

Hypotheses:
- `f` is smooth and `I` is a square-zero ideal of `C`;
- `x₀ ≫ f = Spec.map (mk I) ≫ s`;
- `ch : Fin n → Chart f I x₀ s` are charts whose elements `gᵢ` generate the
  unit ideal.

Write `Rᵢ = C[1/gᵢ]`, `Rᵢⱼ = C[1/(gᵢ gⱼ)]`, `Rᵢⱼₖ = C[1/(gᵢ gⱼ gₖ)]`. Lifts
on these rings are compared through their chart representatives
(`Chart.repL`). The steps:

1. **Local lifts.** `Chart.exists_lift` gives a lift `xᵢ` on `Rᵢ`.
2. **Pair corrections.** For each pair `(i, k)`, `Chart.exists_extension_loc`
   in chart `i` gives a lift `zᵢₖ` on `Rᵢ` whose restriction to `Rᵢₖ` has
   representative `xᵢ + gₖᴺ (xₖ - xᵢ)`. One `N` works for all pairs: it is
   the maximum of the finitely many thresholds.
3. **Triple relations.** For each triple `(i, j, k)`, work on `Rᵢⱼ` in
   chart `i` with the two lifts
   `L = xᵢ + (xⱼ - xᵢ) + (zᵢₖ - xᵢ)` and
   `R = xᵢ + (zⱼₖ - xᵢ) + gₖᴺ (xⱼ - xᵢ)`.
   - Their restrictions to `Rᵢⱼₖ` agree. `Chart.push_pair` transports the
     two pair relations to `Rᵢⱼₖ`. The relation for `zⱼₖ` lives in chart
     `j` and is moved to chart `i` by `Chart.comb_eq`.
   - `Chart.exists_torsion_loc` then gives
     `gₖᴹ ((xⱼ + zᵢₖ - xᵢ) - (zⱼₖ + gₖᴺ (xⱼ - xᵢ))) = 0` on representatives
     over `Rᵢⱼ`, with one `M` for all triples.
4. **Partition of unity.** The powers `gₖ^(N+M)` generate the unit ideal
   (`Ideal.span_pow_eq_top`). Choose `aₖ` with `∑ aₖ gₖ^(N+M) = 1`
   (`Ideal.mem_span_range_iff_exists_fun`).
5. **Corrected lifts.** `Yᵢ = xᵢ + ∑ₖ aₖ gₖᴹ (zᵢₖ - xᵢ)` is a lift on `Rᵢ`
   (`Chart.comb`).
6. **Agreement on overlaps.** The restriction of `Yⱼ` to `Rᵢⱼ` is the
   chart-`j` combination of the restricted lifts, which equals the chart-`i`
   combination by `Chart.comb_eq`. The triple relations and
   `∑ aₖ gₖ^(N+M) = 1` then reduce the equality of representatives to a
   ring identity.
7. **Gluing.** `exists_glue` glues the `Yᵢ`, and `isLift_of_cover` shows the
   result solves the lifting problem.

## Charts and the square-zero theorem

- `exists_chart_at`: every point `q` of `Spec C` lies in the domain of a
  chart.
  - The point comes from a point `p` of `Spec (C ⧸ I)`, because
    `Spec (C ⧸ I) → Spec C` is surjective.
  - Affine opens form a basis (`Scheme.isBasis_affineOpens`). This gives
    `V ∋ f (x₀ p)` and `U ∋ x₀ p` with `U ⊆ f ⁻¹ᵁ V`.
  - Basic opens form a basis (`PrimeSpectrum.isBasis_basic_opens`). This
    gives `g₁` with `q ∈ D(g₁) ⊆ s⁻¹ V` and `g₂` with `p ∈ D(ḡ₂) ⊆ x₀⁻¹ U`.
  - The chart element is `g₁ g₂`.
- `exists_charts`: the chart elements over all points generate the unit
  ideal (a maximal ideal containing them would contradict the chart at its
  own point). By `Ideal.span_eq_top_iff_finite`, finitely many suffice,
  reindexed by `Fin n`.
- `exists_lift_sqZero` is the square-zero case for a surjective
  `q : C ⟶ D` with square-zero kernel:
  - transport `x₀` along `D ≅ C ⧸ ker q` (`RingHom.quotientKerEquivOfSurjective`);
  - apply `exists_charts` and `exists_lift_of_charts`;
  - transport back.

## Provenance

This follows the structure of the proof of Stacks Project, More on
Morphisms, Lemma 37.11.7 (Tag 02H6): local lifts exist, and the
obstruction to gluing vanishes on an affine scheme. The vanishing of the
first cohomology of the quasi-coherent torsor group is replaced here by an
explicit Čech computation with a partition of unity on a finite standard
cover. Worker 496 wrote the Lean code and this description.
