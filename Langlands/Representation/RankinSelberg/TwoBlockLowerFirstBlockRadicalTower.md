# The lower mixed radical quotient tower

This internal support for JPSS (1983), Section 4.9 equation (2), printed page 416,
retains the actual mixed and lower mixed subgroups and every supplied rectangular
additive Haar measure. The coefficient is that measure's integral-cube mass.

For every canonical p-adic field and every positive two-block shape, write
`R` for the lower rectangular matrix space, `M` for the block-diagonal mixed
subgroup, and `L` for the actual lower mixed subgroup. Let `μR` be any supplied
additive Haar on `R`, and let `c = μR {Z | ∀ i j, Z i j ∈ O}`. The fixed measures
`mixedHaar` and `lowerMixedHaar` are the measures already constructed in the
companion measure modules. In particular the latter has integral subgroup mass
one and is independent of `μR`.

The proposition abbreviation `RadicalTowerStatement` says that the actual
`radicalKernel` composed with a lower mixed quotient measure is `c` times the
mixed quotient measure, and that this identity restricts to every pair of
matching integer determinant slices. The theorem `radicalTower` proves this
proposition whenever the two quotient measures are compatible with the same
fixed ambient Haar and the indicated subgroup measures. Its `k = 0`
specialization uses exactly the zero outer slice required by equation (2).

The implemented proof proceeds as follows.

1. `lintegral_mixedHaar_radical` converts the right-coordinate integral
   `∫R ∫M ψ(a R(Z))` to the published left coordinates. Commuting the diagonal
   and radical factors gives a linear change preserving the supplied rectangular
   Haar: both diagonal factors have determinant norm one. Tonelli and the exact
   product measure normalization give `c ∫L ψ(l)`.
2. `lintegral_radicalFiberPoint_quotientAverageReal` applies this identity to a
   nonnegative compactly supported continuous ambient test. Integrability along
   each closed subgroup allows its real orbital average to be expressed as a
   nonnegative integral. This gives the exact orbital-average identity at every
   representative.
3. `lintegral_radicalKernel_comp_quotientAverageReal` integrates that identity
   against any outer measure, using the published kernel representative law.
   `radicalKernel_comp` then uses compatibility of both quotient measures to
   compare their integrals on orbital averages. Positive compact lifting supplies
   every nonnegative compact continuous quotient test as such an average.
   Before applying regular-measure uniqueness, the proof establishes compact
   finiteness of the composite by dominating each compact-set indicator with
   one of these tests. The resulting finite scalar multiple and composite are
   regular; equality follows from their compact continuous tests.
4. `radicalKernel_comp_restrict` proves the matching-slice restriction directly
   on measurable sets. Since the lower radical has determinant one, each fiber
   is wholly in the determinant slice of its base representative. Consequently
   evaluating a fiber on `A ∩ MQk` equals the indicator of `LQk` times its
   evaluation on `A`. Integrating this equality proves the restricted identity
   without introducing another coefficient.

This is derived measure-theoretic support for JPSS (1983), Section 4.9,
equation (2) and the following definition of `L`, printed page 416. The kernel
formulation, explicit normalization and regular-measure uniqueness argument are
internal precision, rather than a claim that JPSS states these lemmas. The proof
reuses the published positive-lifting and recursive quotient integration results.
This pair establishes the radical measure tower; the analytic conclusions and
the first-block tower for equation (8) are separate obligations.
