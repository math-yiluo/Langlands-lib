# The separably closed case of CGP Proposition C.1.6

This module is part of the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6 (printed
pp. 586–588). It covers the case where `k` is separably closed, `G` is
pseudo-reductive and corepresented, and `P = P_G(χ)`. It is assembled from
Library statements and helper modules; the inputs stated separately in the
Library are explicit hypotheses.

## `corepresentedDynamicParabolicQuotientDVRLifting_of_isSepClosed`

Conclusion: `CorepresentedDynamicParabolicQuotientDVRLifting k` (from
`PseudoParabolicQuotientCorepresentedReduction`) for a separably closed field
`k`. That is the DVR lifting property in `algOver` form, for every quotient `q`
of a corepresented pseudo-reductive `G` by `P_G(χ)`.

Hypotheses:
- the Library statements `UnipotentRadicalExistenceStatement`,
  `UnipotentRadicalQuotientStatement` and
  `DynamicFlagQuotientExistenceStatement`;
- `hsep : PseudoReductiveSeparableExtensionStatement.{u}` (CGP 1.1.9(1),
  separable algebraic case);
- `hc : PseudoReductiveRationalUnipotentPointStatement.{u}`;
- `hrat`: nonzero finitely generated geometrically reduced `k`-algebras in
  `Type u` have `k`-points. This is the Library statement
  `SeparablyClosedRationalPointStatement` specialized to the field `k`.

Proof as implemented, with `Ω = AlgebraicClosure k`.
1. `G_Ω` is smooth, affine and connected
   (`connectedSpace_baseChange_of_smooth_affine`). The radical statements give
   the unipotent radical `i : U ⟶ G_Ω` and an fppf quotient `π : G_Ω ⟶ H` with
   kernel `U` and `H` pseudo-reductive. Then `H` is connected reductive, since
   `hsep` applied to `Ω → AlgebraicClosure Ω` (separable, `Ω` perfect) gives
   trivial geometric unipotent radical.
2. Put `λ = opposite χ` and `χ'' = opposite (λ_Ω ≫ π)`. Then
   `opposite χ'' = λ_Ω ≫ π` (`powerHom_neg_one_comp_powerHom_neg_one`), and
   `χ'' = χ_Ω ≫ π` (`baseChangeCocharacter_powerHom`).
3. `DynamicFlagQuotientExistenceStatement` for `(H, χ'')` gives a proper `Q₀`
   with exact fibers and local sections. The parabolic `P_H(χ'')` is
   represented by a smooth (`dynamicSmooth`) closed subgroup whose structure
   map is surjective (`surjective_hom`, the unit is a section). Worker 254's
   `Dynamic.flat_surjective_quasiCompact_of_localSections` then makes `π₀`
   flat, surjective and quasi-compact.
4. The base change `q_Ω` is flat, surjective and quasi-compact, and its fibers
   are the cosets of `P(χ_Ω)` (`dynamicParabolicQuotient_fiber_baseChange`).
   `exists_comparison_desc` then gives `φ : Q_Ω ⟶ Q₀` with
   `q_Ω ≫ φ = π ≫ π₀`.
5. `hker_of_kernel` with `hc` (for the radical `U`) gives the kernel condition.
   `exists_algHom_tensor_ne_zero` with `hrat` gives the density hypothesis; it
   needs `B` to be a domain (`isDomain_of_smooth_connected`) and geometrically
   reduced (`isGeometricallyReduced_of_smooth`), both from Worker 254's
   `CorepresentedSmoothGeometry`.
6. Worker 254's `isDomain_tensor`, `isDiscreteValuationRing_tensor` and
   `isFractionRing_tensor` (for the purely inseparable extension `Ω/k`) make
   `Ω ⊗ R` a DVR with fraction field `Ω ⊗ Frac R`.
7. `exists_extension_of_comparison` concludes.
