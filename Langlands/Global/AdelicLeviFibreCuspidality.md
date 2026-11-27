# Intrinsic cuspidality of Levi fibres

Let `F` be a number field and `G` an affine, locally finite-type connected reductive group scheme over `F` with a supplied `StandardParabolicFamily`. Fix a standard index `P` and a continuous function `f` on `G(𝔸_F)` invariant on the left under `U_P(𝔸_F)M_P(F)`. For every `g`, `isLeftInvariantUnder_leviFibre` gives left `M_P(F)` invariance of `m ↦ f(mg)` on `M_P(𝔸_F)`. If the normalized constant term of `f` vanishes for each standard index `Q < P`, then `leviFibreCuspidality` proves that the fibre has vanishing normalized periods along the unipotent radicals of all proper rational parabolics of `M_P`.

A proper parabolic of the actual Levi is the dynamic parabolic of a cocharacter. A rational conjugation moves the cocharacter into the standard chamber for the maximal split torus lifted to the Levi. The Levi's simple-root set is exactly the root subset of the ambient index `P`, so the resulting standard index is an ambient `Q ≤ P`. Equality would make the parabolic the entire Levi by the full-index endpoint, contradicting properness.

The dynamic unipotent radical of the conjugated cocharacter is the preimage in the Levi of the ambient standard radical of `Q`, by the all-test standard family restriction. The given geometric radical represents this dynamic radical after conjugation. `subgroupConstantTerm_leviFibre` identifies its normalized period with the corresponding ambient constant term, which vanishes by `Q < P`. Left `U_P(𝔸_F)` invariance removes the kernel factor of the radical projection in the integrand. Left `M_P(F)` invariance makes the fibre integrand descend to the rational radical quotient and permits the rational change of variables relating the original and conjugated periods.

This proves the fibre cuspidality comparison used in the induction of Mœglin–Waldspurger I.3.4, pp. 45–46.

- `moeglin-waldspurger-1995-cuspidal-components`, `ce20e97e0e7b5008124763a26598dd024c66c926069ca07e92aa24afe91999f1`, 05.3_pp_40_48_Cuspidal_components.pdf, I.3.4, pp. 45–46, induction on semisimple rank.
