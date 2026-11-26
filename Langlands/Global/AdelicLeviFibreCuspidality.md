# Intrinsic cuspidality of Levi fibres

A proper parabolic of the actual Levi is the dynamic parabolic of a cocharacter. A rational conjugation moves the cocharacter into the standard chamber for the maximal split torus lifted to the Levi. The Levi's simple-root set is exactly the root subset of the ambient index `P`, so the resulting standard index is an ambient `Q ≤ P`. Equality would make the parabolic the entire Levi by the full-index endpoint, contradicting properness.

The dynamic unipotent radical of the conjugated cocharacter is the preimage in the Levi of the ambient standard radical of `Q`, by the all-test standard family restriction. The given geometric radical represents this dynamic radical after conjugation. `subgroupConstantTerm_leviFibre` identifies its normalized period with the corresponding ambient constant term, which vanishes by `Q < P`. The original and conjugated periods are related by the rational change of variables for normalized quotient integrals, since the Levi fibre is rationally invariant. Thus `leviFibreCuspidality` establishes the all-proper-parabolic predicate `IsLeviCuspidal` for every fibre of a continuous relatively cuspidal input.

This proves the fibre cuspidality comparison used in the induction of Mœglin–Waldspurger I.3.4, pp. 45–46.

- `moeglin-waldspurger-1995-cuspidal-components`, `ce20e97e0e7b5008124763a26598dd024c66c926069ca07e92aa24afe91999f1`, 05.3_pp_40_48_Cuspidal_components.pdf, I.3.4, pp. 45–46, induction on semisimple rank.
