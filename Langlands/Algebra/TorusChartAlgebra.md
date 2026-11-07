# The universal Hopf point of `μ_m^r` and its twisting action

Author: Worker 1421.

This module fixes the algebraic data of the finite-level parameter scheme used
in the chart construction of task `45ac6e52-a4d8-4414-91f1-03c3be35223e`.
`R` and `A` are commutative rings in universe `u`, with `A` a finitely
presented `R`-Hopf algebra (the coordinate ring of the ambient group), `r` a
finite index type and `m > 0`. It is an internal module.

- `W R A r m`: Worker 950's `FiniteBialgebraHom.HomAlgebra R A R[(ℤ/m)^r]`,
  which represents homomorphisms `μ_m^r → Spec A`.
- `univ R A r m : A →ₐ[R] W[(ℤ/m)^r]`: the universal Hopf point, transported to
  group-algebra form by `HopfPointBridge.toGroupAlgebra`. `isHopfPoint_univ`.
- `univ_point`: the Hopf point classified by `g : W → C` under Worker 950's
  `homEquiv` is `mapAlgHom g ∘ univ`.
- `mapAlgHom_twistHom_comp_univ`: twisting the representing algebra by
  `HopfPointTwist.twistHom γ` twists the universal point by `mapDomain γ`.
- `pointOf g := mapAlgHom g ∘ univ`, for any `C`-point `g` of `W`
  (`isHopfPoint_pointOf`).
- `pointOf_comp_twistHom`: `pointOf (g ∘ twistHom γ) = mapDomain γ ∘ pointOf g`.
- `twist_injective_of_surjective`: over a nonzero `C`, if `pointOf g` is a
  closed immersion (surjective `scalarExt`) and two twists of `g` have the same
  Hopf point, the twisting automorphisms are equal
  (`HopfPointKernel.eq_refl_of_mapDomain_comp_eq`). This gives freeness of the
  twisting action on the closed-immersion locus.
