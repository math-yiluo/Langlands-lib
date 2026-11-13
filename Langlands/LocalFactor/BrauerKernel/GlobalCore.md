# The epsilon product at the distinguished place of a global Brauer relation

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. It is the analytic heart
of Deligne's global argument (P. Deligne, *Les constantes des équations fonctionnelles des
fonctions L*, 1973, proof of Lemma 4.12, with the auxiliary twist of §4.13–4.16). A global relation
among Hecke characters gives a product of Hecke L-functions whose functional equation has
trivial L-factors. If the characters are twisted by a sufficiently ramified global character
`α` that is trivial at the distinguished place `v`, every local epsilon product away from `v` is
`1`. So the local epsilon product at `v` is `1`.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`.

## Helpers

- `under_eq_of_liesOver`: a finite place lying over `z` restricts to `z`.
- `continuous_brauerEpsilon`: the epsilon factors of the published Brauer product package
  (`RelativeWeilEngine.hasGlobalEquation_brauerProduct`) are continuous in `s`. Each finite
  epsilon factor is differentiable and nonzero (`finiteEpsilon_differentiable`,
  `finiteEpsilon_ne_zero`), so products, inverses and integer powers are continuous.
- `infiniteComponent_twist_eq`: let `E/k` be totally real and Galois, let `α` be trivial at
  infinity, and let the reciprocity character of `Θ` be trivial on the idele classes of `E`.
  Then `(α ∘ N) · ‖·‖^t · Θ` has the archimedean components of `‖·‖^t`. Proof:
  `normComp_infiniteComponent_eq_one` handles `α ∘ N`, and the unit `ArchimedeanTrivial` handles
  `Θ`.

## Main result

`exists_twist_placeEpsilonRatioProduct_eq_one`. Hypotheses:

- `hCC`: normalized local reciprocity families exist (`CommonClosureReciprocityExistence`);
- `hsq`: `ExtensionWeilTransferReciprocityStatement`;
- `hM`: `LocalRelativeWeilMapExistenceStatement`;
- local invariant families `I` and a class family `c` with the four compatibilities;
- a totally real Galois extension `E/k`;
- intermediate fields `K i` (`i : Fin n`) with nonzero weights `r i`, exponents `t_j i`, and
  Hecke characters `Θ_j i` whose reciprocity characters are trivial on the idele classes of `E`;
- `hrel`: for every Hecke character `α` of `k`, the characters
  `(α ∘ N) · ‖·‖^{t_j i} · Θ_j i` satisfy the global relation
  `Σ_i r_i Ind([τ ∘ Λ₁ i] - [τ ∘ Λ₂ i]) = 0`;
- `hdim`, the balancing of types: `Σ_i r_i [K i : k] ([t₁ i = τ] - [t₂ i = τ]) = 0` for every
  `τ`.

Conclusion: for every finite place `v` there are a nontrivial additive character `ψv` of `k_v`,
Haar measures, and a Hecke character `α` of `k` such that `α_v = 1`, `α` is trivial at infinity,
and `placeEpsilonRatioProduct` of the place `v` (unit `PlaceEpsilon`) for these characters is
`1`.

Proof, following Deligne:

1. Choose normalized families `eC z` at every finite place (`hCC`). Choose the standard global
   additive character with its canonical components and self-dual measures
   (`exists_associatedAdditiveInputs`). Take archimedean data of the trivial character
   (`nonempty_heckeArchData`) for the real scales.
2. Let `T` be the finite set of places `z ≠ v` below a place of some `K i` that is ramified over
   `k` or at which some `Θ_j i` is ramified (`finite_setOf_ramificationIdx_ne_one`,
   `exists_finset_isUnramifiedAt`). At each `z`, bound the conductors of `‖·‖^t · Θ` above `z`
   by `Kb z`. The unit `PlaceEpsilon` (`exists_bound_placeEpsilonRatioProduct_eq_one`) gives a
   depth `Bd z` beyond which a twist makes the epsilon product at `z` trivial.
3. The proved `ramifiedTwistIsolation` gives `α` of finite order with `α_v = 1`, trivial at
   infinity, and nontrivial on the principal units of level `Bd z` at each `z ∈ T`. So its
   conductor exponent at `z` exceeds `Bd z` (`lt_multiplicativeConductor_quasicharacterBase`).
4. Let `Λ_j i = (α ∘ N) · ‖·‖^{t_j i} · Θ_j i`. The unit `GlobalLocalRelation` restricts `hrel α`
   to the local relation at every finite place. The archimedean data of each `Λ_j i` is
   `normPowerArchData`. The epsilon supports are finite (`exists_finset_finiteEpsilon_eq_one`).
   Let `B` be `{v}`, `T`, and these supports.
5. `hasGlobalEquation_brauerProduct` (with exponent `0` on the base character) gives the global
   functional equation of the product. Its L-factors and dual L-factors are `1` wherever
   nonzero: unit `PlaceEuler`, with the dual relation `localPlaceRelation_inv`. Its archimedean
   blocks have the germ of `1` (unit `BrauerArch`). By the unit `GlobalEpsilonIdentity`, the
   product of its epsilon factors over `B` at `s = 0` is `1`.
6. At `s = 0` each epsilon factor is `placeEpsilonRatioProduct`
   (`prod_finiteEpsilon_eq_placeEpsilonRatioProduct`). It is `1` at every `z ∈ B` other than
   `v`: for `z ∈ T` by the ramified bound of step 2, and for `z ∉ T` by the unramified lemma
   `placeEpsilonRatioProduct_eq_one_of_unramified`. Hence the factor at `v` is `1`.
