# Transport along Lie algebra equivalences

Let `e : L ≃ₗ⁅ℂ⁆ L'` and `π : L →ₗ⁅ℂ⁆ End(V)`. Put `π' = π ∘ e⁻¹`, and let
`Φ = LieEnvelopingEquiv.enveloping e : U(L) ≃ U(L')` (Library).

* `envelopingAction_comp_enveloping`: `π'(Φ u) = π(u)`. Both sides are algebra maps out of
  `U(L)` that agree on generators (`UniversalEnvelopingAlgebra.hom_ext`).
* `mem_center_enveloping_symm`: `Φ⁻¹` maps the center into the center, since `Φ` is a
  multiplicative bijection.
* `mem_center_enveloping`: likewise `Φ` maps the center into the center.
* `hasInfinitesimalCharacter_comp`: if central elements act by scalars under `π`, they do so
  under `π'`.
* `isMaximallyFaithful_of_comp`: if `π'` is maximally faithful, so is `π`. Apply `Φ⁻¹` to the
  membership of `Φ u` in the ideal for `π'`. By span induction, `Φ⁻¹` maps that ideal into the
  ideal for `π`: generators go to central elements acting by `0`, and left multiples go to left
  multiples.
* `hasInfinitesimalCharacter_of_comp`: conversely, if central elements act by scalars under `π'`,
  then a central `z ∈ U(L)` acts under `π` as the central element `Φ z` acts under `π'`.
* `isMaximallyFaithful_comp`: if `π` is maximally faithful, so is `π'`. Apply
  `isMaximallyFaithful_of_comp` to `e⁻¹` and `π'`, using `π' ∘ (e⁻¹)⁻¹ = π`.
