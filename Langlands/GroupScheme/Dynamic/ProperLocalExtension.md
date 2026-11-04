# Extending field points over valuation rings, and points of local schemes in opens

This module is an internal helper for the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6. It is used where
that proof extends the point of the proper reductive flag variety over the
base-changed DVR, and where it checks that the extended point lands in a
translate of the open cell. The notation `algOver Ω A` and `algOverHom` is from
`Langlands.GroupScheme.Dynamic.FieldPointBasicOpen`.

- `exists_extension_of_isProper X A K' x`: let `X` be proper over `Spec Ω`,
  `A` a valuation ring that is an `Ω`-algebra, and `K'` a field of fractions of
  `A` (`IsFractionRing A K'`) whose `Ω`-structure factors through `A`. Then
  every point `x : Spec K' ⟶ X` over `Ω` extends to `xA : Spec A ⟶ X` with
  `Spec (A → K') ≫ xA = x`. This is the existence half of Mathlib's valuative
  criterion. Mathlib's `UniversallyClosed.eq_valuativeCriterion` turns
  universal closedness of the proper structure map into
  `ValuativeCriterion.Existence`, which is applied to the evident square.
  Unlike the Library's `PseudoComplete.exists_extension_of_isProper`, the
  fraction field is any model `K'` rather than `FractionRing A`. That lets the
  C.1.6 argument use `Ω ⊗[k] Frac R` directly.
- `range_subset_of_residue A y hC h`: let `A` be a local `Ω`-algebra and
  `y : Spec A ⟶ Y`. If the point `Spec (residue field) → Spec A → Y` lands in
  an open `C`, then all of `y` lands in `C`. The point of `Spec` of the residue
  field maps to the closed point of `Spec A` (`IsLocalRing.comap_closedPoint`).
  Every point of `Spec A` specializes to the closed point, and opens are stable
  under generization (`Specializes.mem_open`).
