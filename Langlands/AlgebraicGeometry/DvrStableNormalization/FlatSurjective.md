# Flatness and surjectivity of the normalization model

Worker 6.

- `flat_of_injective_of_isUnit`: an algebra over a DVR that embeds into an algebra in which a
  uniformizer is a unit is torsion-free, hence flat
  (`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`).
- `flat_of_injective_generic`: a scheme `Y` over `Spec R` is flat if some `τ : Z → Y` with
  `τ ≫ f` factoring through `Spec (FractionRing R)` is injective on sections over every affine open
  (`HasRingHomProperty.of_iSup_eq_top`).
- `flat_source`: `source X` is flat over `Spec R`; `toNormalization` is scheme-theoretically dominant
  (its kernel is `⊥`, Mathlib `ker_toNormalization`), so sections inject into generic sections.
- `surjective_map`: for flat `X`, `map X` is surjective: it is integral, hence closed, and its image
  contains the generic fibre, which is dense because flat morphisms are generalizing.

Conrad's appendix (p.28 and the A.4 argument) notes flatness of the torsion-free normalization;
these lemmas implement that remark.
