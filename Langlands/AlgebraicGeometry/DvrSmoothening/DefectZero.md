# Points of defect zero lie in the smooth locus

`defectZeroSmoothAtStatement` proves the Library proposition
`Langlands.AlgebraicGeometry.DvrSmoothening.DefectZeroSmoothAtStatement`.

- `isDomain_localization_of_isSmoothAt`: a localization of a finitely presented algebra over a
  discrete valuation ring at a prime where it is smooth is a domain. The proof passes to a basic
  open `D(g)` on which the algebra is smooth; the stalk there is a regular local ring by the
  Library's `AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing`
  (module `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing`),
  hence a domain by `IsRegularLocalRing.isDomainFLT` (module
  `Langlands.AnthropicFLT.Theorems.Thm_IsRegularLocalRing_isDomain`). This stalk is identified with
  the localization at the prime (`Spec.stalkIso` and localization of a localization).
- `isSmoothAt_of_free_tensor`: let `P → A` be a surjection onto an algebra over a discrete
  valuation ring `R` from a formally smooth, finitely presented `R`-algebra `P` with finite free
  differentials, and `φ : A → R'` a point with values in a discrete valuation ring such that
  `R' ⊗_A Ω_{A/R}` is free and `A` is smooth over `R` at the generic point `ker (A → Frac R')`.
  Then `A` is smooth over `R` at the closed point of `φ`. Proof: choose relations `f₁, …, f_c` of
  `A` with independent differentials at the closed point, with `c` at least the drop in dimension
  of the differentials from `P` to `A` there (`exists_relations_linearIndependent`); then
  `C = P ⧸ (f)` is smooth at the closed point, `C` localized there is a domain, and comparing ranks
  at the closed point and at the generic point of `R'` shows that `C → A` is an isomorphism after
  localization (the kernel vanishes generically by `ker_eq_bot_of_finrank_le`, hence everywhere in
  the domain). So `A` is smooth at the closed point of `φ`.
- `defectZeroSmoothAtStatement`: the statement, since defect zero means that `R' ⊗_A Ω_{A/R}` is
  free (`TorsionLength.torsionLength_eq_zero_iff_free`).

This is Bosch–Lütkebohmert–Raynaud, *Néron Models*, §3.3, Lemma 1 (printed p. 65), in the form
for points of ramification index one (§3.6, printed p. 79).
