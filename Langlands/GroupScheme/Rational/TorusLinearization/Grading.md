# Weight grading of a split torus action

Helper module for the proof of `TorusVectorActionLinearizationStatement` (task 3be1ce22).
Internal machinery only.

Let `a : PointAction k K I n`. Over the splitting field `K`, `charAction` is the action of the
split torus with character group `I → ℤ` on the polynomial algebra `K[X]`, as a library
`Langlands.GroupScheme.CharacterAction.Action`. A character `τ` acts through the coordinate units
`unitsOf τ` and the splitting `σ`. The library coaction lemmas then give:

- `coact`: the coaction `K[X] → K[X][I → ℤ]`; `comp χ f` is the weight-`χ` component of `f`;
- `coact_comp`, `comp_comp`: components are homogeneous, and the projections are orthogonal
  idempotents; `sum_comp`: a polynomial is the sum of its components;
- `comp_pow_char`, `comp_pow_char_smul`, `comp_pow_char_eq_zero`: in characteristic `p`, the
  components of `f ^ p` sit in weights `p • χ`, and there they equal `(comp χ f) ^ p`;
- `charOf τ`: the character with coordinate units `τ` (`unitsOf_charOf`, `map_charOf`);
- `pullK t`: pullback of polynomials over `K` along a point over a `K`-algebra; `pullK_map`
  compares it with `pull`. `pullK_σ` is the eigenvalue formula
  `pullK (σ τ) h = Σ_χ charOf τ χ • comp χ h`.
