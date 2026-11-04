# Gradings and the comparison map of a homomorphism out of a base change

This module is an internal helper for the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6. Everything here is
derived from Library lemmas; no external result is used. The notation is that of
`Langlands.GroupScheme.Dynamic.BaseChangeCoordinates`. `ν` is a cocharacter of
`G = Spec B` over `k`, and `π : G_Ω ⟶ H` is a homomorphism to an affine
`Ω`-group.

- `Dynamic.AffineChart.pointRing_conj χ x u`: for an affine group `H` with
  cocharacter `χ`, a point `x` over `Spec A` and a unit `u` of `A`, the
  classifying map of `χ(u) x χ(u)⁻¹` is the coaction, then the coefficient map
  of `x`, then evaluation at `u`. This is the affine-chart analogue of the
  Library's `Corepresented.pointRing_conj`, with the same proof:
  `Dynamic.lift_comp_orbit`, `laurentAt_comp_laurentPoint` and
  `AffineChart.pointRing_laurentPoint_comp_orbit`.
- `testOverHom_comp_unitPoint u`: the unit point `u` of `𝔾_{m,Ω}` over `Spec A`,
  transported to `𝔾_{m,k}` through `Gm.baseChangeIso` and the pullback point
  equivalence, is the unit point `u` of `𝔾_{m,k}`. The proof compares units with
  `Gm.pointsEquiv` and the Library's `Gm.baseChangeUnitsEquiv_baseChangeIso_inv`.
- `basePoint_conj ν z u`: conjugation by the base-changed cocharacter
  `Dynamic.baseChangeCocharacter (scalarMap k Ω) ν` at the unit `u` corresponds
  to conjugation by `ν` at `u` on underlying `k`-points. This holds because the
  pullback point equivalence is multiplicative, and by the Library's
  `baseChangePointsEquiv_baseChangeCocharacter`.
- `laurentEmbedding B Ω : B → (Ω ⊗[k] B)[T, T⁻¹]`: `b ↦ C (1 ⊗ b)`.
  `classifying_bcPoint_laurentEmbedding`: the classifying map of its base change
  is the constant embedding `C`. This is checked on pure tensors.
- `coeff_classifying_conj ν m n`: let `t` be the coordinate unit `T` of
  `(Ω ⊗[k] B)[T, T⁻¹]`. Conjugate the point `bcPoint (laurentEmbedding)` by the
  base-changed cocharacter at `t`. The `n`-th coefficient of its classifying
  map at `m ∈ Ω ⊗[k] B` is the base-changed weight component
  `(Ω ⊗ weightPart n) m`. Proof: by `basePoint_conj`, the Library's
  `Corepresented.pointRing_conj` and `laurentCoeffMap_comp_laurentC_comp_laurentEval`,
  the underlying `k`-point sends `b` to `∑ₙ (1 ⊗ (c b)ₙ) Tⁿ`. Then induct on `m`.
- `lTensor_weightPart_comparisonMap ν π f n` (equivariance): give `H` the
  cocharacter `ν_Ω ≫ π`. Then
  `(Ω ⊗ weightPart n)(comparisonMap π f) = comparisonMap π ((c_H f)ₙ)`.
  Proof: compute the classifying map of `π` applied to the conjugated point of
  the previous item in two ways. `π` is a homomorphism, so conjugation commutes
  with `π`. One way, `AffineChart.pointRing_conj` on `H` together with
  `classifying_bcPoint_laurentEmbedding` gives coefficients
  `comparisonMap π ((c_H f)ₙ)`. The other way, `pointRing_comp_eq` together with
  `coeff_classifying_conj` gives `(Ω ⊗ weightPart n)(comparisonMap π f)`.
