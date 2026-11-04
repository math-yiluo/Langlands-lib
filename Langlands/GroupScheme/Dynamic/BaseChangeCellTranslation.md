# Translation into the opposite cell through a homomorphism out of a base change

This module is an internal helper for the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6. It is the
counterpart of `Langlands.GroupScheme.Dynamic.CellTranslation` for the
comparison quotient over an algebraic closure. In CGP's proof one `g ∈ G(k)`
moves both the generic point and the point of the reductive quotient
`G''/P''` into the respective open cells. This module gives the condition on
`g` coming from the second point. It is derived from Library results and the
other helper modules; nothing is quoted from the source.

Notation: `G = Spec B` is corepresented over a field `k`, `Ω` a field with
`Algebra k Ω`, and `bcPoint F e Ω A φ` the point of `G_Ω` over `Spec A` that is
the base change of the `k`-point `φ : B → A` (`BaseChangeCoordinates`).

## Naturality of base-changed points

- `algOverHom_comp_bcPoint ψ φ`: for an `Ω`-algebra map `ψ : A → A'`,
  `Spec ψ ≫ bcPoint φ = bcPoint (ψ ∘ φ)`. Proof: compare underlying `k`-points
  through the injective pullback point equivalence.
- `bcPoint_basePoint z`: every point `z` of `G_Ω` is the base change of its
  underlying `k`-point.

## `exists_ne_zero_eq_mul_comp_baseChange`

Setting:
- `H` is a smooth affine `Ω`-group;
- `π : G_Ω ⟶ H` is a homomorphism whose underlying scheme map is surjective;
- `χ''` is a cocharacter of `H`;
- `q₀ : H ⟶ Q₀` is flat, surjective and quasi-compact, with fibers the right
  cosets of `P_H(χ'')` (`hf₀`);
- `κ'` is a field over `Ω` (with compatible `k`-structure) and
  `x₀ : Spec κ' ⟶ Q₀` is a point over `Ω`.

Conclusion: there is a nonzero `f ∈ κ' ⊗[k] B` such that every `k`-point
`a : B → k` with `evalMap κ' a f ≠ 0` satisfies
`x₀ = (π(a_Ω) * u'') ≫ q₀` for some `u'' ∈ U_H(χ''⁻¹)(κ')`. Here
`a_Ω = bcPoint F e Ω κ' (ofId ∘ a)`.

Proof as implemented. On `T = Spec (κ' ⊗[k] B)`, an `Ω`-scheme through `κ'`,
use the point `g₀ = π(bcPoint includeRight)` of `H` and the projection `p₀` to
`Spec κ'`. Let `y = g₀⁻¹ · (p₀ ≫ x₀)` for the Library action `flagQuotientAct`
of `H` on `Q₀`, and let `O ⊆ T` be the preimage of the opposite cell of `H`.

- `O` is open, by `OppositeCell.isOpen_cell`.
- `O` is nonempty. By `exists_lift_of_surjective` (over `Ω`), lift `x₀`
  through `q₀` to `h₁ ∈ H(K₁)`, and `h₁` through `π` to `h₂ ∈ G_Ω(K₂)`. Then
  `h₂` is the base change of a `k`-point `γ` (`bcPoint_basePoint`). The
  `Ω`-algebra map `κ' ⊗ B → K₂` built from `κ' → K₁ → K₂` and `γ` gives a
  `K₂`-point of `T`. By `algOverHom_comp_bcPoint`, its composites with `g₀` and
  `p₀` are the images of `h₁` and of `κ' → K₂`, so its composite with `y` is
  `h₁⁻¹ · (h₁ ≫ q₀) = 1 ≫ q₀`, which lies in the cell.
- `exists_ne_zero_range_subset` gives `f`. For `a` with `evalMap κ' a f ≠ 0`,
  the `Ω`-algebra map `evalMapOver Ω κ' a` has the same underlying ring map as
  `evalMap κ' a`. So its spectrum is a `κ'`-point of `T` inside `O`. Its
  composite with `y` is `π(a_Ω)⁻¹ · x₀`, by `algOverHom_comp_bcPoint` again. So
  `OppositeCell.exists_mem_unipotent` gives `u''` with
  `u'' ≫ q₀ = π(a_Ω)⁻¹ · x₀`. Then `x₀ = (π(a_Ω) * u'') ≫ q₀` by the action
  laws.
