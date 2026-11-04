# Extension of points of a dynamic parabolic quotient through a proper comparison

This module contains the core of the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6 (printed
pp. 586–588). It is the argument after the reductions to `k` separably closed
and `G` pseudo-reductive with `P = P_G(λ)`. The comparison data over an
algebraic closure, and several separately stated facts, enter as hypotheses.
CGP's root-group valuation step is replaced by the graded integrality theorem
of `Langlands.CommutativeAlgebra.GradedDVRIntegrality`. The statement is
derived here; it is not quoted from the source.

## `exists_extension_of_comparison`

Setting over a field `k`:
- `G = Spec B` is corepresented, smooth and affine, with `B` finitely
  generated;
- `χ` is a cocharacter;
- `q : G ⟶ Q` is flat, surjective and quasi-compact, with fibers the right
  cosets of `P_G(χ)` (`hf`).

Comparison data over a field `Ω` with `Algebra k Ω`:
- `H` is a smooth affine `Ω`-group;
- `π : G_Ω ⟶ H` is a homomorphism with surjective underlying map;
- `χ''` is a cocharacter of `H` whose opposite equals the base change of the
  opposite of `χ` followed by `π` (`hχ`);
- `q₀ : H ⟶ Q₀` is flat, surjective and quasi-compact, with fibers the right
  cosets of `P_H(χ'')` (`hf₀`), and `Q₀` is proper over `Ω`;
- `φ : Q_Ω ⟶ Q₀` satisfies `q_Ω ≫ φ = π ≫ q₀` (`hφ`).

Further hypotheses:
- `hker`: a contracting `k`-point `a` of `B` (for the opposite of `χ`) with
  `π(a_Ω) = π(ε_Ω)` is the counit `ε`;
- `hrat`: nonzero finitely generated geometrically reduced `k`-algebras have
  `k`-points;
- `hdense`: for fields `K₁, K₂` over `k` and nonzero `f₁ ∈ K₁ ⊗[k] B`,
  `f₂ ∈ K₂ ⊗[k] B`, some `k`-point `a` has `(K₁ ⊗ a)(f₁) ≠ 0` and
  `(K₂ ⊗ a)(f₂) ≠ 0`;
- `R` is a DVR over `k` with geometrically reduced residue field, and
  `Ω ⊗[k] R` is a domain and a DVR with fraction field `Ω ⊗[k] Frac R` (`hfrac`,
  for the algebra structure `Ω ⊗ (R → Frac R)`).

Conclusion: every point `x : Spec (Frac R) ⟶ Q` over `k` extends to
`xR : Spec R ⟶ Q` with `Spec (R → Frac R) ≫ xR = x`.

Proof as implemented. Write `λ` for the opposite of `χ` and `K` for `Frac R`.
1. `CellTranslation.exists_ne_zero_eq_mul_comp` gives `0 ≠ f ∈ K ⊗ B`.
2. Let `x'' = tensorPoint Ω x ≫ φ`, a point of `Q₀` over `Ω ⊗ K`. Using the
   field structure on `Ω ⊗ K` from `hfrac`, `exists_extension_of_isProper`
   extends it to `xA` over `A' = Ω ⊗ R`. Let `x₀` be the restriction of `xA` to
   the residue field `κ'` of `A'`. `exists_ne_zero_eq_mul_comp_baseChange`
   gives `0 ≠ f' ∈ κ' ⊗ B`.
3. `hdense` gives one `k`-point `a` for `f` and `f'` (converted with
   `evalMap_apply`). Hence `x = (a_K * u) ≫ q` with `u ∈ U_G(λ)(K)`, and
   `x₀ = (π(a_Ω) * u₀) ≫ q₀` with `u₀ ∈ U_H(χ''⁻¹)(κ')`.
4. Let `y = π(a_Ω)⁻¹ · xA` (action of `H` on `Q₀`). Its residue-field
   restriction is `u₀ ≫ q₀`, which lies in the cell. By
   `range_subset_of_residue` all of `y` lies in the cell, so
   `y = u'' ≫ q₀` with `u'' ∈ U_H(χ''⁻¹)(A')`, and
   `xA = (π(a_Ω) * u'') ≫ q₀`.
5. Over `Ω ⊗ K`, put `v₁ = π(u_Ω)` and `v₂ = u''|`. Both lie in
   `U_H(χ''⁻¹)`: `v₁` by `tensorGPoint_mem_unipotent`, `unipotent_le_comap`
   and `hχ`. Both satisfy `(c * v) ≫ q₀ = x''` with `c = π(a_Ω)`: for `v₁` by
   `hφ` and multiplicativity of base change, for `v₂` by step 4. The fiber
   criterion `hf₀` gives `v₁⁻¹ v₂ ∈ P_H(χ'')`, so `(v₁⁻¹ v₂) ≫ q₀ = 1 ≫ q₀`.
   `OppositeCell.eq_of_mem_unipotent` then gives `v₁⁻¹ v₂ = 1`, i.e.
   `v₁ = v₂`.
6. Hence every function on `H` takes its value at `π(u_Ω)` in the image of
   `Ω ⊗ R`. `exists_point_of_baseChange_comparison` (with `hker`, `hrat`)
   gives `uR ∈ U_G(λ)(R)` restricting to `u`.
7. `xR = (a_R * uR) ≫ q` restricts to `(a_K * u) ≫ q = x`.
