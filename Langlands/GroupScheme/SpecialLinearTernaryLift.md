# Homomorphisms out of ternary SL from two binary SL homomorphisms

Module `Langlands.GroupScheme.SpecialLinearTernaryLift`, namespace
`Langlands.GroupScheme.SpecialLinear.TernaryPresentation`.

This internal module is group theory and matrix algebra: it has no schemes or
functors. Its main result, `TernaryRelations.exists_lift`, says: let `F` be a
field and let `φ₁ φ₂ : SL₂(F) →* H` be group homomorphisms into an arbitrary
group `H`. If they satisfy the nine relations of `TernaryRelations`, then one
homomorphism `Φ : SL₃(F) →* H` restricts to `φ₁` on the upper-left block copy
`left` and to `φ₂` on the lower-right block copy `right`. There is no condition
on the size of `F`. The module is the presentation-free half of the planned
proof of the Library statement `Langlands.GroupScheme.AdjacentSimpleRootSpecialLinearStatement`;
it does not mention that statement and does not prove it.

It imports `Langlands.GroupScheme.SpecialLinearTernaryPresentation` (block
embeddings `left`, `right`, with matrices `leftMatrix`, `rightMatrix`), which
in turn provides the binary presentation module: `upper t` and `lower t` (the
unipotent matrices `[1, t; 0, 1]` and `[1, 0; t, 1]`), `BinaryPresentation.diag u`
(the matrix `diag(u, u⁻¹)`), `BinaryUpper.weylMatrix` (the matrix
`w = [0, -1; 1, 0]`) and `BinaryPresentation.hom_ext` (two homomorphisms out of
`SL₂(F)` agreeing on all `upper t` and `lower t` are equal). The source group
`G` of the abstract section lives in universe `u`, fields `F` in universe `u`,
and target groups `H` in universe `v`.

All statements are internal and every step is proved in Lean; no literature
theorem is used. The method is the classical one: extend a homomorphism from a
maximal parabolic subgroup `P` to the whole group using the decomposition
`SL₃(F) = P ∪ P n P`.

Notation: `SL2 A` and `SL3 A` are local notations for
`Matrix.SpecialLinearGroup (Fin 2) A` and `Matrix.SpecialLinearGroup (Fin 3) A`.
The option `backward.isDefEq.respectTransparency false` is set for the whole
file, so that rewriting with `Matrix.SpecialLinearGroup.coe_mul` works.

## Extending across one double coset (section `CellExtension`)

Here `G` and `H` are arbitrary groups, `P` a subgroup of `G`, `n ∈ G`,
`f : G → H` a function and `ν ∈ H`.

- `CellData P n f ν` (a `Prop` structure) has the fields `not_mem : n ∉ P`,
  `sq_mem : n * n ∈ P`, `map_mul` (`f` is multiplicative on `P`), `conj`
  (for `μ ∈ P` with `n μ n⁻¹ ∈ P`, `f (n μ n⁻¹) = ν f(μ) ν⁻¹`) and
  `sq : f (n * n) = ν * ν`.
- `CellGood P n f ν r` says that there are `p₁, p₂ ∈ P` with
  `n r n = p₁ n p₂` and `ν f(r) ν = f(p₁) ν f(p₂)`.
- Consequences of `CellData` (namespace `CellData`): `map_one`, `map_inv` (on
  `P`), `cell_not_mem` (`p n q ∉ P` for `p, q ∈ P`), `cell_eq` (if
  `p n q = p' n q'` with all four in `P`, then `f p ν f q = f p' ν f q'`; this
  uses `conj` at `q q'⁻¹`), `conj_inv_mem`, `map_conj_inv` (the same
  compatibility for conjugation by `n⁻¹`), `map_n_mul_n` (for `q ∈ P` with
  `n q n ∈ P`, `f (n q n) = ν f(q) ν`) and `cellGood_mul` (goodness of `r` is
  preserved by multiplying `r` on both sides by elements `μ ∈ P` with
  `n μ n⁻¹ ∈ P`).
- `cellExtendFun P n f ν g` is `f p ν f q` if `g = p n q` for some `p, q ∈ P`
  (chosen by `Classical.choose`), and `f g` otherwise. By `cell_eq` the value
  does not depend on the choice (`cellExtendFun_cell`), and it is `f g` on `P`
  (`cellExtendFun_of_mem`).
- Assume in addition `cover : ∀ g ∉ P, ∃ p ∈ P, ∃ q ∈ P, g = p * n * q` and
  `good : ∀ q ∈ P, n * q * n ∉ P → CellGood P n f ν q`. Then
  `cellExtendFun_mul_mem` (right multiplication by `P`), `cellExtendFun_mul_n`
  (right multiplication by `n`; the case `n q n ∈ P` uses `map_n_mul_n`, the
  other case uses `good`) and hence `cellExtendFun_mul` (multiplicativity on
  all of `G`) hold.
- `cellExtend D cover good : G →* H` is this homomorphism, with
  `cellExtend_of_mem` (it equals `f` on `P`) and `cellExtend_n` (it sends `n`
  to `ν`).

## Binary identities (section `BinaryIdentities`)

Matrix forms `coe_diag`, `coe_upper`, `coe_lower`, `coe_weylMatrix`, and the
identities `upper_add`, `diag_mul_upper` (`diag u · upper s = upper (u² s) · diag u`),
`diag_mul_weylMatrix` (`diag u · w = w · diag u⁻¹`), `weylMatrix_mul_weylMatrix`
(`w² = diag(-1)`), `weylMatrix_mul_lower` (`w · lower t = upper (-t) · w`),
`eq_upper_mul_diag` (an element `g` of `SL₂(F)` with `g₁₀ = 0` equals
`upper (g₀₀ g₀₁) · diag g₀₀`) and the Bruhat identity
`weylMatrix_mul_upper_mul_weylMatrix` (for `t ≠ 0`,
`w · upper t · w = upper (-t⁻¹) · w · (upper (-t) · diag t)`). Each is checked
entrywise.

## Cells of ternary SL (section `TernaryCells`)

- `det_three` expands `det g = 1` for `g ∈ SL₃(F)`.
- `parabolic : Subgroup (SL3 F)` is the stabilizer of the line through the first
  basis vector, i.e. the matrices with `g₁₀ = g₂₀ = 0` (`mem_parabolic`); call it
  `P`. `parabolic_det` gives `g₀₀ (g₁₁ g₂₂ - g₁₂ g₂₁) = 1` on `P`, and
  `parabolic_apply_ne_zero` gives `g₀₀ ≠ 0`. `right_mem_parabolic`: the right
  block lies in `P`; `left_mem_parabolic`: so does `left Y` when `Y₁₀ = 0`.
- `cellWeyl = left w` (call it `n`), `rightWeyl = right w`, and
  `corner t = 1 + t E₀₂`, with matrix forms `coe_cellWeyl`, `coe_cellWeyl_inv`,
  `coe_rightWeyl`, `coe_corner`, and `corner_mem_parabolic`.
- `cellWeyl_not_mem` (`n ∉ P`), `cellWeyl_mul_cellWeyl` (`n² = left (diag(-1))`)
  and `cellWeyl_mul_cellWeyl_mem`.
- `inv_mul_apply_of_col`: if `A, B` have the same column `j`, then column `j`
  of `A⁻¹ B` is the basis vector `e_j`.
- `conj_apply_one_zero`, `conj_apply_two_zero`, `conj_mem_parabolic_iff`
  (`n μ n⁻¹ ∈ P` iff `μ₀₁ = μ₂₁ = 0`) and `sandwich_mem_parabolic_iff`
  (`n q n ∈ P` iff `q₀₁ = q₂₁ = 0`).
- `cover`: every `g ∉ P` is `p n q` with `p, q ∈ P`. Proof: write down an
  explicit `p ∈ P` such that `p n` has the same first column as `g` (two cases,
  `g₁₀ = 0` or not); then `q = (p n)⁻¹ g ∈ P` by `inv_mul_apply_of_col`.
- Conjugation identities: `cellWeyl_conj_corner` (`n · corner c · n⁻¹ = right (upper c)`),
  `cellWeyl_conj_right_upper` (`n · right (upper d) · n⁻¹ = corner (-d)`),
  `cellWeyl_conj_left_diag` (`n · left (diag α) · n⁻¹ = left (diag α⁻¹)`),
  `cellWeyl_conj_right_diag` (`n · right (diag w) · n⁻¹ = left (diag w) · right (diag w)`),
  the braid relation `cellWeyl_braid` (`n · rightWeyl · n = rightWeyl · n · rightWeyl`)
  and `cellWeyl_sandwich_left_upper` (the left block copy of the binary Bruhat
  identity).
- `exists_levi_decomposition`: every `μ ∈ P` with `μ₀₁ = μ₂₁ = 0` (that is,
  `μ ∈ P ∩ n⁻¹ P n`) equals `corner c · right (upper d) · left (diag α) · right (diag w)`
  for some `c, d ∈ F` and units `α, w`; the parameters are given explicitly.

## Reducing the cell conditions to generators (section `TernaryCellData`)

- `diag_apply_one_zero`, `upper_apply_one_zero`: the `(1, 0)` entries of
  `diag u` and `upper t` vanish.
- `conj_of_generators`: if `f : SL₃(F) → H` is multiplicative on `P` and the
  compatibility `f (n x n⁻¹) = ν f(x) ν⁻¹` holds for `x` equal to `corner c`,
  `right (upper d)`, `left (diag α)` and `right (diag w)` (stated in the
  conjugated forms given by the four conjugation identities above), then it
  holds for every `μ ∈ P` with `n μ n⁻¹ ∈ P`. Proof: `exists_levi_decomposition`.
- `cellGood_of_reps`: given `CellData P n f ν`, if `rightWeyl` and every
  `left (upper t)` with `t ≠ 0` are good, then every `q ∈ P` with `n q n ∉ P` is
  good. Proof: such `q` is `μ r μ'` with `r` one of the two representatives
  (`left (upper (q₀₁/q₀₀))` if `q₂₁ = 0`, `rightWeyl` otherwise), `μ` an explicit
  element of `P ∩ n⁻¹ P n` and `μ' = (μ r)⁻¹ q`, which lies in `P ∩ n⁻¹ P n`
  because `μ r` and `q` share their first two columns; then `cellGood_mul`.

## The ternary relations and the lift (section `TernaryRelationsSection`)

Auxiliary binary facts: `upper_zero`, `binaryDiag_one`, `binaryDiag_mul`,
`binaryDiag_inv` (`diag` is a homomorphism, via the Library's
`Root.contractingMatrixHom`), `diag_conj_upper`, `weylMatrix_conj_diag`
(`w · diag u · w⁻¹ = diag u⁻¹`) and `weylMatrix_inv_conj_upper`
(`w⁻¹ · upper (-t) · w = lower t`).

Let `φ₁ φ₂ : SL₂(F) →* H`. Write `x₁(s) = φ₁ (upper s)`, `x₂(t) = φ₂ (upper t)`,
`y₂(t) = φ₂ (lower t)`, `h₁(u) = φ₁ (diag u)`, `h₂(u) = φ₂ (diag u)`,
`ν₁ = φ₁ w`, `ν₂ = φ₂ w`.

- `cornerPoint φ₁ φ₂ t = ν₁ · x₂(-t) · ν₁⁻¹`, written `x₃(t)` below. In
  `SL₃(F)` with `φ₁ = left`, `φ₂ = right`, this is `corner t`.
- `TernaryRelations φ₁ φ₂` (a `Prop` structure) has nine fields, each true for
  `φ₁ = left`, `φ₂ = right` in `SL₃(F)`:
  - `torus_upper`: `h₁(u) x₂(t) h₁(u)⁻¹ = x₂(u⁻¹ t)`;
  - `torus_lower`: `h₁(u) y₂(t) h₁(u)⁻¹ = y₂(u t)`;
  - `weyl_torus`: `ν₁ h₂(u) ν₁⁻¹ = h₁(u) h₂(u)`;
  - `commutator`: `x₂(c) x₁(s) x₂(c)⁻¹ = x₁(s) x₃(-(c s))`;
  - `commute_upper_corner`: `x₂(c)` commutes with `x₃(t)`;
  - `commute_lower_upper`: `y₂(c)` commutes with `x₁(s)`;
  - `lower_corner`: `y₂(c) x₃(t) y₂(c)⁻¹ = x₃(t) x₁(-(c t))`;
  - `commute_corner`: `x₁(s)` commutes with `x₃(t)`;
  - `braid`: `ν₁ ν₂ ν₁ = ν₂ ν₁ ν₂`.
- `cornerPoint_add`, `cornerPoint_zero` (always true), `radicalPoint φ₁ φ₂ s t = x₁(s) x₃(t)`
  (the image of the unipotent radical of `P`) and `radicalPoint_zero`.
- `conjDiag c : SL₂(F) →* SL₂(F)` is conjugation by `diag(c, 1)` in `GL₂`,
  written as the explicit matrix `[X₀₀, c X₀₁; c⁻¹ X₁₀, X₁₁]`, with
  `coe_conjDiag`, `conjDiag_upper` and `conjDiag_lower`.
- Under `R : TernaryRelations φ₁ φ₂` (namespace `TernaryRelations`):
  `radicalPoint_add` (the radical map is additive, by `commute_corner`),
  `torus_conj_cornerPoint` (`h₁(c) x₃(t) h₁(c)⁻¹ = x₃(c t)`),
  `torus_conj_radicalPoint`, `right_conj_radicalPoint_upper`,
  `right_conj_radicalPoint_lower` and their consequence
  `right_conj_radicalPoint` (`φ₂ X` acts on the radical coordinates `(s, t)` by
  `(X₁₁ s - X₁₀ t, X₀₀ t - X₀₁ s)` for every `X ∈ SL₂(F)`, by Mathlib's
  `Matrix.SL2.transvection_induction`), and `torus_conj_right`
  (`h₁(c)⁻¹ φ₂(X) h₁(c) = φ₂ (conjDiag c X)`, by `BinaryPresentation.hom_ext`).
- Levi decomposition of `P`: `parabolicUnit g` is the unit `g₀₀` (and `1` off
  `P`), `leviRight g` is `[g₀₀ g₁₁, g₀₀ g₁₂; g₂₁, g₂₂]` (and `1` off `P`),
  `radicalFst g = g₀₀ (g₀₁ g₂₂ - g₀₂ g₂₁)` and
  `radicalSnd g = g₀₀ (g₀₂ g₁₁ - g₀₁ g₁₂)`, with `coe_parabolicUnit`,
  `coe_leviRight`, `mul_apply_three` and the multiplication rules
  `parabolicUnit_mul`, `leviRight_mul` (twisted by `conjDiag`), `radicalFst_mul`
  and `radicalSnd_mul` on `P`.
- `leviPoint φ₁ φ₂ g = h₁(g₀₀) · φ₂ (leviRight g)` and
  `parabolicMap φ₁ φ₂ g = radicalPoint (radicalFst g) (radicalSnd g) · leviPoint g`.
  Under `R`: `leviPoint_mul`, `leviPoint_conj` (action of the Levi part on the
  radical) and `parabolicMap_mul` (`parabolicMap` is multiplicative on `P`).
  Without hypotheses: `parabolicMap_right` (`= φ₂ X` on `right X`),
  `parabolicMap_left` (`= φ₁ Y` on `left Y` when `Y₁₀ = 0`, via
  `eq_upper_mul_diag`) and `parabolicMap_corner` (`= x₃(t)` on `corner t`).
- `TernaryRelations.cellData`: `CellData parabolic cellWeyl (parabolicMap φ₁ φ₂) ν₁`.
  The four generator conditions of `conj_of_generators` come from
  `torus_upper` at `u = -1` (with `w² = diag(-1)`), the definition of
  `cornerPoint`, `weylMatrix_conj_diag`, and `weyl_torus`; `sq` comes from
  `w² = diag(-1)`.
- `TernaryRelations.cellGood_rightWeyl` (from `cellWeyl_braid` and `braid`) and
  `TernaryRelations.cellGood_left_upper` (from the binary Bruhat identity; it
  needs no relation).
- **`TernaryRelations.exists_lift`** (`R : TernaryRelations φ₁ φ₂`):
  `∃ Φ : SL₃(F) →* H, Φ.comp left = φ₁ ∧ Φ.comp right = φ₂`. Proof: `Φ` is
  `cellExtend` for `cellData`, with `cover` and the goodness from
  `cellGood_of_reps`. On the right block it is `parabolicMap_right`. On the left
  block, `BinaryPresentation.hom_ext` reduces to `upper t` (in `P`) and
  `lower t = n⁻¹ · left (upper (-t)) · n` (with `cellExtend_n`).
