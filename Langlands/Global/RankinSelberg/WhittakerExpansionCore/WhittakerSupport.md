# Finite-level support of Whittaker terms

Module `Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerSupport`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. These are helper lemmas for half (S) of the
Whittaker expansion (see `Interface`). Let `f` be a function on `GL_(r+1)(𝔸)` that is invariant
on the left under rational points and on the right under an open subgroup `L` of
`GL_(r+1)(𝔸_f)`. The module bounds the denominators of the last row `ξ` of `γ ∈ GL_(j+1)(F)`
whenever the Whittaker term `W_f(diag(γ, I) ρ x)` is nonzero, uniformly in a rational matrix `ρ`
of controlled denominator and in `x` from a compact set.

## Section `Absorption` (any topological group `G`)

* `exists_pow_conj_mem`: let `U` be a compact subgroup, `L` an open subgroup and `Q` a compact
  set. Then there is `δ > 0` with `x⁻¹ g^δ x ∈ L` for all `g ∈ U` and `x ∈ Q`.
  Proof: `H = {g : x⁻¹ g x ∈ L for all x ∈ Q}` is a subgroup. It is a neighbourhood of `1`: the
  map `(g, x) ↦ x⁻¹ g x` is continuous and sends `(1, x)` into the open set `L`, so a tube-lemma
  argument over the compact set `Q` (`IsCompact.eventually_forall_of_forall_eventually`) applies.
  Hence `H` is open, and `H ∩ U` is an open subgroup of the compact group `U`, of finite
  index (`Subgroup.quotient_finite_of_isOpen`). Take for `δ` the index of its normal core `N`:
  then `g^δ ∈ N ⊆ H ∩ U` for every `g ∈ U` (`Subgroup.pow_index_mem`, `Subgroup.normalCore_le`).

## Section `SquareZero` (any commutative ring)

* `sqZeroUnit Y hY`: for a square matrix `Y` with `Y Y = 0`, the invertible matrix `1 + Y`,
  with inverse `1 - Y`.
* `val_sqZeroUnit_pow`: `(1 + Y)^k = 1 + k Y`, by induction on `k`.

## Section `Coordinates`

* `finCoord y`: the finite component `y_f ∈ GL_n(𝔸_f)` of an adelic point, obtained through
  the Library equivalence `GeneralLinearGroupPoints.adelicEquiv` and `AdelicGL.finite`. It is
  multiplicative (`finCoord_mul`, `finCoord_inv`) and continuous (`continuous_finCoord`, via
  `GeneralLinearGroupPoints.adelicHomeomorph`).
* `finCoord_ratPoint_apply`: the finite component of a rational point `ratPoint ρ` has entries
  `ρ_(a b)` embedded diagonally in `𝔸_f`.
* `inv_mul_mul_eq_finitePoint`: if `P` has archimedean component `1`, then
  `y⁻¹ P y = finitePoint(y_f⁻¹ P_f y_f)`. Both sides are compared componentwise
  (`AdelicGL.ext_infinite_finite`).
* `finCol c`: a column `c` of finite adeles, viewed as adeles with archimedean part `0`.
* `infinite_colPoint_finCol`, `finCoord_colPoint_finCol`: the column point
  `colPoint (finCol c)` (Library, the unipotent matrix `1 + colMatrix` in column `j + 1`) has
  archimedean component `1` and finite component `1 + colMatrix j c`.
* `colMatrix_nsmul`: `colMatrix j (k c) = k colMatrix j c`.
* `isColSupported_finCol`: `finCol` preserves the support condition `IsColSupported j`
  (entries vanish from row `j + 1` on).

## Section `Integrality`

* `algebraMap_mem_integralFiniteAdeles`: an algebraic integer of `F` is integral in `𝔸_f`
  (Library `algebraMap_integer_mem`).
* `exists_nat_mul_isIntegral`: every `x ∈ F` has a positive integer multiple `m x` that is an
  algebraic integer (Mathlib `exists_integral_multiples`, then taking `|m|`).
* `sqZeroUnit_mem_standardIntegral`: if `Y` is square-zero with entries in `Ô`, then `1 + Y`
  lies in `GL_n(Ô)` (Library `FiniteAdelicGL.standardIntegral`), since `1 + Y` and `1 - Y` have
  integral entries.

## Section `Conjugation`

* `exists_conj_colPoint_eq_pow`: let `e ρ` and `e ρ⁻¹` have algebraic integer entries and let
  `c'` be a column with entries in `Ô`. Then for every `δ` there is `g ∈ GL_(r+1)(Ô)` with
  `ρ_f⁻¹ (1 + colMatrix(δ e² c')) ρ_f = g^δ`. Proof: put `C = colMatrix j c'` and
  `Y = ρ_f⁻¹ (e² C) ρ_f = (e ρ_f⁻¹) C (e ρ_f)`. Then `Y` has integral entries, and
  `Y Y = 0` because `C C = 0` (Library `colMatrix_mul_colMatrix`). Take `g = 1 + Y`. Then
  `g^δ = 1 + δ Y = ρ_f⁻¹ (1 + δ e² C) ρ_f`.

## Section `Support`

* `exists_support_denominator` (support): assume `j < r`, `ψ` is a standard additive character,
  `f` is left invariant under rational points and right invariant under the open subgroup `L`,
  and `C` is compact. Then there is a positive integer `D₀` with the following property. Let
  `e ρ` and `e ρ⁻¹` have algebraic integer entries, `x ∈ C`, `γ ∈ GL_(j+1)(F)`, and
  `W_f(diag(γ, I) (ratPoint ρ) x) ≠ 0`. Then every entry of `D₀ e² ξ` is an algebraic integer,
  where `ξ` is the last row of `γ`.

  Proof. Write `ψ(a) = ψ₀(β a)` with `β ∈ F^×` (Library `exists_eq_standardCharacter_mul`). Let
  `D ∈ 𝒪` be the dual denominator of Library `exists_dual_denominator_finite`: if
  `ψ₀(z t) = 1` for all `t ∈ Ô`, then `D z ∈ Ô`. Apply `exists_pow_conj_mem` to
  `U = GL_(r+1)(Ô)` (compact, Library `isCompact_standardIntegral`), `L`, and the compact set
  `Q = {x_f : x ∈ C}`; this gives `δ`. Choose `m > 0` with `m (D β)⁻¹` integral and put
  `D₀ = m δ`.

  Fix an index `b` and `t ∈ Ô`, and let `c` be the column with `δ e² t` in row `b` and `0`
  elsewhere. Put `z = ρ x`. By `exists_conj_colPoint_eq_pow`,
  `l = z_f⁻¹ (1 + colMatrix c) z_f = x_f⁻¹ g^δ x_f` with `g ∈ GL_(r+1)(Ô)`, so `l ∈ L`, and
  `colPoint(c) z = z · finitePoint(l)` (`inv_mul_mul_eq_finitePoint`). The left translation
  formula `whittaker_padRational_colPoint` (from `WhittakerBasic`) and the right
  `L`-invariance of `W_f` give `W = ψ(ξ_b δ e² t) W` for the nonzero value
  `W = W_f(diag(γ, I) z)`. So `ψ₀(β ξ_b δ e² t) = 1` for all `t ∈ Ô`
  (`standardCharacter_mul_finiteAdele`), and therefore `D β ξ_b δ e²` is an algebraic integer
  (`exists_eq_algebraMap_of_integral`). Multiplying by the integral element `m (D β)⁻¹` shows
  that `m δ e² ξ_b` is an algebraic integer.

This is the classical observation that a Whittaker function of finite level has support in a
lattice of the unipotent characters. The formulation (uniform `D₀` with the explicit factor `e²`,
absorption through the normal core) is this project's own, chosen for the inductive majorant
estimate of half (S).
