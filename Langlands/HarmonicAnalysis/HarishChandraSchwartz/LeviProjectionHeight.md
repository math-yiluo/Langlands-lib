# Heights of Levi components of dynamic parabolic points

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.LeviProjectionHeight`, namespace
`Langlands.GroupScheme.MatrixRepresentation`.

## Purpose and provenance

Provenance: internal. In Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), IV.1.1, printed pp. 277–281 (PDF pp. 43–47), the convergence
proof of the standard intertwining integral bounds coefficients of the inducing representation
at the Levi component `m_P(x)` of an Iwasawa decomposition `x = m u k`. It uses, without
stating it separately, that the height of `m` is controlled by the height of `m u`. This module
proves that fact for dynamic parabolic subgroups of an affine group over a non-archimedean
local field: there is `C` with `‖m‖ ≤ C ‖m u‖` for every `m ∈ Z(χ)(F)` and `u ∈ U(χ)(F)`. The
argument (the Levi component is the limit of `χ(t)ⁿ (m u) χ(t)⁻ⁿ`, and conjugation by `χ(t)ⁿ`
does not enlarge the entries of a block triangular matrix in a diagonalizing basis) is derived
from Library results and is not transcribed from a source.

## Setting and notation

- `F` carries `[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`, and
  `|·|` is `LocalField.residueNormalizedAbsoluteValue F`.
- `G` is a group scheme over `Spec F` with `G.X.left` affine; the main theorem also assumes
  `[LocallyOfFiniteType G.X.hom]`. `G(F)` is `rationalPoints G` with the point topology
  `rationalPointTopology F G.X`.
- For a cocharacter `χ : 𝔾_m ⟶ G` and `t ∈ Fˣ`, `χ(t)` is `gmRationalPoint t ≫ χ.hom.hom`.
  `P(χ)(F)`, `Z(χ)(F)`, `U(χ)(F)` are `(Dynamic.parabolic χ).rationalPoints`,
  `(Dynamic.centralizer χ).rationalPoints`, `(Dynamic.unipotent χ).rationalPoints`.
- For a representation `ρ` of `G` on `Fin N`, `ρ.rationalMatrix x` is its matrix at `x ∈ G(F)`,
  and `‖x‖ = rationalMatrixNorm F ρ x` is the height (the maximum of the absolute values of the
  entries of `ρ(x)` and `ρ(x)⁻¹`). `IsClosedSubgroup ρ` says `ρ` is a closed immersion.
- `blockParabolicSubgroup F e` (for `e : Fin N → ℤ`) is the subgroup of `GL_N(F)` of matrices
  `g` with `g i j = 0` whenever `e i < e j`; `diagonalCocharacter (Fin N) _ e` is
  `t ↦ diag(t ^ e i)`.

## Declarations

- `abs_rationalMatrix_apply_le_of_tendsto_conj`: let `ρ₁` be a representation of `G` on `Fin N`
  with `χ ≫ ρ₁ = diagonalCocharacter (Fin N) _ e`, and let `t ∈ Fˣ` with `t ^ n → 0`. If
  `ρ₁(p) ∈ blockParabolicSubgroup F e` and `χ(t) ^ n p χ(t)⁻ⁿ → m` in `G(F)`, then
  `|ρ₁(m) i j| ≤ |ρ₁(p) i j|` for all `i, j`.
- `exists_rationalMatrixNorm_levi_le`: for a cocharacter `χ` of `G` and a closed representation
  `ρ₀` of `G` on a nonempty `Fin N` (`G` locally of finite type), there is `C : ℝ` such that for
  all `p, m ∈ G(F)` with `p ∈ P(χ)(F)`, `m ∈ Z(χ)(F)` and `m⁻¹ p ∈ U(χ)(F)`,
  `rationalMatrixNorm F ρ₀ m ≤ C * rationalMatrixNorm F ρ₀ p`.

## Proof as implemented

1. Entry bound. The matrix of `χ(t)` under `ρ₁` is `diagonalUnits F e t`
   (`rationalMatrix_gmRationalPoint_comp`), so the `(i, j)` entry of
   `ρ₁(χ(t) ^ n p χ(t)⁻ⁿ)` is `(t ^ n)⁻¹ ^ (e j - e i) · ρ₁(p) i j`
   (`HarishChandraSchwartz.diagonalUnits_conj_apply`). The entry and the absolute value are
   continuous (`continuous_rationalMatrix_entry`,
   `Plancherel.continuous_residueNormalizedAbsoluteValue`), so `|ρ₁(m) i j|` is the limit of the
   absolute values of these entries. If `e i < e j`, the entry of `p` is `0` (block
   parabolic), so all entries along the sequence are `0`. If `e i ≥ e j`, the factor has absolute
   value at most `1`, because `|t| ≤ 1` (`residueNormalizedAbsoluteValue_le_one_of_tendsto_pow`)
   and the exponent is nonpositive. In both cases `le_of_tendsto'` concludes.
2. Diagonalization. Choose `t` with `t ^ n → 0` (public `exists_unit_tendsto_pow_zero`) and
   `g₀` with `χ ≫ ρ₀ ≫ inn(g₀) = diag(t ^ e i)` (public
   `exists_innerIso_comp_eq_diagonalCocharacter`). Then `ρ₁ = ρ₀ ≫ inn(g₀)` is closed
   (`IsClosedSubgroup.comp_iso`), and its matrices are `g₀ ρ₀(x) g₀⁻¹`
   (`rationalMatrix_comp_innerIso`). Submultiplicativity and inversion invariance of `glNorm`
   give `‖x‖₁ ≤ M² ‖x‖₀` and `‖x‖₀ ≤ M² ‖x‖₁` with `M = glNorm g₀`.
3. Limits. Since `m ∈ Z(χ)(F)` commutes with `χ(t) ^ n` (public `commute_cocharPoint`) and
   `χ(t) ^ n (m⁻¹ p) χ(t)⁻ⁿ → 1` (public `tendsto_cocharPoint_pow_conj`, with the bridge
   `cocharPoint_eq_gmRationalPoint_comp`), `χ(t) ^ n p χ(t)⁻ⁿ = m · χ(t) ^ n (m⁻¹ p) χ(t)⁻ⁿ → m`,
   and inverting gives `χ(t) ^ n p⁻¹ χ(t)⁻ⁿ → m⁻¹`. Points of `P(χ)(F)` have block parabolic
   matrices under `ρ₁` (`Dynamic.mem_parabolic_iff_of_diagonal` and
   `rationalMatrix_mem_blockParabolicSubgroup_iff`), and `p⁻¹ ∈ P(χ)(F)`.
4. Apply step 1 to `p → m` and to `p⁻¹ → m⁻¹`: every entry of `ρ₁(m)` and of `ρ₁(m)⁻¹` is
   bounded by `glNorm ρ₁(p)` (`norm_le_glNorm`, `norm_inv_le_glNorm`), so `‖m‖₁ ≤ ‖p‖₁` by
   `glNorm_le`. Combining with step 2, `‖m‖₀ ≤ M² M² ‖p‖₀`.

## Scope

Only the dynamic Levi decomposition `P(χ) = Z(χ) U(χ)` on rational points is treated; the
identification with a parabolic root presentation is made in the module
`ParabolicIntertwiningCharacterDecay`.
