# Iwasawa bounds for eigenlines of a dynamic parabolic and of its Levi

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.EigenlineIwasawaBounds`,
namespace `Langlands.GroupScheme.MatrixRepresentation`.

## Purpose and provenance

Provenance: internal. In the convergence proof of the standard intertwining integrals
(Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*
(2003), II.3.4 and IV.1.1, printed pp. 256–257 and 277–281), the Levi component `m` of a point
`x = m u κ` of `Ū(F)` or of `Ū(F) ∩ U'(F)` is controlled through characters of `M`, by letting
`x` act on lines in representations of `G`. The public module `ParabolicLineCharacter` does this
for the one Chevalley line whose stabilizer is exactly `P(χ)(F)`. This module proves the same
two kinds of estimate for an arbitrary nonzero eigenvector. Then any line on which `P(χ)(F)`, or
only its Levi `Z(χ)(F)`, acts by scalars can be used. For example, the top exterior power of the
Lie algebra of the radical of a larger parabolic is such a line (public `AdjointDeterminantLine`).
The arguments are derived from Library results and are not transcribed from the source.

## Setting and notation

- `k` is a field, `G` a group scheme over `Spec k`, `ρ` a matrix representation of `G` on a
  finite type `n`, `v : n → k` a vector, `S` a subgroup of `G(k) = rationalPoints G` and
  `c : G(k) → k` a function. `ρ.rationalMatrix x` is the matrix of `x`.
- `χ : 𝔾_m ⟶ G` is a cocharacter, `P(χ) = Dynamic.parabolic χ`, `Z(χ) = Dynamic.centralizer χ`,
  `U(χ) = Dynamic.unipotent χ`, and `Ū(F) = U(χ⁻¹)(F)` with
  `χ⁻¹ = Dynamic.oppositeCocharacter χ`. `(·).rationalPoints` is the subgroup of rational points.
- In the local-field part, `F` is a nonarchimedean local field, `|·|` is
  `LocalField.residueNormalizedAbsoluteValue F`, and `G(F)` carries `rationalPointTopology F G.X`.
  `K ⊆ G(F)` is compact.

## Declarations

- `IsEigenvectorOn ρ v S c` (definition, a `Prop`): for every `x ∈ S`, `ρ(x) v = c x • v`.
- `eigenvalue_mul`, `eigenvalue_one`, `eigenvalue_mul_inv`: if `v ≠ 0` and
  `IsEigenvectorOn ρ v S c`, then on `S` the function `c` is multiplicative, `c 1 = 1`, and
  `c x * c x⁻¹ = 1`.
- `eigenvalue_eq_one_of_mem_unipotent`: let `G` be affine and locally of finite type over `F`,
  `v ≠ 0`, `P(χ)(F) ≤ S` and `IsEigenvectorOn ρ v S c`. Then `c x = 1` for every `x ∈ U(χ)(F)`.
- `exists_abs_eigenvalue_le` (upper bound): let `G` be affine and locally of finite type over
  `F`, `v ≠ 0` and `IsEigenvectorOn ρ v P(χ)(F) c`. Then there is `C` such that `|c p| ≤ C`
  whenever `x ∈ Ū(F)`, `p ∈ P(χ)(F)`, `κ ∈ K` and `x = p κ`.
- `exists_le_abs_eigenvalue` (lower bound): let `G` be affine and locally of finite type over
  `F`, `v ≠ 0` and `IsEigenvectorOn ρ v Z(χ)(F) c`. Then there is `C > 0` such that
  `C ≤ |c m|` whenever `m ∈ Z(χ)(F)`, `u ∈ U(χ)(F)`, `κ ∈ K`, `x = m u κ` and `ρ(x) v = v`.

## Proofs as implemented

**Eigenvalue laws.** From `ρ(x y) v = ρ(x) (c y • v) = (c x * c y) • v` and `v ≠ 0`
(`smul_left_injective`); `ρ(1) = 1` gives `c 1 = 1`, and then `c x * c x⁻¹ = c 1 = 1`.

**Unipotent points.** Take `t` with `t ^ j → 0` (public `exists_unit_tendsto_pow_zero`) and
`a = χ(t) ∈ P(χ)(F)` (public `gmRationalPoint_comp_mem_parabolic`). For `x ∈ U(χ)(F)` the
conjugates `a ^ j x a ^ (-j)` tend to `1` (public `mem_unipotent_iff_tendsto_conj`). They lie in
`S`, and by multiplicativity their eigenvalue is `c x`, so `ρ(a ^ j x a ^ (-j)) v = c x • v` for
all `j`. The map `g ↦ ρ(g) v` is continuous (public `continuous_rationalMatrix_entry`), so the
constant sequence `c x • v` tends to `ρ(1) v = v`. Hence `c x • v = v` and `c x = 1`.

**Upper bound.** `v` is an eigenvector of every `ρ(χ(t))`, because `χ(t) ∈ P(χ)(F)`. The public
`exists_rationalVectorNorm_le_mul_of_weightVector` gives `C' > 0` with `‖v‖ ≤ C' ‖ρ(y) v‖` for
`y ∈ Ū(F)`. The public `exists_rationalVectorNorm_mulVec_inv_le` gives `B` with
`‖ρ(κ⁻¹) v‖ ≤ B` on `K`. For `x = p κ ∈ Ū(F)`, `ρ(x⁻¹) v = c(p⁻¹) ρ(κ⁻¹) v` and
`|c(p⁻¹)| = |c p|⁻¹`. Applying the first estimate to `y = x⁻¹` gives
`‖v‖ ≤ C' |c p|⁻¹ B`, that is `|c p| ≤ C' B / ‖v‖`.

**Lower bound.** The points `χ⁻¹(t)` lie in `Z(χ)(F)` (public `range_comp_le_centralizer_comp`),
so `v` is an eigenvector of every `ρ(χ⁻¹(t))`. Since `(χ⁻¹)⁻¹ = χ` (public
`oppositeCocharacter_oppositeCocharacter`), the weight-vector estimate for `χ⁻¹` gives `C' > 0`
with `‖v‖ ≤ C' ‖ρ(y) v‖` for `y ∈ U(χ)(F)`. The set `K⁻¹` is compact, which gives `B` with
`‖ρ(κ) v‖ ≤ B` for `κ ∈ K`. If `x = m u κ` fixes `v`, then `κ = u⁻¹ m⁻¹ x` and
`ρ(κ) v = c(m⁻¹) ρ(u⁻¹) v`, so `‖ρ(u⁻¹) v‖ ≤ |c m| max B 1`. With `y = u⁻¹` this gives
`‖v‖ ≤ C' |c m| max B 1`, that is `‖v‖ / (C' max B 1) ≤ |c m|`.

## Scope

These are estimates for one line at a time. Turning them into the decay of
`δ^{1/2} χ` at Levi components on `Ū(F) ∩ U'(F)` still needs explicit lines whose eigenvalues are
known characters of the Levi, and the cone geometry of relative roots. Neither is done here, and
the module does not complete the host theorem.
