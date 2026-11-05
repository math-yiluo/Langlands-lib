# Contraction criterion and products of dynamic unipotent rational points

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnipotentIntersectionProduct`,
namespace `Langlands.GroupScheme.MatrixRepresentation`.

## Purpose and provenance

Provenance: internal. In Waldspurger, *La formule de Plancherel pour les groupes p-adiques,
d'après Harish-Chandra* (2003), IV.1, printed p. 279 (PDF p. 45), the standard intertwining
integral over `(U ∩ U') \ U'` is computed through the product decomposition
`U' = (U ∩ U') (Ū ∩ U')`. The source uses this decomposition without proof. This module proves
it on rational points for dynamic unipotent subgroups of a smooth affine group of finite type
over a non-archimedean local field, by verifying the hypotheses of the abstract theorem in
`OpenCellIntersectionProduct`. On the way it proves that the rational points of a dynamic
unipotent subgroup `U(ξ)(F)` are exactly the points contracted to `1` by conjugation with the
powers of `ξ(t)`, when `t ^ n → 0`. The forward half of that criterion is the public
`tendsto_cocharPoint_pow_conj`; the converse is new here. Neither argument is transcribed from
a source.

## Setting and notation

- `F` carries `[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`, and
  `|·|` is `LocalField.residueNormalizedAbsoluteValue F`.
- `G` is a group scheme over `Spec F` with `G.X.left` affine. `G(F)` is `rationalPoints G` with
  the canonical point topology `rationalPointTopology F G.X`. In the later results `G` is also
  affine over the base and locally of finite type (`[IsAffineHom G.X.hom]`,
  `[LocallyOfFiniteType G.X.hom]`), and for the open cell also smooth (`[Smooth G.X.hom]`).
- For a cocharacter `ξ : 𝔾_m ⟶ G` and `t ∈ Fˣ`, `ξ(t)` is `gmRationalPoint t ≫ ξ.hom.hom`.
  `U(ξ)(F)`, `Z(ξ)(F)` and `P(ξ)(F)` are `(Dynamic.unipotent ξ).rationalPoints`,
  `(Dynamic.centralizer ξ).rationalPoints` and `(Dynamic.parabolic ξ).rationalPoints`. The
  cocharacter `ξ⁻¹` is `CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫ ξ`.
- `blockUnipotentSubgroup F e` is the subgroup of `GL_N(F)` of matrices `g` with
  `g i j = δ i j` whenever `e i ≤ e j`. `IsClosedSubgroup ρ` says that a representation `ρ` is a
  closed immersion.

## Declarations

### Bridge

- `cocharPoint_eq_gmRationalPoint_comp`: the point `cocharPoint χ t` of the public module
  `CocharacterContraction` equals `gmRationalPoint t ≫ χ.hom.hom`. No topology on `F` is used.

### The contraction criterion

- `residueNormalizedAbsoluteValue_le_one_of_tendsto_pow`: if `t ^ n → 0` in `F`, then
  `|t| ≤ 1`.
- `rationalMatrix_mem_blockUnipotentSubgroup_of_tendsto`: let `ρ₁` be a representation of `G`
  on `Fin N` with `ξ ≫ ρ₁ = diag(t ^ e i)` (`diagonalCocharacter`). If `t ^ n → 0` and
  `ξ(t) ^ n y ξ(t)⁻ⁿ → 1` in `G(F)`, then `ρ₁(y) ∈ blockUnipotentSubgroup F e`.
- `mem_unipotent_of_tendsto_conj`: for a closed representation `ρ₀` of `G` on `Fin N`, if
  `t ^ n → 0` and `ξ(t) ^ n y ξ(t)⁻ⁿ → 1`, then `y ∈ U(ξ)(F)`.
- `mem_unipotent_iff_tendsto_conj` (for `G` affine over the base and locally of finite type):
  if `t ^ n → 0`, then `y ∈ U(ξ)(F)` if and only if `ξ(t) ^ n y ξ(t)⁻ⁿ → 1`.
- `mem_normalizer_unipotent_of_commute`: under the same hypotheses, every `c ∈ G(F)` commuting
  with `ξ(t)` normalizes `U(ξ)(F)`.

### Products of dynamic unipotent groups

Here `G` is moreover smooth. Let `χ, ξ` be cocharacters of `G` and `t ∈ Fˣ` with `t ^ n → 0`,
and assume

- `hξ`: `ξ(t) ∈ Z(χ)(F)`;
- `hZU`: the only element of `Z(χ)(F)` lying in `U(ξ)(F)` is `1`.

- `isOpenCellContraction_dynamic`: with the topological group structure
  `rationalPoint_isTopologicalGroup F G`,
  `IsOpenCellContraction (P(χ)(F)) (U(χ⁻¹)(F)) (U(χ)(F)) (U(ξ)(F)) (Z(χ)(F)) (ξ(t)) (χ(t))`
  holds (structure of `OpenCellIntersectionProduct`).
- `unipotentIntersectionProduct` (definition): the homeomorphism
  `(U(χ)(F).subgroupOf U(ξ)(F)) × (U(χ⁻¹)(F).subgroupOf U(ξ)(F)) ≃ₜ U(ξ)(F)` given by the
  `productHomeomorph` of the previous structure. `unipotentIntersectionProduct_apply`: its value
  at `(h, k)` is `h * k`.

## Proofs as implemented

**Bridge.** After rewriting with the public `cocharPoint_eq`, both sides are the composite of
the same rational point of `𝔾_m` with `χ`; `congr 1` closes the goal by definitional
unfolding of `Gm.affinePointsEquiv` and `gmRationalPoint`.

**`|t| ≤ 1`.** If `|t| > 1`, then `|t ^ n| = |t| ^ n ≥ 1` for all `n`, while `|t ^ n| → |0| = 0`
by continuity of `|·|` (public `continuous_residueNormalizedAbsoluteValue`). Mathlib's
`ge_of_tendsto'` gives `1 ≤ 0`.

**Diagonal criterion.** Put `A = ρ₁(y)` and `s = (t ^ n)⁻¹`. By
`rationalMatrix_gmRationalPoint_comp`, `ρ₁(ξ(t)) = diag(t ^ e i)`, so the matrix of
`ξ(t) ^ n y ξ(t)⁻ⁿ` is `D⁻¹ A D` with `D = diag(s ^ e i)`. By public `diagonalUnits_conj_apply`
its `(i, j)` entry is `s ^ (e j - e i) * A i j`. Each entry of `ρ₁` is continuous on `G(F)`
(public `continuous_rationalMatrix_entry`), so these entries converge to `δ i j`. Let
`e i ≤ e j`.

- If `e i < e j`, then `i ≠ j`. Since `|t| ≤ 1`, `|s| ≥ 1`, so
  `|s ^ (e j - e i) * A i j| ≥ |A i j|` for all `n`. The absolute values converge to `|0| = 0`,
  so `|A i j| ≤ 0` and `A i j = 0 = δ i j`.
- If `e i = e j`, the entry is the constant `A i j`, and uniqueness of limits in the Hausdorff
  field `F` gives `A i j = δ i j`.

**Criterion.** Diagonalize `ξ ≫ ρ₀` by public `exists_innerIso_comp_eq_diagonalCocharacter`:
there are `g₀ ∈ GL_N(F)` and weights `e` with `ξ ≫ ρ₁ = diag e` for the closed representation
`ρ₁ = ρ₀ ≫ Int(g₀)` (public `IsClosedSubgroup.comp_iso`). Then `ξ⁻¹ ≫ ρ₁ = diag(-e)` (public
`inv_comp_diagonalCocharacter`). The diagonal criterion shows that `ρ₁(y)` is block unipotent
for `e = -(-e)`. Public `rationalMatrix_mem_blockUnipotentSubgroup_iff` and
`Dynamic.mem_unipotent_iff_of_diagonal`, applied to `ξ⁻¹`, give `y ∈ U((ξ⁻¹)⁻¹)(F)`, and public
`powerHom_neg_one_comp_powerHom_neg_one` identifies `(ξ⁻¹)⁻¹` with `ξ`.

**Equivalence.** The forward direction is public `tendsto_cocharPoint_pow_conj`, composed with
`n ↦ (n, y)` and rewritten by the bridge. The converse uses a closed representation from the
public `affineLinearEmbeddingStatement` and `mem_unipotent_of_tendsto_conj`.

**Normalizer.** If `c` commutes with `a = ξ(t)`, then
`a ^ n (c h c⁻¹) a⁻ⁿ = c (a ^ n h a⁻ⁿ) c⁻¹`. Conjugation by `c` and by `c⁻¹` is continuous, so
`a ^ n h a⁻ⁿ → 1` if and only if `a ^ n (c h c⁻¹) a⁻ⁿ → 1`. The equivalence above turns this
into `h ∈ U(ξ)(F) ↔ c h c⁻¹ ∈ U(ξ)(F)`, which is `Subgroup.mem_normalizer_iff`.

**`isOpenCellContraction_dynamic`.** The fields are supplied as follows.

- Open embedding: public `isOpenEmbedding_openCellMap_rationalPoint` (module `OpenCellPoints`),
  with `IsOpenUnits F` obtained as in public `FlagQuotientComparison`.
- `U(χ)(F) ≤ P(χ)(F)`: public `RationalPoint.unipotent_le_parabolic`.
- `ξ(t)` normalizes `P(χ)(F)`: it lies in `Z(χ)(F) ≤ P(χ)(F)` (public `levi_le_parabolic`), and
  a subgroup normalizes itself (`Subgroup.le_normalizer`).
- `ξ(t)` normalizes `U(χ⁻¹)(F)`: public `centralizer_inverseCocharacter` gives
  `ξ(t) ∈ Z(χ⁻¹)(F)`, and public `levi_le_normalizer_unipotent` for `χ⁻¹` applies.
- Contraction of exactly `U(ξ)(F)` by `ξ(t)`, and of `U(χ)(F)` by `χ(t)`:
  `mem_unipotent_iff_tendsto_conj`.
- `P(χ)(F) = Z(χ)(F) U(χ)(F)`: public `RationalPoint.existsUnique_levi_mul_unipotent`.
- `χ(t)` commutes with `Z(χ)(F)`: public `commute_cocharPoint` and the bridge.
- `U(ξ)(F)` is closed: public `isClosed_unipotentPoints`, with the Hausdorff instance
  `localField_t2Space`.
- `χ(t)` normalizes `U(ξ)(F)`: `hξ` and public `commute_cocharPoint` show that `χ(t)` commutes
  with `ξ(t)`; apply `mem_normalizer_unipotent_of_commute`.
- `Z(χ)(F) ∩ U(ξ)(F) = 1`: `hZU`.

**`unipotentIntersectionProduct`.** This is `productHomeomorph` of the structure above; its
application formula holds by definition.

## Scope

The hypotheses `hξ` and `hZU` are not proved here for any particular pair of cocharacters; for
two parabolics with a common Levi they must be derived from the parabolic data. The module does
not identify supplied radicals or Levi subgroups with dynamic subgroups, and it says nothing
about Haar measures on the factors or on the quotient `(U ∩ U') \ U'`, or about convergence of
intertwining integrals.
