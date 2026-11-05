# Heights on opposite unipotent points bounded by a line displacement

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.OppositeUnipotentDisplacement`.
Declarations are in the namespaces `Langlands.HarishChandraSchwartz`,
`Langlands.GroupScheme.MatrixRepresentation` and `Langlands.LocalField`, as listed below.

## Purpose and provenance

Provenance: internal. This module proves the diagonal case of a height comparison used for
II.2 (6) in J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra* (2003), printed p. 254 (PDF p. 20). Waldspurger obtains II.2 (6) from
polynomial estimates and the closedness of unipotent orbits. That route is not transcribed
here. Instead the module applies the matrix contraction argument of
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.DiagonalContraction`
(`exists_offIdentityNorm_le_mul_pow`) to actual rational points of an affine group scheme
over a non-archimedean local field.

The main theorem `exists_rationalMatrixNorm_le_of_diagonal` concerns the opposite unipotent
subgroup `Ū = U(χ⁻¹)` of a cocharacter `χ`. Its statement is: if `ρ(ū) w = w` holds for no
`ū ∈ Ū(F)` other than `1`, then the height of `ū ∈ Ū(F)` in a closed matrix representation
`ρ₀` is at most `C * max 1 ‖ρ(ū) w‖ ^ D`. It assumes that `χ` acts diagonally in both `ρ₀`
and `ρ` and that `w` lies in one weight block. Diagonalizing a general cocharacter is not done
in this module.

## Setting and notation

- `F` is a field. In the local-field part it carries `[ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]`, and `G` is a group scheme over `Spec F` with affine
  underlying scheme.
- `rationalPoints G` carries `rationalPointTopology F G.X`.
- `|·|` is `LocalField.residueNormalizedAbsoluteValue F`. Where a norm on `F` is needed,
  it is the normed field structure of this absolute value. Vectors `n → F` carry the sup norm.
- `diagonalUnits F e t` is `diag(t ^ e i)`, and `blockUnipotentSubgroup F (-e)` consists of
  the `g : GL n F` with `g i j = δ i j` whenever `e j ≤ e i`.
- `entryNorm`, `glNorm` (largest entry of a matrix and of its inverse) and `offIdentityNorm`
  (`entryNorm (g - 1)`) come from the `Height` and `DiagonalContraction` modules.
  `rationalMatrixNorm F ρ g` is `glNorm (ρ.rationalMatrix g)` for this norm.
- `Ū(F)` is written in Lean as
  `(Dynamic.unipotent (CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫ χ)).rationalPoints`.

## Declarations

### Inverses of block unipotent matrices (`Langlands.HarishChandraSchwartz`)

`F` is a normed field, `n` a finite type with decidable equality, `e : n → ℤ`, and `g` lies
in `blockUnipotentSubgroup F (-e)`.

- `sub_one_pow_apply_eq_zero`: `((g - 1) ^ k) i j = 0` whenever `e j < e i + k`.
- `sub_one_pow_eq_zero`: if `d : ℕ` bounds the weight gaps (`e j - e i ≤ d` whenever
  `e i < e j`), then `(g - 1) ^ (d + 1) = 0`.
- `coe_inv_eq_sum`: under the same gap bound, `g⁻¹ = ∑_{k ≤ d} (-(g - 1)) ^ k`.
- `entryNorm_neg` (for nonempty `n`): `entryNorm (-X) = entryNorm X`.

The remaining lemmas of this group assume in addition that `F` is ultrametric
(`IsUltrametricDist F`) and `n` nonempty.

- `entryNorm_pow_le`: `entryNorm (X ^ k) ≤ max 1 (entryNorm X) ^ k` for any square matrix
  `X`.
- `entryNorm_le_max_offIdentityNorm`: `entryNorm g ≤ max 1 (offIdentityNorm g)` for any
  `g : GL n F`.
- `entryNorm_inv_le`: for `g` block unipotent for `-e` with gap bound `d`,
  `entryNorm g⁻¹ ≤ max 1 (offIdentityNorm g) ^ d`.
- `glNorm_le_max_offIdentityNorm_pow`: under the same hypotheses,
  `glNorm g ≤ max 1 (offIdentityNorm g) ^ (d + 1)`.
- `norm_mulVec_le`: `‖A *ᵥ y‖ ≤ entryNorm A * ‖y‖` for a square matrix `A` and a vector
  `y` (sup norm).

### Rational matrices (`Langlands.GroupScheme.MatrixRepresentation`)

`F` is a field, `G` a group scheme over `Spec F`, and `ρ` a matrix representation of `G`.

- `gmRationalPoint t` (definition, for `t : Fˣ`) is the rational point of
  `𝔾_m` over `Spec F` corresponding to `t`, via `Gm.pointsEquiv` and the inverse of
  `Scheme.ΓSpecIso`.
- `rationalMatrix_gmRationalPoint_comp`: if `χ ≫ ρ = diagonalCocharacter n F e`, then
  `ρ.rationalMatrix (gmRationalPoint t ≫ χ) = diagonalUnits F e t`.
- `rationalMatrix_comp_innerIso`: for a rational point `g` of `GL_n`, the rational matrix of
  `ρ ≫ Int(g)` at `x` is `M g * ρ.rationalMatrix x * (M g)⁻¹`, where `M g` is the rational
  matrix of `g` under the identity representation.
- `rationalMatrix_mem_blockUnipotentSubgroup_iff`,
  `rationalMatrix_mem_blockParabolicSubgroup_iff`: `ρ.rationalMatrix x` lies in the block
  unipotent (resp. block parabolic) subgroup for `e` over `F` exactly when the matrix of
  `x ≫ ρ` over `Γ(Spec F, ⊤)` lies in the corresponding subgroup there.

### Continuity of sup norms (`Langlands.HarishChandraSchwartz`)

- `continuous_entryNorm_comp`: `x ↦ entryNorm (M x)` is continuous if every
  `x ↦ ‖M x i j‖` is.
- `continuous_norm_pi_comp`: `x ↦ ‖f x‖` is continuous if every `x ↦ ‖f x k‖` is.

Neither lemma uses a topology on `F`.

### Local fields (`Langlands.LocalField`)

- `vle_of_residueNormalizedAbsoluteValue_le`: `|x| ≤ |y|` implies `x ≤ᵥ y`.
- `isCompact_residueNormalizedAbsoluteValue_le`: `{x | |x| ≤ C}` is compact for every
  real `C`.

### Rational points over a local field (`Langlands.GroupScheme.MatrixRepresentation`)

- `rationalVectorNorm F v` (definition) is the sup norm `max_k |v k|` of `v : n → F`.
- `isCompact_rationalMatrix_entry_le`: for a closed representation `ρ` (`IsClosedSubgroup ρ`)
  on `Fin N` and a real `C`, the set of rational points `g` such that every entry of
  `ρ.rationalMatrix g` and of its inverse has `|·| ≤ C` is compact.
- `continuous_absoluteValue_rationalMatrix_sub_one_apply`: `g ↦ |(ρ(g) - 1) i j|` is
  continuous.
- `continuous_absoluteValue_rationalMatrix_mulVec_sub_apply`: for `w : n → F`,
  `g ↦ |(ρ(g) w - w) k|` is continuous.
- `isClosed_rationalMatrix_mem_blockUnipotentSubgroup`: `{g | ρ(g) ∈ blockUnipotentSubgroup F f}`
  is closed.
- `exists_rationalMatrixNorm_le_of_diagonal` (main theorem). Its hypotheses:
  - `χ : 𝔾_m ⟶ G` is a cocharacter;
  - `ρ₀` is a closed representation on `Fin N` (`N` positive) with
    `χ ≫ ρ₀ = diagonalCocharacter (Fin N) F e₀`;
  - `ρ` is a representation on a finite type `n` with `χ ≫ ρ = diagonalCocharacter n F e`;
  - `w : n → F` vanishes outside `{k | e k = m}`;
  - for `x ∈ Ū(F)`, `ρ(x) w = w` implies `x = 1`.

  It concludes that there are `C > 0` and `D : ℕ` with
  `rationalMatrixNorm F ρ₀ x ≤ C * max 1 (rationalVectorNorm F (ρ(x) w)) ^ D` for every
  `x ∈ Ū(F)`.

## Proofs as implemented

**Block unipotent inverses.** By induction on `k`, an entry of `(g - 1) ^ (k + 1)` at
`(i, j)` is a sum of terms `((g - 1) ^ k) i l * (g - 1) l j`. The first factor vanishes when
`e l < e i + k`. Otherwise `e j ≤ e l`, so the second factor vanishes by block unipotence.
With `k = d + 1` every pair `(i, j)` satisfies `e j < e i + d + 1`, so `g - 1` is nilpotent.
The geometric series identity `mul_neg_geom_sum` then gives the inverse. The ultrametric
bounds follow from submultiplicativity `entryNorm_mul_le` (in `Height`) by induction, and
from the ultrametric inequality for sums. The bound on `entryNorm g` writes
`g i j = (g - 1) i j + δ i j`. The bound on `glNorm` takes the larger of the bounds for `g`
and `g⁻¹`.

**Rational matrices.** `rationalMatrix_gmRationalPoint_comp` rewrites with
`pointsEquiv_diagonalCocharacter` and compares diagonal entries through
`Scheme.ΓSpecIso`. `rationalMatrix_comp_innerIso` reduces both sides to the identity
representation using `rationalMatrix_restrict` and uses `rationalPoints_map_innerIso`. The two
membership transports map block subgroups along the ring isomorphism `Scheme.ΓSpecIso` in
both directions (`map_mem_blockUnipotentSubgroup`, `map_mem_blockParabolicSubgroup`).

**Local fields.** `vle_of_residueNormalizedAbsoluteValue_le` unfolds the absolute value
through the strictly monotone `WithZeroMulInt.toNNReal` and the valuation compatibility. For
compactness, choose `k` with `C < q ^ k` (`q` the residue cardinality). Then the set is a
closed subset of the compact valuation ball of `ϖ⁻ᵏ` (`IsNonarchimedeanLocalField.isCompact_closedBall`).

**Rational points.** `isCompact_rationalMatrix_entry_le` writes the set as the preimage of a
compact product of absolute-value balls under `Units.embedProduct ∘ ρ.rationalMatrix`. This
map is a closed embedding by `isClosedEmbedding_rationalMatrix` for closed representations.
The continuity lemmas use `continuous_rationalMatrix_entry` and
`continuous_residueNormalizedAbsoluteValue`. The closedness lemma writes the locus as an
intersection of equalities of continuous entry functions (`F` is Hausdorff by
`localField_t2Space`).

**Main theorem.** Write `U = Ū(F)`.
1. `x ∈ U` exactly when `ρ₀(x)` is block unipotent for `-e₀`
   (`Dynamic.mem_unipotent_iff_of_diagonal`, which uses that `ρ₀` is a closed immersion). In
   particular `U` is closed.
2. For `x ∈ U`, `ρ(x)` is block unipotent for `-e`. This follows from
   `Dynamic.unipotent_le_comap`, `inv_comp_diagonalCocharacter` and
   `unipotent_diagonalCocharacter`.
3. Let `t` be a uniformizer, so that `|t| = q⁻¹ < 1`, and let `a = χ(t)`. Then
   `ρ₀(a) = diagonalUnits F e₀ t` and `ρ(a) = diagonalUnits F e t`, and `x ↦ a⁻¹ x a`
   preserves `U` (`diagonalUnits_conj_mem`). This map is the `c` of
   `exists_offIdentityNorm_le_mul_pow`, applied on the subtype `U` with
   `r₀ x = ρ₀(x)` and `r x = ρ(x)`.
4. The hypothesis `r x w = w → r₀ x = 1` is the fixed-point hypothesis followed by
   `map_one`. Continuity of `β x = offIdentityNorm (ρ₀ x)` and of `x ↦ ‖ρ(x) w - w‖` is the
   continuity group above.
5. The annulus `{1 ≤ q ^ d β, β ≤ 1}` is a closed subset of `U ∩ K`, where `K` is the compact
   set of `isCompact_rationalMatrix_entry_le` with `C = 1`. The reason: on `{β ≤ 1}` the
   entries of `ρ₀(x)` and `ρ₀(x)⁻¹` have absolute value at most `1`, by
   `entryNorm_le_max_offIdentityNorm` and `entryNorm_inv_le`.
6. This gives `C₁ > 0` with `β x ≤ C₁ ‖ρ(x) w - w‖ ^ d` when `β x ≥ 1`. Set
   `Y = max 1 ‖ρ(x) w‖` and `L = 1 + ‖w‖`. Then `‖ρ(x) w - w‖ ≤ L Y`, so
   `max 1 (β x) ≤ C₂ Y ^ d` with `C₂ = max 1 (C₁ L ^ d)`. Finally
   `glNorm_le_max_offIdentityNorm_pow` gives the theorem with `C = C₂ ^ (d + 1)` and
   `D = d (d + 1)`, where `d` bounds the weight gaps of `e₀` (`exists_weight_gap_le`).

## Scope

The theorem assumes that `χ` is already diagonal in both representations and that `w` is a
single weight vector. It also assumes that the stabilizer of `w` in `Ū(F)` is trivial.
Supplying that stabilizer statement (for example from an exact Chevalley line stabilizer and
`P ∩ Ū = 1`) and removing the diagonal hypothesis by a change of basis are left to later
modules. The constants `C` and `D` are not explicit beyond the description above. No
statement about modulus characters or Haar measures is made.
