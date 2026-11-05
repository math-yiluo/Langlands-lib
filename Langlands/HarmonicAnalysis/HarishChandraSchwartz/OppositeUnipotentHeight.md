# Heights on opposite unipotent points bounded by a weight-vector displacement

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.OppositeUnipotentHeight`.
Declarations are in the namespaces `Langlands.HarishChandraSchwartz` and
`Langlands.GroupScheme.MatrixRepresentation`, as listed below.

## Purpose and provenance

Provenance: internal. This module removes the diagonal hypotheses from
`exists_rationalMatrixNorm_le_of_diagonal` in
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.OppositeUnipotentDisplacement`. The result
is a height comparison used for II.2 (6) in J.-L. Waldspurger, *La formule de Plancherel pour
les groupes p-adiques, d'après Harish-Chandra* (2003), printed p. 254 (PDF p. 20).
Waldspurger's argument there uses polynomial estimates and the closedness of unipotent orbits.
That route is not transcribed. Here every cocharacter of a general linear group is conjugated
to a diagonal one (public `exists_innerIso_comp_eq_diagonalCocharacter`), and the diagonal
case is applied to the conjugated representations.

The main theorem `exists_rationalMatrixNorm_le_of_weightVector` concerns the opposite unipotent
subgroup `Ū = U(χ⁻¹)` of a cocharacter `χ`. Let `v` be an eigenvector of every `ρ(χ(t))`, and
suppose that `ρ(ū) v = v` holds for no `ū ∈ Ū(F)` other than `1`. Then the height of
`ū ∈ Ū(F)` in a closed matrix representation `ρ₀` is at most `C * max 1 ‖ρ(ū) v‖ ^ D`.
Neither `ρ₀` nor `ρ` has to be diagonal for `χ`.

## Setting and notation

- `F` is a field. In the local-field part it carries `[ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]`, and `G` is a group scheme over `Spec F` with affine
  underlying scheme.
- `|·|` is `LocalField.residueNormalizedAbsoluteValue F`, and vectors `n → F` carry the sup
  norm `rationalVectorNorm F` for it.
- `ρ.rationalMatrix x` is the matrix of the rational point `x` in the representation `ρ`.
  `gmRationalPoint t` is the rational point of `𝔾_m` given by `t : Fˣ`, so that
  `gmRationalPoint t ≫ χ` is the point `χ(t)` of `G`.
- `diagonalUnits F e t` is `diag(t ^ e i)`. `glNorm` is the largest absolute value of an entry
  of a matrix or of its inverse, and `rationalMatrixNorm F ρ x` is `glNorm (ρ.rationalMatrix x)`.
- `Int(g)` is the inner automorphism `(groupScheme n F).innerIso g` of `GL_n`, and `M g` is
  the rational matrix of a rational point `g` of `GL_n` in the identity representation.
- `Ū(F)` is written in Lean as
  `(Dynamic.unipotent (CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫ χ)).rationalPoints`.

## Declarations

### Weight blocks and matrix bounds (`Langlands.HarishChandraSchwartz`)

`F` is a normed field and `n` a finite type.

- `exists_weight_block_of_mulVec_eq_smul`: if `‖t‖ ≠ 1` and
  `diagonalUnits F e t *ᵥ w = c • w`, then there is `m : ℤ` with `w k = 0` whenever
  `e k ≠ m`. So an eigenvector of `diag(t ^ e i)` lies in one weight block.
- `exists_norm_mulVec_le` (for ultrametric `F`): every square matrix `A` has a constant
  `K ≥ 0` with `‖A *ᵥ y‖ ≤ K * ‖y‖` for all vectors `y`.

### Conjugate representations (`Langlands.GroupScheme.MatrixRepresentation`)

`F` is a field, `G` a group scheme over `Spec F`, `ρ` a matrix representation of `G` on `n`,
and `g` a rational point of `GL_n`.

- `rationalMatrix_comp_innerIso_mulVec`: the matrix of `ρ ≫ Int(g)` at `x`, applied to
  `M g *ᵥ v`, equals `M g *ᵥ (ρ.rationalMatrix x *ᵥ v)`.
- `rationalMatrix_eq_conj_comp_innerIso`:
  `ρ.rationalMatrix x = (M g)⁻¹ * rationalMatrix (ρ ≫ Int(g)) x * M g`.
- `IsCocharacterEigenvector χ ρ v` (definition, a proposition): for every `t : Fˣ` there is
  `c : F` with `ρ.rationalMatrix (gmRationalPoint t ≫ χ) *ᵥ v = c • v`. In words, `v` spans
  a line stable under `ρ(χ(t))` for every `t`, or `v = 0`.

### Local fields (`Langlands.GroupScheme.MatrixRepresentation`)

`exists_rationalMatrixNorm_le_of_weightVector` (main theorem). Its hypotheses:

- `χ : 𝔾_m ⟶ G` is a cocharacter;
- `ρ₀` is a closed representation (`IsClosedSubgroup ρ₀`) on `Fin N` with `N` positive;
- `ρ` is a representation on a finite type `n`, and `v : n → F` satisfies
  `IsCocharacterEigenvector χ ρ v`;
- for `x ∈ Ū(F)`, `ρ.rationalMatrix x *ᵥ v = v` implies `x = 1`.

It concludes that there are `C > 0` and `D : ℕ` with
`rationalMatrixNorm F ρ₀ x ≤ C * max 1 (rationalVectorNorm F (ρ.rationalMatrix x *ᵥ v)) ^ D`
for every `x ∈ Ū(F)`.

## Proofs as implemented

**Weight blocks.** Suppose `w k₀ ≠ 0` and set `m = e k₀`. If also `w k ≠ 0` with
`e k ≠ m`, comparing coordinates gives `t ^ e k = c = t ^ e k₀`. Taking norms gives
`‖t‖ ^ e k = ‖t‖ ^ e k₀`, and since `‖t‖` is positive and different from `1`, the map
`z ↦ ‖t‖ ^ z` is injective (`zpow_right_injective₀`). This is a contradiction. If `w = 0`,
any `m` works.

**Matrix bounds.** For empty `n` take `K = 0`. Otherwise take `K = entryNorm A` and use
`norm_mulVec_le` from `OppositeUnipotentDisplacement`.

**Conjugate representations.** Both identities follow from `rationalMatrix_comp_innerIso`
(`OppositeUnipotentDisplacement`), which writes the matrix of `ρ ≫ Int(g)` as
`M g * ρ.rationalMatrix x * (M g)⁻¹`, followed by group cancellation in `GL_n(F)`.

**Main theorem.**
1. By `exists_innerIso_comp_eq_diagonalCocharacter` choose rational points `g₀`, `g` and
   weights `e₀`, `e` with `χ ≫ ρ₀ ≫ Int(g₀) = diagonalCocharacter (Fin N) F e₀` and
   `χ ≫ ρ ≫ Int(g) = diagonalCocharacter n F e`. The conjugate `ρ₀ ≫ Int(g₀)` is again
   closed (`IsClosedSubgroup.comp_iso`).
2. Put `w = M g *ᵥ v`. By `rationalMatrix_comp_innerIso_mulVec`, `x` fixes `w` in
   `ρ ≫ Int(g)` exactly when `M g *ᵥ (ρ(x) v) = M g *ᵥ v`. Since `M g` is invertible this
   gives `ρ(x) v = v`, so the trivial-stabilizer hypothesis transfers to `w`.
3. Let `t` be a uniformizer, so that `|t| = q⁻¹ ≠ 1` (`q` the residue cardinality). The
   matrix of `χ(t)` in `ρ ≫ Int(g)` is `diagonalUnits F e t`
   (`rationalMatrix_gmRationalPoint_comp`). With the eigenvalue equation for `v` at `t`
   and step 2, `w` is an eigenvector of `diagonalUnits F e t`. By
   `exists_weight_block_of_mulVec_eq_smul`, `w` lies in one weight block `{e = m}`.
4. `exists_rationalMatrixNorm_le_of_diagonal` for `ρ₀ ≫ Int(g₀)`, `ρ ≫ Int(g)` and `w`
   gives `C > 0` and `D` with
   `rationalMatrixNorm F (ρ₀ ≫ Int(g₀)) x ≤ C * max 1 ‖(ρ ≫ Int(g))(x) w‖ ^ D` on `Ū(F)`.
5. Comparison back. By `rationalMatrix_eq_conj_comp_innerIso`, `glNorm_mul_le` and
   `glNorm_inv`, `rationalMatrixNorm F ρ₀ x ≤ glNorm (M g₀) ^ 2 * rationalMatrixNorm F
   (ρ₀ ≫ Int(g₀)) x`. Let `K` be the constant of `exists_norm_mulVec_le` for `M g`. Then
   `(ρ ≫ Int(g))(x) w = M g *ᵥ ρ(x) v`, so
   `max 1 ‖(ρ ≫ Int(g))(x) w‖ ≤ max 1 K * max 1 ‖ρ(x) v‖`.
   The theorem follows with constant `glNorm (M g₀) ^ 2 * C * max 1 K ^ D` and the same `D`.

## Scope

The trivial-stabilizer hypothesis is assumed, not proved. Supplying it (for example from an
exact Chevalley line stabilizer and `P ∩ Ū = 1`) is left to later work. The eigenvector
hypothesis is only used at a uniformizer. The constants `C` and `D` are not explicit beyond
the description above. No statement about modulus characters or Haar measures is made.
