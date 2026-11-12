# Opposite-cell integrality from an integral diagonal matrix representation

Author: Worker 4686.

This internal module proves the published
`Langlands.GroupScheme.IntegralModel.DynamicCellIntegralityStatement` (from
`IwasawaCellDynamic.lean`) from a new proposition,
`IntegralDiagonalRepresentationStatement`. That proposition asks for a linear
representation that detects integrality. The module does not prove it, and it
does not prove `MaximalCompactStatement` unconditionally.

## Matrix algebra over a commutative ring

The declarations in `Langlands.GroupScheme.GeneralLinear` work with weights
`e : n → ℤ` on a finite index type and a commutative ring `A`. They use the
published block subgroups `blockUnipotentSubgroup`, `blockParabolicSubgroup`,
the upper threshold blocks `thresholdBlock e c` (rows and columns
`{l | c ≤ e l}`) and the cell minor `cellMinor e`, the product of the
determinants of the threshold blocks over the values of `e`.

* `det_eq_one_of_blockTriangular`: a matrix that is block triangular for a map
  `b` into a linear order, and whose entries agree with the identity matrix
  whenever `b i = b j`, has determinant `1`. The proof uses Mathlib's
  `Matrix.BlockTriangular.det`; every diagonal block is the identity.
* `det_thresholdBlock_of_unipotent_neg`: if `u` is block unipotent for `-e`
  (its entries agree with the identity whenever `e j ≤ e i`), every threshold
  block of `u` has determinant `1`. The block is block triangular for `e`.
* `det_thresholdBlock_of_unipotent`: the same for `w` block unipotent for `e`,
  with the order dual of `e`.
* `cellMinor_mul_eq_one`: for such `u` and `w`, `cellMinor e (u * w) = 1`. The
  published `thresholdBlock_mul_of_right` makes threshold blocks multiplicative
  because `w` is block parabolic for `e`.
* `exists_map_eq_of_mul_mem_range`: let `f : R →+* K` be injective, `u` block
  unipotent for `-e` and `w` block unipotent for `e` over `K`. If `u * w` is
  the image under `f` of an invertible matrix `C` over `R`, then so is `w`.
  Proof: `f` maps `cellMinor e C` to `cellMinor e (u * w) = 1`, so
  `cellMinor e C = 1` by injectivity. The published `exists_cell_decomposition`
  then writes `C = u' p` over `R` with `u'` block unipotent for `-e` and `p`
  block parabolic for `e`. Over `K`, `f(u')⁻¹ u = f(p) w⁻¹` lies in both
  subgroups, whose intersection is trivial by the published
  `blockUnipotentSubgroup_neg_inf_blockParabolicSubgroup`. Hence `w = f(p)`.
* `rationalPointsEquiv_mem_blockUnipotentSubgroup`: a rational point of the
  dynamic unipotent subgroup of the diagonal cocharacter of `e` in `GL_N` over
  any `R` has block unipotent matrix under the published `rationalPointsEquiv`.
  The proof uses `unipotent_diagonalCocharacter` and
  `glRingEquiv_mem_blockUnipotentSubgroup_iff`.

## The statement `IntegralDiagonalRepresentationStatement`

The statement keeps the quantifiers and hypotheses of
`MaximalCompactStatement`: every universe-`u` field `F` with
`[ValuativeRel F]`, `[TopologicalSpace F]` and `[IsNonarchimedeanLocalField F]`,
every `G` over `Spec F` with `IsConnectedReductive G`, and every supplied
`M : IntegralModel 𝒪[F] F G` whose special-fibre pullback
`(GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group` is connected
reductive. For every model cocharacter `χ : Gm ⟶ M.group` over `𝒪[F]` it
asserts the existence of `N : ℕ`, a matrix representation
`ρ : MatrixRepresentation G (Fin N)` over `F`, and weights `e : Fin N → ℤ`
such that

1. `M.genericCocharacter χ ≫ ρ` is the published diagonal cocharacter
   `GeneralLinear.diagonalCocharacter (Fin N) _ e`, and
2. for every `g : rationalPoints G`, `g ∈ M.integralPoints` if and only if the
   matrix `GeneralLinear.rationalPointsEquiv N _ (rationalPoints.map ρ g)` lies
   in the image of `Matrix.GeneralLinearGroup.map (algebraMap 𝒪[F] F)`, that is,
   it is an invertible matrix over `𝒪[F]`.

No closedness of `ρ` over `F` is required.

## Main results

* `dynamicCellIntegralityStatement_of_integralDiagonalRepresentation` proves
  `DynamicCellIntegralityStatement.{u}` from
  `IntegralDiagonalRepresentationStatement.{u}`. Let
  `v ∈ U_G(λ⁻¹)(F)`, `w ∈ U_G(λ)(F)` with `v * w` integral, where
  `λ = M.genericCocharacter χ`. By the published functoriality
  `Dynamic.unipotent_le_comap`, `ρ v` lies in the unipotent subgroup of the
  opposite of `λ ≫ ρ`. That opposite is the diagonal cocharacter of `-e`, by
  `GeneralLinear.inv_comp_diagonalCocharacter`. Similarly `ρ w` lies in that of
  the diagonal cocharacter of `e`. So their matrices are block unipotent for
  `-e` and `e`. Condition 2 makes the matrix of `ρ (v * w)` integral.
  `exists_map_eq_of_mul_mem_range`, with the injective map `𝒪[F] → F`, makes
  the matrix of `ρ w` integral. Condition 2 again gives
  `w ∈ M.integralPoints`.
* `maximalCompactStatement_of_integralDiagonalRepresentation` proves the exact
  `MaximalCompactStatement.{u}` from
  `IntegralDiagonalRepresentationStatement.{u}` and the published
  `LeviMaximalCocharacterStatement.{u}`, through
  `maximalCompactStatement_of_dynamic`.

## Provenance and intended proof of the new statement

The module is derived internally. The cell argument replaces the unipotent
step of Marco Maculan, *Maximality of hyperspecial compact subgroups avoiding
Bruhat–Tits theory*, Ann. Inst. Fourier 67(1) (2017), Lemma 5.2 (printed
pp.14–15 / PDF pp.15–16), registered as
`maculan-2017-hyperspecial-maximality`. Maculan uses a highest-weight section
of a line bundle on the flag variety; here the cell minor of a linear
representation plays that role. The Lean statements are not taken from that
paper.

The intended proof of `IntegralDiagonalRepresentationStatement` is as
follows. The smooth affine group `M.group` over the discrete valuation ring
`𝒪[F]` has a faithful linear representation, that is, a closed immersion into
some `GL_N` over `𝒪[F]`: F. Bruhat and J. Tits, *Groupes réductifs sur un corps
local II*, Publ. Math. IHÉS 60 (1984), 1.4.5 (printed p.25 / PDF p.22),
registered as `bruhat-tits-1984-reductive-local-groups-ii`. Their proof takes a
finitely generated (hence free) subcomodule of the coordinate ring that
generates it as an algebra, by a proposition of Serre, and uses its matrix
coefficients. The cocharacter `χ` acts on this free module by a grading whose
pieces are free over the local ring `𝒪[F]`. A basis adapted to the grading
makes `ρ ∘ χ` diagonal. The base change of this representation to `F`, composed
with the generic identification, gives `ρ`. Condition 2 holds because a closed
immersion over `𝒪[F]` detects integral points.
