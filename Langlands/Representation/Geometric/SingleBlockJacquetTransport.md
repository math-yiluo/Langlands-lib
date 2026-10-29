# The single-block normalized refined Jacquet comparison

Author: Worker 938.

Let `C : GeneralLinear.BlockShape n` have one block (`hC : C.length = 1`) and let
`D : Geometric.BlockRefinement C` be an arbitrary refinement. The published
`Langlands.Group.GL.SingleBlock` turns `D` into the block shape
`B := C.singleBlockRefinementEquiv hC D` of the whole group `GL_n`: it is the refinement
of the sole block, cast to rank `n`. This module compares the actual refined objects of
`D` with the actual standard objects of `B`. For an arbitrary complex representation
`ρ : Representation ℂ (GeneralLinear n F.Carrier) V`, put
`σ := ρ.comp (C.leviEmbedding F.Carrier)`. The main construction is

```lean
T.singleBlockNormalizedRefinedJacquetEquiv C hC D ρ :
  (T.normalizedRefinedJacquet C D σ).Equiv
    ((T.normalizedJacquet B ρ).comp (C.singleBlockRefinedLeviEquiv hC F.Carrier D).toMonoidHom)
```

in `Langlands.PadicField.TopologicalData`. It is a `Representation.Equiv`, built from
the published Library objects, not a replacement abstract representation. The module
also gives the block-scalar version and transports generalized eigencharacters, Jacquet
exponents and the absolute-value chamber predicates.

Provenance: this is a derived internal construction for type-A Levi bookkeeping. The
underlying fact is standard: for a one-block shape, the Levi is all of `GL_n`, and a
refinement of its block is a standard parabolic of `GL_n`. No literature source states
these Lean maps, so none is cited. Every declaration is a definition or a proved theorem.
No declaration takes a theorem-valued comparison hypothesis.

Scope: `p` is any prime and `F : PadicField.{uF} p` has compatible topological data `T`.
The representation carrier `V : Type uV` lives in an independent universe. `ρ` is
arbitrary: no smoothness, admissibility, irreducibility, nontriviality, finite length or
finite dimension is assumed. `D` is an arbitrary refinement, and the group-level
statements hold over any commutative ring. The scalar coordinate equivalence works for
any monoid `M`. The rank-zero shape cannot occur, since `C.length = 1`. No smooth
corollary is stated, so nothing here uses smoothness.

## Generic character-space transport (namespace `Langlands`)

These lemmas hold for a commutative ring `R`, monoids `A` and `A'`, and representations
`π` on `V` and `σ` on `W`. The universes are arbitrary.

- `equiv_apply_mem_characterSpace_iff (e : π.Equiv σ) χ k v`:
  `e v ∈ characterSpace σ χ k ↔ v ∈ characterSpace π χ k`. The forward direction is the
  published `map_mem_characterSpace_of_intertwiningMap` (from
  `Filtration.GeneralizedEigencharacterProof`), applied to `e`. The backward direction
  applies it to `e.symm`.
- `map_characterSpace_of_equiv e χ k`: the image of `characterSpace π χ k` under `e` is
  `characterSpace σ χ k`.
- `characterSpace_comp_mulEquiv π f χ k`, for `f : A' ≃* A`: the character space of
  `π.comp f` and `χ.comp f` equals that of `π` and `χ`, for the same power `k`.
- `isGeneralizedEigencharacter_comp_mulEquiv_iff π f χ`: the matching iff for
  `IsGeneralizedEigencharacter`, whose definition takes one common natural power. This
  is needed in both directions. The published `isGeneralizedEigencharacter_comp` only
  goes one way and is reached through a classification import.

## Group transport (namespace `Langlands.GeneralLinear.BlockShape`)

- `singleBlockUnique C hC`: the `Unique (Fin C.length)` instance whose element is
  `C.singleBlockIndex hC`.
- `singleBlockRefinedLeviEquiv C hC R D : Geometric.refinedLevi R C D ≃* B.Levi R`, for
  any commutative ring `R`. It is the inverse of the published
  `Geometric.refinedLeviEquiv R C D` followed by `MulEquiv.piUnique`. So it sends a
  refined Levi element `m` to its inner block coordinates at the sole block
  (`singleBlockRefinedLeviEquiv_apply`, true by `rfl`). The target `(D i0).Levi R` is
  definitionally `B.Levi R`, because `rankCast` keeps the block sizes.
- `leviEmbedding_refinedLeviEquiv_symm_singleBlockIndex`: embedding those coordinates
  block-diagonally gives back the sole block `m.val i0`.
- `singleBlockRefinedLeviEquiv_leviEmbedding`: compatibility with the two actual
  embeddings into `GL_n`:
  `B.leviEmbedding R (singleBlockRefinedLeviEquiv m) = C.leviEmbedding R m.val`.
  The proof compares matrix entries. Every row or column index of `B` is
  `B.index j a`. `singleBlockRefinement_index` rewrites it as
  `C.index i0 ((D i0).index j a)`. The published `leviEmbedding_apply_same` and
  `leviEmbedding_apply_ne` then handle equal and distinct inner blocks.

## Scalar coordinates and order

- `singleBlockFlattenOrderIso C hC D : Fin B.length ≃o Fin (C.flatten D).length`
  sends `j` to `C.flattenBlockEquiv D ⟨C.singleBlockIndex hC, j⟩`
  (`singleBlockFlattenOrderIso_apply`). Its underlying bijection is
  `Equiv.uniqueSigma` followed by the published `flattenBlockEquiv`. It is an order
  isomorphism by the published `flattenBlockEquiv_lt_iff`. This is the formal record that
  the coordinate change keeps the order of the sole refined block.
- `singleBlockScalarMulEquiv C hC D M : (Fin (C.flatten D).length → M) ≃* (Fin B.length → M)`,
  for any monoid `M`. The `j`-th ordinary coordinate of `a` is the flattened coordinate
  `a (C.flattenBlockEquiv D ⟨C.singleBlockIndex hC, j⟩)`
  (`singleBlockScalarMulEquiv_apply`). The inverse formula is
  `singleBlockScalarMulEquiv_symm_apply`.
- `singleBlockScalarEquiv C hC D M`: the same map as a continuous multiplicative
  equivalence `≃ₜ*` for any topology on `M`, with the product topologies. Both
  directions are coordinate projections. `singleBlockScalarEquiv_toMulEquiv` and
  `coe_singleBlockScalarEquiv` say that its underlying map is
  `singleBlockScalarMulEquiv`.
- `singleBlockRefinedLeviEquiv_flattened_blockScalarLevi`: for
  `a : Fin (C.flatten D).length → Rˣ`,
  `singleBlockRefinedLeviEquiv (flattenedLeviEquiv R C D ((C.flatten D).blockScalarLevi R a))`
  equals `B.blockScalarLevi R (singleBlockScalarMulEquiv a)`. So the flattened block
  scalars are the ordinary block scalars after this coordinate change. The proof uses the
  published `flattenedLeviProductEquiv_apply_symm`.
- Order consequences, for any function `f` on the flattened indices:
  `singleBlock_monotone_comp_iff` (monotone in the ordinary numbering iff monotone in the
  flattened one), `singleBlock_exists_ne_comp_iff` (nonconstancy), and
  `singleBlock_forall_block_monotone_iff` (blockwise monotone in the flattened numbering
  iff monotone in the ordinary numbering; there is only one outer block).

## The actual quotient comparison

`singleBlockRefinedJacquetLinearEquiv C hC D ρ` is a linear equivalence
`Geometric.RefinedJacquetModule C D σ ≃ₗ[ℂ] B.JacquetModule ρ`, for any commutative ring
`F`. Both directions use the published universal property `Jacquet.lift` of the two
actual coinvariant quotients:

- Forward: lift `B.jacquetMk ρ` through the refined quotient. A refined unipotent `u`
  satisfies `C.leviEmbedding u ∈ B.unipotentSubgroup` by the published
  `singleBlock_mem_refinedUnipotent_iff`, so `Jacquet.mk_apply_subgroup` shows that
  `B.jacquetMk` kills `ρ(u) v - v`.
- Backward: lift `Geometric.refinedJacquetMk C D σ` through the standard quotient. Every
  element of `B.unipotentRadical` is `C.leviEmbedding m` for some `m`, by the published
  `singleBlock_leviEmbedding_surjective`. The same iff puts `m` in the refined unipotent
  subgroup.

The two composites are the identity on quotient classes, by `rfl`.
`singleBlockRefinedJacquetLinearEquiv_mk` and `..._symm_mk` state that the class of a
vector `v` goes to the class of the same `v` in each direction.

## The normalized comparison (namespace `Langlands.PadicField.TopologicalData`)

- `singleBlock_refinedLeviModulus`: `T.refinedLeviModulus C D m` equals
  `T.leviModulus B (singleBlockRefinedLeviEquiv m)`. The refined modulus is a product over
  the outer blocks, and only the sole block contributes (`Fintype.prod_eq_single`).
  The remaining factor is the standard modulus of `B` by `rfl`.
- `singleBlockNormalizedRefinedJacquetEquiv C hC D ρ`: the representation equivalence
  above, with underlying linear map `singleBlockRefinedJacquetLinearEquiv`. Each side
  keeps its own normalization. On the refined side,
  `normalizedRefinedJacquet_mk` multiplies by `(sqrt (T.refinedLeviModulus C D m))⁻¹`.
  On the standard side, `normalizedJacquet_mk` multiplies by
  `(sqrt (T.leviModulus B (singleBlockRefinedLeviEquiv m)))⁻¹`. These factors agree by
  `singleBlock_refinedLeviModulus`. The group elements agree by
  `singleBlockRefinedLeviEquiv_leviEmbedding`. The class formulas
  `singleBlockNormalizedRefinedJacquetEquiv_mk` and `..._symm_mk` are `rfl`.
- `singleBlockScalarJacquetEquiv C hC D ρ`: the scalar-action equivalence. Its source is
  the refined action pulled back through
  `(flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp ((C.flatten D).blockScalarLevi F.Carrier)`,
  which is the expression the consumer uses. Its target is
  `(T.splitCentreJacquet B ρ).comp (singleBlockScalarMulEquiv C hC D F.Carrierˣ).toMonoidHom`.
  The underlying linear equivalence is again the quotient comparison
  (`singleBlockScalarJacquetEquiv_mk`). The intertwining law follows from that of the
  normalized comparison and the block-scalar identity above.

## Characters, exponents and chambers

In what follows, `χ` is an arbitrary character of the ordinary scalars `Fin B.length →
F.Carrierˣ`, `ψ` is an arbitrary character of the flattened scalars, and the refined
scalar action is the source of `singleBlockScalarJacquetEquiv`.

- `singleBlock_mem_characterSpace_iff` and `singleBlock_map_characterSpace`: the quotient
  comparison identifies `characterSpace` of the refined scalar action at
  `χ.comp singleBlockScalarMulEquiv` with `characterSpace` of `T.splitCentreJacquet B ρ`
  at `χ`, with the same power `k`, as a vector-wise iff and as an equality of submodules.
- `singleBlock_isGeneralizedEigencharacter_iff` (from `χ`) and
  `..._iff_flattened` (from `ψ`, compared with `ψ.comp singleBlockScalarMulEquiv.symm`):
  `IsGeneralizedEigencharacter` corresponds in both directions, with the same common
  natural power. The proof combines the published `isGeneralizedEigencharacter_iff_of_equiv`
  with `isGeneralizedEigencharacter_comp_mulEquiv_iff`.
- `singleBlock_isOpen_ker_iff`: for the topology `T.topology`, the kernel of
  `χ.comp singleBlockScalarMulEquiv` is open iff the kernel of `χ` is open. It is the
  preimage under the homeomorphism `singleBlockScalarEquiv`.
- `singleBlock_isJacquetExponent_iff`: `T.IsJacquetExponent B ρ χ` holds iff the flattened
  pullback of `χ` has open kernel and is a generalized eigencharacter of the refined
  scalar action. `singleBlock_isJacquetExponent_iff_flattened` states the same thing
  starting from `ψ`. `IsJacquetExponent` is the published definition (open kernel and
  occurrence in `splitCentreJacquet`), unchanged.
- `singleBlockScalar_monotone_normalizedAbs_iff`,
  `singleBlockScalar_exists_normalizedAbs_ne_iff` and
  `singleBlockScalar_forall_block_monotone_iff`: for flattened scalars `a`,
  `Monotone (fun j => T.normalizedAbs (singleBlockScalarMulEquiv a j))` is equivalent to
  `Monotone (fun k => T.normalizedAbs (a k))`. The same holds for nonconstancy
  (`∃ i j, … ≠ …`). The refined blockwise monotone condition is equivalent to the ordinary
  one. These are the Monotone absolute-value chamber and nonconstancy predicates.

No exponent criterion, square-integrability or temperedness statement is proved or
assumed here.

## Import-closure audit

Direct imports: `Langlands.Representation.Geometric.FlattenedLevi`,
`Langlands.Representation.Geometric.RefinementFunctors`,
`Langlands.Representation.Exponents.Jacquet` and
`Langlands.Representation.Filtration.GeneralizedEigencharacterProof`. At Library commit
`e40be87d4e73ac457e91929eddf904bd95d12d2f`, the transitive closure has 64 `Langlands`
modules. They are all unchanged published Lean/Markdown pairs:

- `Group.GL`: `Basic`, `BlockIwahoriDefinitions`, `BlockModulus`, `Blocks`, `Maps`,
  `NormalizedCharacter`, `OppositeBlocks`, `Padic`, `PadicBlocks`, `SingleBlock`.
- `LocalField`: `Canonical`, `Definitions`, `Topology`, `Normalization.Definitions`,
  `Normalization.Statement`, `Normalization.Proof`.
- `Representation.Category`: `Basic`, `Twist`.
- `Representation.Classification`: `Supercuspidal`, `SupercuspidalTwist`.
- `Representation.CuspidalSupport`: `LeviDefinitions`, `MinimalJacquetStatement`,
  `MinimalJacquetProof`.
- `Representation.Exponents.Jacquet`.
- `Representation.Filtration`: `Definitions`, `GeneralizedEigencharacterStatement`,
  `GeneralizedEigencharacterProof`.
- `Representation.Geometric`: `FlattenedLevi`, `RefinementDefinitions`,
  `RefinementFunctors`, `WeylDefinitions`.
- `Representation.Induction.Definitions`.
- `Representation.Jacquet`: `CharacterTwistEquiv`, `Coinvariants`, `Normalized`,
  `Parabolic`, `PositiveCharacter`, `SmoothTwist`.
- `Representation.Parabolic`: `RefinementCharacter`, `RefinementComposition`,
  `RefinementPreimage`.
- `Representation.Smooth`: `Definitions`, `FixedVectors.Definitions`,
  `SmoothPart.Definitions`, `Admissibility.CofinalStatement`/`CofinalProof`,
  `Admissibility.EquivalenceStatement`/`EquivalenceProof`,
  `Transfer.PullbackStatement`/`PullbackProof`,
  `Transfer.SubquotientStatement`/`SubquotientProof`.
- `Representation.Twist`: `Definitions`, `RealPower`, `SubquotientDefinitions`, and the
  `Admissibility`, `Algebra`, `Smooth` and `Subquotient` statement/proof pairs.
- `Representation.Unitary.Basic`.

The closure contains none of the excluded work:

- no segment, multisegment, ordered-multisegment, tempered-block, square-integrable or
  regular Langlands classification module;
- no tempered support, exhaustion, unitarity or genericity module;
- no weakly-critical module and no equal-exponent grouping module;
- no `Jacquet.ReciprocityProof` and no `CuspidalSupport.LeviAdmissibleFactorizationProof`.

The two `Classification` modules define the supercuspidal predicate and class sets and
prove that they are invariant under equivalence and determinant twists. No excluded task
owns them, and this module uses nothing from them. `Unitary.Basic` only defines
`IsUnitarizable`. `CuspidalSupport.MinimalJacquetProof`
enters only through `FlattenedLevi`, which uses only its `flatten`, `flattenBlockEquiv`
and `flattenBlockEquiv_lt_iff`. This module uses those three and no Jacquet-descent
result. `Filtration.GeneralizedEigencharacterProof` adds three modules of generic linear
algebra. From it the module uses `map_mem_characterSpace_of_intertwiningMap` and
`isGeneralizedEigencharacter_iff_of_equiv`. The module does not import
`Classification.SegmentQuotientJacquetSingleBlock`,
`Classification.ProductLeviDualOppositeAdapter` or
`Classification.InverseTransposeAnalyticProof`.
