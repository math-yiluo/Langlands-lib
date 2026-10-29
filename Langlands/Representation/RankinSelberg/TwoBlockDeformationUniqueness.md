# Uniqueness of inverse-character functionals on the deformed induction

Module `Langlands.Representation.RankinSelberg.TwoBlockDeformationUniqueness`,
namespace `Langlands.RankinSelberg.TwoBlockDeformation`.

This is a helper module for the proof of
`Langlands.RankinSelberg.TwoBlockWhittakerDeformationStatement` (JPSS 1983,
Section (4.5)). It contains:

- the transport of full Whittaker type and of inverse-character functionals
  through the deformation twist `|det|^u`;
- a nonzero inverse-character functional on each block;
- a conditional proof that every deformed induction `ρ_u` has full
  inverse-standard Whittaker type, so that its inverse-character functionals
  form a line.

The conditional results take the proposition
`Langlands.RankinSelberg.NormalizedProductWhittakerTypeStatement` as an explicit
hypothesis `H`. This module does not prove `H`. It also proves no analytic,
integral or stabilizer statement.

## Provenance

JPSS (source ID `jpss-1983-rankin-selberg`) define representations of
Whittaker type in Section (2.1). They state in Section (2.3) that
normalized parabolic induction preserves this class, and they use that fact
for `ρ_u` in Section (4.5) (printed pages 408–409). In the Library, the
upper-block, standard-character form of the (2.3) assertion is the published
proposition `NormalizedProductWhittakerTypeStatement`. Its proof is a separate
task. Here it is only an assumption.

The target lemma uses the lower parabolic `Q̄`, as in JPSS Section (3.1)
(printed page 404), and the inverse character `ψ⁻¹`, as on page 409. The work
in this module is converting between these conventions. All three conversions
use published Library results:

1. Lower normalized induction of a block tensor is equivalent to upper
   normalized induction of the reversed block family
   (`Langlands.glOppositeProductReversal`).
2. Full Whittaker type is invariant under equivalence of representations
   (`IsOfWhittakerType.of_equiv`).
3. Full standard type and full inverse-standard type agree for the same
   representation (`isOfWhittakerType_standard_iff_inverse`, through the
   character change at `-1`).

The twist `|det|^u` keeps full type by `isOfWhittakerType_twist_iff`. These
statements are internal adapters. None of them is quoted from the source.

## Setting

Let `p` be prime, `F : PadicField.{uF} p`, `T = F.canonicalTopologicalData`,
and give `F.Carrier` the topology `T.topology`. Let `m : Fin 2 → ℕ`,
`h : ∑ i, (m i + 1) = t + 1`, and `W : Fin 2 → Type uW` be complex vector
spaces carrying representations `σ i` of `GeneralLinear (m i + 1) F.Carrier`.
Let `ψ` be a unitary additive character of `F.Carrier`. The hypothesis `hσ`
says that every `σ i` has full standard Whittaker type:
`IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)`. Full type means
admissible, finitely generated over the group algebra, and with a space of
Whittaker functionals linearly equivalent to `ℂ`. The blocks may be reducible.
`twoBlockDeformedBlocks F m σ u` and `twoBlockDeformedInduced F m h σ u` are the
published deformed blocks and the deformed lower induction `ρ_u` of the target
module.

## Results

- `twoBlockDeformedBlocks_isOfWhittakerType_iff F m σ u i θ`: for every complex
  `u`, every block index `i` and every character `θ` of the upper unipotent
  subgroup of `GeneralLinear (m i + 1) F.Carrier`, the deformed block
  `twoBlockDeformedBlocks F m σ u i` has full Whittaker type for `θ` iff `σ i`
  does.

  *Proof.* The deformed block is `twist χ (σ i)`, where `χ` is the published
  determinant power `T.determinantComplexPower (m i + 1) s` and `s` is `u` or
  `0`. `χ` has open kernel (`isOpen_ker_determinantComplexPower`). It is
  trivial on upper unipotent matrices
  (`determinantComplexPower_upperUnipotent`, from the published
  `TwoBlockJacquetConvergenceStatement` module), because these have
  determinant `1`. Then `isOfWhittakerType_twist_iff` gives the equivalence.

- `exists_block_inverse_functional F m ψ σ hσ i`: there is
  `l : glInverseFunctionals ψ (m i) (σ i)` with `l.val ≠ 0`.

  *Proof.* `isOfWhittakerType_standard_iff_inverse` turns `hσ i` into full
  inverse-standard type of `σ i`. `IsOfWhittakerType.exists_ne_zero` then gives
  a nonzero functional. The canonical field is a topological ring, as the
  character-change result requires. This instance comes from the canonical
  valuative relation and local-field structure (private lemma
  `isTopologicalRing`).

- `deformedBlockFunctional F m ψ σ u i l`: for every complex `u`, a block index
  `i` and `l : glInverseFunctionals ψ (m i) (σ i)`, this is the same linear map
  as an element of
  `glInverseFunctionals ψ (m i) (twoBlockDeformedBlocks F m σ u i)`. The simp
  lemma `deformedBlockFunctional_val` states that its value is `l.val`
  (`rfl`). It is the published `twistFunctional` for the determinant power.
  It is well defined because the power is trivial on upper unipotent matrices
  (`determinantComplexPower_upperUnipotent`). So the block functionals do not
  depend on `u`.

- `isOfWhittakerType_twoBlockDeformedInduced F m h H ψ σ hσ u`: assuming
  `H : NormalizedProductWhittakerTypeStatement.{uF, uW}`, for every complex `u`
  the representation `twoBlockDeformedInduced F m h σ u` has full Whittaker type
  for `inverseStandardCharacter ψ t`.

  *Proof.* By the first result, every deformed block has full standard type,
  so in particular it is smooth (the first conjunct of admissibility).
  `glOppositeProductReversal`, applied to the shape `succBlockShape m h` and
  the deformed blocks, gives an equivalence `E` from `ρ_u` to
  `T.normalizedProductInduced (succBlockShape m h).reverse` of the reversed
  family `i ↦ twoBlockDeformedBlocks F m σ u i.rev`. The reversed shape is
  definitionally `succBlockShape (fun i => m i.rev) h'` with
  `h' : ∑ i, (m i.rev + 1) = t + 1`. Here `h'` is obtained from `h` by
  reindexing the sum along `Fin.revPerm`. `H` applied to `k = 2`, the
  sizes `m i.rev`, the carriers `W i.rev` and the reversed deformed blocks
  gives full standard type of this upper induction. `IsOfWhittakerType.of_equiv`
  with `E.symm` transports it to `ρ_u`. `isOfWhittakerType_standard_iff_inverse`
  converts standard to inverse-standard type.

- `functional_eq_smul F m h H ψ σ hσ u ℓ ℓ' hℓ`: assuming `H`, for every complex
  `u` and inverse-character functionals
  `ℓ ℓ' : glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ u)` with
  `ℓ.val ≠ 0`, there is `c : ℂ` with `ℓ'.val = c • ℓ.val`.

  *Proof.* `IsOfWhittakerType.eq_smul` applied to the previous result gives
  `ℓ' = c • ℓ` in the functional submodule. Taking underlying linear maps gives
  the claim.

## Intended use

The deformation proof is meant to compare a nonzero inverse-character
functional on each `ρ_u` with the given functional `ℓ₀` at `u = 0` through
`functional_eq_smul`, and to use the block functionals of
`exists_block_inverse_functional` when contracting the block tensor. Those
steps are in other modules, not here. Every result here that uses `H` keeps it
as an explicit hypothesis. Using them unconditionally requires a published
proof of `NormalizedProductWhittakerTypeStatement`.
