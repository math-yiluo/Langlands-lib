# Coordinates for an actual block refinement

This module turns a specified correspondence of nested block coordinates into
isomorphisms of the existing actual Levi and parabolic groups. It is a reusable
construction: it does not construct an adjacent merge or prove that any
particular grouping satisfies its coordinate hypothesis.

## Inputs and conventions

Let `B D : GeneralLinear.BlockShape n` and
`S : Geometric.BlockRefinement D`. The inputs are

- `e : ((i : Fin D.length) × Fin (S i).length) ≃ Fin B.length`,
  a bijection from outer/inner block labels to the original block labels;
- `hs : ∀ a, (S a.1).size a.2 = B.size (e a)`, equality of the corresponding
  block sizes;
- for the ambient comparisons, the exact consecutive-coordinate identity
  `hc : ∀ i k x, D.index i ((S i).index k x) =
  B.index (e ⟨i,k⟩) (Fin.cast (hs ⟨i,k⟩) x)`.

All algebraic constructions use any commutative ring `R : Type u`, with no
field, nontriviality, representation carrier or analytic assumption. The
continuous equivalences additionally use `TopologicalSpace R` and
`IsTopologicalRing R`, with the published matrix, product and subgroup
topologies. The rank may be zero. No order-preservation hypothesis is supplied:
the order properties needed below are proved from `hc`, positivity of all
blocks, and the standard consecutive numbering.

## Exported constructions and intrinsic laws

All declarations are in `Langlands.GeneralLinear.BlockShape`. The common
argument prefix for the group equivalences is `B D S e hs R`. Comparisons
using `hc` take it after `R`. The two order lemmas do not depend on `R`, so
their prefix is `B D S e hs hc`.

| Declaration | Meaning |
| --- | --- |
| `nestedLeviEquiv` | Identifies `B.Levi R` with `∀ i, (S i).Levi R` by the label bijection and matrix reindexing along the size equalities. |
| `nestedLeviEquiv_apply`, `nestedLeviEquiv_entry`, `nestedLeviEquiv_symm_apply` | Explicit forward block, matrix-entry and inverse block formulas, including the direction of every size cast. |
| `leviRefinementEquiv` | Composes that product equivalence with `Geometric.refinedLeviEquiv`, giving `B.Levi R ≃* Geometric.refinedLevi R D S`. |
| `leviRefinementEquiv_val` | Describes the value in each outer block by the actual inner block-diagonal embedding. |
| `nestedLeviEquivContinuous`, `leviRefinementEquivContinuous` | The same multiplicative equivalences, continuous in both directions. |
| `leviEmbedding_leviRefinementEquiv` | The actual ambient matrix `D.leviEmbedding R (leviRefinementEquiv ... m).val` equals `B.leviEmbedding R m`. |
| `refinementBlock_lt_of_outer_lt` | Every original block inside an earlier outer block precedes every original block inside a later outer block. |
| `refinementBlock_strictMono` | Within a fixed outer block, the inner labels map in strictly increasing order to original labels. |
| `composedParabolic_eq_of_coordinates` | `Parabolic.composedParabolic R D S = B.parabolic R` as subgroups of the actual `GeneralLinear n R`. |
| `parabolicRefinementEquiv`, `parabolicRefinementEquiv_val` | The resulting equivalence from the original parabolic to the composed parabolic, retaining the same underlying matrix. |
| `parabolicRefinementEquivContinuous` | That matrix-preserving equivalence with continuity in both directions. |
| `composedLeviProjection_parabolicRefinementEquiv` | Composed projection after the parabolic equivalence equals original projection followed by `leviRefinementEquiv`. |

## Implemented proof

The product equivalence composes `Equiv.piCongrLeft`, componentwise
`GeneralLinear.reindex` along `finCongr hs.symm`, and dependent currying.
Each component reindexing is multiplicative. Its matrix-entry formula is
definitionally the original entry evaluated at the two forward `Fin.cast hs`
coordinates. The inverse block formula follows from the inverse identity for
the equivalence. Forward continuity is componentwise; inverse continuity
uses surjectivity of the label bijection to reduce to the explicit inverse
block formula. The subgroup-valued equivalence reuses
`Geometric.refinedLeviEquiv` and its published continuous version.

For ambient embedding compatibility, each of two arbitrary coordinates is
decomposed into an outer and inner block. In the same block the entry formula
and `hc` agree. In different inner or outer blocks both block-diagonal matrices
have zero entries; injectivity of `e` identifies exactly which labels differ.

To derive the two block-order laws, choose coordinate zero inside each positive
inner block. Standard block numbering compares these coordinates, and `hc`
transfers the comparison to `B`. Monotonicity of `Geometric.blockIndex B`
gives a weak comparison of original block labels; injectivity of `e` makes
it strict.

Membership in the composed parabolic is membership in the actual outer
parabolic together with membership of its diagonal projection in each inner
parabolic. For a forbidden entry of the original parabolic, the column's outer
block is either earlier, equal, or later than the row's outer block. The first
case vanishes by the outer triangularity condition, the second by the inner
condition, and the third contradicts the derived order law. Conversely,
original triangularity and the two order laws establish both outer and inner
conditions. This proves subgroup equality, from which the parabolic equivalence
is constructed by retaining each underlying matrix.

Finally, apply the inverse of `refinedLeviEquiv` to the projection comparison.
Each remaining entry is a nested diagonal submatrix entry. The published
`leviProjection_apply` formula and `hc` identify it with the original
diagonal entry. No decomposition, subgroup equality or projection comparison
is supplied as an assumption.

## Provenance and scope

This is a derived construction from the imported actual block, refinement and
preimage definitions. Its intended adjacent-block application is motivated by
Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), section 2.16(2) and Lemma 2.17, printed page 450. There the elementary
maps for `GL(n,F)` are described as transpositions of neighbouring blocks.
The general ring-valued coordinate bridge and its Lean implementation are
internal deductions, not a direct transcription of a theorem at that location.

The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`,
source ID `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The cited location is PDF page 11 (zero-based index 10). No source-specific
errata file was present in the public notes at preparation.

For a concrete adjacent merge, the shapes, label bijection, size equalities,
coordinate identity and swapped-shape comparison must still be constructed
and proved separately before applying this module. No normalized induction,
modulus comparison, representation equivalence, transitivity or classification
theorem is asserted here.
