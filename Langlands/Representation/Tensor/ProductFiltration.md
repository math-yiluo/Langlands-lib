# Filtrations of binary and finite external tensor products

Module `Langlands.Representation.Tensor.ProductFiltration`,
namespace `Langlands.FiniteTensorFiltration`.

This module is separate from the published `Tensor/FiniteFiltration` module,
which filters an indexed tensor product through a single slot. Here every factor
has its own filtration, and all of them are combined.

## Purpose and provenance

This is an internal helper for the product-Levi cuspidal Jacquet multiplicity
theorem (`Langlands.ProductLeviCuspidalJacquetMultiplicityStatement`). The
intended proof works one coarse block at a time. Each factor
`GL(B.size i)` of the product Levi gets its own supplied filtration, and these
filtrations must then be combined into one filtration of the external tensor
product `FiniteTensor.external`. The graded pieces of the combined filtration are
the external tensor products of the factor graded pieces, and each choice of one
graded piece per factor occurs exactly once.

The underlying fact is standard linear algebra over a field: tensoring is exact.
The construction is not the total-degree filtration `∑_{a+b=c} F_a ⊗ G_b`,
whose graded quotients are direct sums of the products of the same total degree.
Instead, `A ⊗ B` is first filtered by the steps `F_a ⊗ B`, with graded quotients
`gr_a F ⊗ B`. Each of these quotients is then refined by the filtration
`gr_a F ⊗ G_b` coming from `B`. The resulting filtration has one step for each
pair `(a, b)`, and that step's graded quotient is `gr_a F ⊗ gr_b G`. No
statement of the literature is formalized here; the content is internal. The
proof uses only
published Library results: the binary image filtrations of
`Langlands.Representation.Tensor.Filtration`, the interval lift of
`Filtration/IntervalLiftProof`, the concatenation of relation series of
`Filtration/GradedRefinementProof`, and the head/tail splitting of finite
external tensor products of `Tensor/FiniteEquivalences`.

All filtrations are actual `ObjectRepFiltration`s. All comparisons are actual
`Representation.Equiv`s, or `Nonempty` of them in the existence theorems. The
coefficient ring is a field `k` wherever filtrations occur. No simplicity of any
graded piece is assumed or produced.

## Declarations

### Equivalence bookkeeping (section `Equivalences`, `External`)

* `tprodCongr e f : (tprod ρ σ).Equiv (tprod ρ' σ')` is the tensor product
  `TensorProduct.congr` of two actual equivalences `e : ρ.Equiv ρ'` and
  `f : σ.Equiv σ'`.
* `compCongr e φ : Representation.Equiv (ρ.comp φ) (σ.comp φ)` pulls an
  equivalence back along a monoid homomorphism `φ : H →* G`. The underlying
  linear equivalence is the same.
* `compSymmComp ρ φ` is the identity-on-vectors equivalence
  `((ρ.comp φ) .comp φ.symm) ≃ ρ` for a monoid equivalence `φ : H ≃* G`.
* `gradedCongr s h` identifies the graded pieces `i` and `j` of a filtration `s`
  when `h : i = j`.
* `externalCongr e : (FiniteTensor.external ρ).Equiv (FiniteTensor.external σ)`
  is `PiTensorProduct.congr` of a family `e i : (ρ i).Equiv (σ i)` of actual
  equivalences of representations of the factor groups `H i`, for any index
  type.

### Refinement by filtrations of the graded pieces (section `Splice`)

`exists_splice f m t`: let `f` be an `n`-step filtration of `A`, and for each `i`
let `t i` be an `m i`-step filtration of the graded piece
`f.gradedRepresentation i`. Then there is a filtration `s` of `A` of some length
`N` and an equivalence `E : Fin N ≃ Σ i, Fin (m i)` such that the `j`-th graded
piece of `s` is equivalent to the `(E j).2`-th graded piece of `t (E j).1`.

Proof: pull each step of `t i` back to `A` with `IntervalLiftProof.pull` (between
steps `i` and `i+1` of `f`). This gives a relation series for `≤` from step `i` to
step `i+1` (`pull_bot`, `pull_top`, `pull_mono`). Concatenate these series with
`GradedRefinementProof.concatenate`, which also gives the index equivalence and
says which pulled-back steps bound each new step. Then compare quotients with
`nonempty_quotient_pull_equiv`.

### Binary tensor products (section `Binary`)

`exists_tprod s t`: let `s` be an `n`-step filtration of `A` and `t` an `m`-step
filtration of `B`, both representations of the same monoid `G` over a field
`k`. Then there is a filtration `f` of `Rep.of (tprod A.ρ B.ρ)` and an equivalence
`E : Fin N ≃ Fin n × Fin m` such that the `j`-th graded piece of `f` is
equivalent to `tprod (s.gradedRepresentation (E j).1).ρ (t.gradedRepresentation (E j).2).ρ`.

Proof: start from the right tensor filtration `s.tensorRight B` with graded pieces
`gr_a s ⊗ B` (`tensorRightGradedEquiv`). Refine each of these by the left tensor
filtration `t.tensorLeft (gr_a s)`, transported to the graded piece along
`tensorRightGradedEquiv` with `LengthTwo.transport`. Its graded pieces are
`gr_a s ⊗ gr_b t` (`equivTransportGradedEquiv`, `tensorLeftGradedEquiv`). Then
apply `exists_splice` and reindex `Σ a, Fin m` as `Fin n × Fin m`.

### Finite external tensor products (section `Finite`)

`exists_external K A r s`: let `A i` be a representation of the group `H i` in a
universe `uV`, and `s i` an `r i`-step filtration of `A i`, for `i : Fin K`. Then
there is a filtration `f` of `Rep.of (FiniteTensor.external fun i => (A i).ρ)` (a
representation of `∀ i, H i`) of some length `N` and an equivalence
`E : Fin N ≃ ∀ i, Fin (r i)` such that, for every `j`, the `j`-th graded piece of
`f` is equivalent to
`FiniteTensor.external fun i => ((s i).gradedRepresentation (E j i)).ρ`.
Each tuple of factor indices labels exactly one graded piece.

Proof by recursion on `K`:

* `K = 0`: take the one-step filtration `LengthTwo.oneStep`. Its only graded piece
  is the whole representation (`IrreducibleMultiplicityProof.oneStepGradedEquiv`).
  The two empty external products are identified by `externalCongr` of the
  vacuous family. `E` is `Equiv.ofUnique`.
* `K + 1`: apply the recursion to the tail factors `j.succ`, giving `f'` and `E'`.
  Pull `s 0` back along `MonoidHom.fst` and `f'` along `MonoidHom.snd`
  (`ObjectRepFiltration.comp`, with graded pieces from `compGradedEquiv`). Apply
  `exists_tprod` to these two filtrations of representations of
  `H 0 × ∀ j, H j.succ`. Move the result to `(external ρ).comp (headTail H).symm`
  along `(FiniteTensor.headTailEquiv ρ).symm`. Pull it back along
  `headTail H` and transport it along `compSymmComp` to a filtration of
  `external ρ`. The index equivalence is the binary one followed by
  `E'` on the tail and `Fin.consEquiv`. The graded-piece equivalence composes the
  same steps on graded pieces, ending with `FiniteTensor.headTailEquiv` for the
  family of graded pieces. `gradedCongr` and `externalCongr` match the indices
  `Fin.cons a (E' b)` on the head and tail coordinates.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
