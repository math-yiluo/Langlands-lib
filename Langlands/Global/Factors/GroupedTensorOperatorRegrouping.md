# Operators under tensor regrouping by block

The source is a tensor of two factors. The first is indexed by block. The second is indexed first by place and then by block. `groupedOperator` applies a specified linear operator in each of these slots. A linear regrouping map that sends pure tensors to the specified blockwise tensors intertwines this operator with the tensor of the resulting block operators.

`groupedPlaceOperator` applies a sum of block operators at one place of the nested tensor. If each one-place operator corresponds to a given operator on the matching block, the regrouping map sends the sum to the sum of those block operators. The proof expands the sum and checks on a pure tensor that the selected place and block are updated on both sides. The pure tensors of the inner slots span, so tensor extensionality proves the equality on the full source.

These are internal regrouping lemmas for Task 6553. Flath (1979), §2, pp. 180–181 (PDF 176–177), gives the tensor product and component map context. The Lean proof uses the Library's indexed tensor maps and one-slot operator algebra homomorphisms.
