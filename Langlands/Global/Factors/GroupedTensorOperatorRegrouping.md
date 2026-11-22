# Operators under tensor regrouping by block

The source is a tensor of two factors. The first is indexed by block. The second is indexed first by place and then by block. `groupedOperator` applies a specified linear operator in each of these slots. For a finite place index, suppose a linear regrouping map sends fully pure tensors to the tensors of the specified blockwise maps. If each blockwise map carries the source operators in that block to its target operator on pure tensors, the regrouping map intertwines `groupedOperator` with the tensor of the target operators.

`groupedPlaceOperator` applies a sum over the finite block index at one place of the nested tensor. With a finite place index and the same pure-tensor formula for regrouping, the comparison assumes that applying the selected place operator before a blockwise map agrees with applying the corresponding target operator after that map. The proof expands the sum and checks that each term updates the selected place and block. In both comparisons, finiteness of the place index allows the spanning property in the inner slots to give equality on the full source.

These are internal regrouping lemmas for Task 6553. Flath (1979), §2, pp. 180–181 (PDF 176–177), gives the tensor product and component map context. The Lean proof uses the Library's indexed tensor maps and one-slot operator algebra homomorphisms.
