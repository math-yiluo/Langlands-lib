# Regrouped cuspidal block tensors and their local Lie operators

`groupedBlockTensorEquiv` takes the tensor of the finite coefficients and the nested infinite coefficients to the tensor of the actual cuspidal block realizations. It is the grouped scalar coefficient equivalence followed by the inverse of scalar coefficient evaluation. On a pure tensor this makes each output block from its finite coefficient and its own infinite place factors.

`groupedBlockTensorEquiv_placeLie` compares a sum of Lie operators in one place of the source with the sum of the corresponding operators on the individual realized blocks. Each presentation equivalence supplies the comparison for one selected block and place. The tensor regrouping rule sums these block comparisons and extends them to arbitrary coefficients.

This is internal to the normalized scalar induction for Task 6553. Flath (1979), §2, pp. 180–181 (PDF 176–177), gives the componentwise tensor map context. Getz and Hahn (2024), §10.1, pp. 270–271 (PDF 282–283), give the scalar inducing model. The proof uses the actual coefficient and spectral presentation equivalences.
