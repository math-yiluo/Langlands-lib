# Evaluation of cuspidal Levi coefficients

`operatorRealizationFunctionEvaluation` evaluates an actual operator
realization in scalar-valued functions on the adelic general linear group.
It is injective because the realization embeds in the continuous functions.
Taking the tensor of these evaluations embeds the block tensor in functions
on the Levi.

If the evaluated tensor is the Levi restriction multiplied by the product
of block determinant characters, the tensor vanishes exactly when the
restriction vanishes. Each character takes values in complex units, so the
product is nowhere zero. On pure tensors, the finite Levi action translates
each corresponding adelic variable. The tensor product universal property
extends this equality to every tensor. When the input restriction is
translated, multiplicativity of the determinant characters gives the
inverse character factor in `cuspidalLeviCoefficient_finiteCovariance`.

This recovers the covariance of the coefficient tensors used in the
cuspidal Levi projection and induction in Langlands, *On the notion of an
automorphic representation*, Corvallis Part I (1979), p. 205 (PDF p. 200),
in the proof of Proposition 2 after Lemma 6. The character multipliers here
convert between the original coefficient functions and the unitary-character
ones used for the cuspidal decomposition.
