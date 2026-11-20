# Mixed angular derivative bounds for monomial pullbacks

`smoothTorusMonomialPullback` composes a smooth scalar function with the
integer monomial map between the two finite tori. For an ordered output list
of derivative directions, the proof bounds the corresponding output seminorm
by the finite supremum of source seminorms up to the same order. The bound
has a factor given by the product, over those output directions, of the
column sums of absolute values of the monomial matrix.

The proof removes the last direction of the ordered list. The angular chain
rule expresses that derivative as a linear combination of source angular
derivatives with the entries of the corresponding column. Linearity and the
triangle inequality give the extra column-sum factor. The proof never needs
an identity that permutes angular derivatives. This derived estimate is used
for the change of unramified characters by Weyl conjugation in the weak
constant-term argument for Waldspurger VI.3.1.
