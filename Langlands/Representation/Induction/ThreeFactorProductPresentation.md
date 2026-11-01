# Actual three-factor product presentations

This internal unit proves that the binary normalized product of a supplied
quotient of \(A\times B\) with \(C\) is an actual quotient of the literal
three-block normalized induction of \(A,B,C\). All three ranks are positive
and may differ. Its total rank is `(a+b)+c`; its source shape is
`Shahidi.threeBlocksRight a b c ha hb hc`, with the original factor family
`threeBlockSmoothFamily A B C`. No transport between bracketings of addition
is needed in this interface. The topological data \(T\) is supplied, and
the input carriers lie in `max uF uV`.

`threeRightProductEquiv` is an actual equivariant linear equivalence from
that literal three-block product to \((A\times B)\times C\), using precisely
`twoBlockFactors` for the two products. It applies the existing ordered
induction-in-stages theorem and `rightRegroupingEquiv`. The intermediate
two-block products use `pairFamily`; explicit factor equivalences identify
these with the supplied `twoBlockFactors`, and the equivalences are
composed. These comparisons retain every supplied factor and its action.

`rightProductMap_surjective` applies the preceding actual right-product
short exactness theorem to the kernel inclusion of a supplied surjection.
Its exactness hypothesis is the ordinary equality of the range of the
kernel inclusion with that kernel. `rightProductMap_injective` separately
uses tensor injectivity and injectivity of the actual normalized induction
map. These two helper results allow arbitrary independent input carrier
universe `uV`.

For `binaryRightProduct_isQuotient_threeBlocksRight`, the supplied quotient
is an actual surjective smooth morphism \(A\times B\to Q\). Its induced
right-product map is surjective by the helper just described. Composing it
with `threeRightProductEquiv` gives an actual surjection
\[
 A\times B\times C\longrightarrow Q\times C.
\]
The existing positive-rank binary-product comparison identifies the target
with `T.binaryNormalizedProductFunctor (a+b) c` on `(Q,C)`. The conclusion
is `SmoothRep.IsQuotient`, retaining the actual surjective map; it therefore
also supplies an actual subquotient presentation.

The provenance is internal: the proof composes actual tensor and induction
exactness, ordered induction in stages, and the positive-rank binary
product comparison. It assumes no product irreducibility, constructs no
proper subrepresentation of a linked product, and proves no local Jacquet
transfer.
