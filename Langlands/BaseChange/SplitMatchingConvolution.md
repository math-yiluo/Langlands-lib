# The split tensor integral at a fixed product

`splitProductFiberChart` completes \((w_0,\ldots,w_{l-1})\) by the last
entry \((w_0\cdots w_{l-1})^{-1}g\). The inverse records the full ordered
product and the first \(l\) entries. The two maps are continuous, giving a
homeomorphism between \(G\times G^l\) and \(G^{l+1}\).

The coordinate tensor is continuous and its support lies in the product
of the supports of its factors. The homeomorphism and pullback along a closed
embedding preserve compact support. This proves integrability both at fixed
\(g\) and on the orbit of a regular semisimple element with the free coordinates.

`integral_splitProductFiber` changes variables from the free tuple to its head
and tail using `splitFinHead_measurePreserving`. Fubini integrates the tail
at ordered product \(w_0^{-1}g\). The induction hypothesis turns that inner
integral into the tail convolution, and the outer integral is the Library
convolution formula. For \(l=0\) the empty product measure is a Dirac measure
on the unique empty tuple.

This is the convolution calculation of Arthur–Clozel (1989), Chapter 1, §5,
(5.2), in the free coordinates from `SplitMatchingChart`. The analytic
lemmas are internal steps for that calculation.
