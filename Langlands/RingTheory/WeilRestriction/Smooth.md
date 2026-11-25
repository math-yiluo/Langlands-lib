# Smoothness under finite projective Weil restriction

Suppose `B` is finite projective over `A` and `C` is finitely presented over `B`. Formal smoothness of `C` over `B` gives formal smoothness of `WeilRestriction A B C` over `A`. Its finite presentation then gives the corresponding smoothness instance when `C` is smooth.

To lift a point through a square-zero quotient of a test algebra, the proof first classifies it as a `B`-algebra map from `C`. Tensoring the quotient with `B` gives a surjection whose kernel is the extension of the square-zero ideal, so its square is zero as well. Formal smoothness lifts the classified point, and the representing equivalence transports that lift back. [Representing algebra](PresentedAlgebra.md) and [tensor quotient kernel](../TensorProduct/QuotientKernel.md)
