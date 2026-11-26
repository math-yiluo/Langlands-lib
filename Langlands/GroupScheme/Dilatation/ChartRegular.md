# Regularity of the denominator in a dilatation chart

`regular_quotient_ofList_of_regular_mod` works in a commutative ring \(A\). If multiplication by \(t\) is injective on \(A\) and the images of \(x_1,\ldots,x_n\) form a weakly regular sequence in \(A/(t)\), multiplication by \(t\) is injective on \(A/(x_1,\ldots,x_n)\).

For one equation, a congruence \(ta=tb\bmod x_1\) gives \(t(a-b)=x_1c\). Regularity of \(x_1\) modulo \(t\) gives \(c=td\). Cancelling \(t\) yields \(a-b=x_1d\). The induction removes one equation at a time. The canonical equivalence between the two orders of quotienting by \(t\) and by that equation carries the remaining sequence to its image in the new ring.

This is the cancellation step used for the affine blow-up chart in Appendix A.5.9–10 of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*, Cambridge University Press, 2023, printed p. 635. The Lean statement expresses it for an arbitrary list of equations.
