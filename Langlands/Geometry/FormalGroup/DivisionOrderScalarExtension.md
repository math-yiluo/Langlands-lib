# Scalar extension of the local division order

`integerTensorEquiv` identifies the scalar extension of the actual valuation
integer ring `IntegerRing K D` with the original local division algebra `D`.
It is the `K`-algebra equivalence that sends a pure tensor `k ⊗ a` to `k • a`
in `D`. Its inverse sends an integral element `a` to `1 ⊗ a`.

The underlying map is the scalar extension of the integral inclusion. It is
injective because the fraction field is flat and extending the scalars of a
`K`-module from `𝒪[K]` to `K` recovers that module. Its range is the `K`-span
of the integer order, which is the whole division algebra by
`localDivisionIntegerLattice_span`.

This internal construction lets the existing integral order actions act by
rational formal endomorphisms. It supplies the scalar extension needed for
the division-algebra units in Drinfel'd, *Coverings of p-adic symmetric
regions* (1976), §2 A, printed p. 109. The equivalence applies to the canonical
valuation integer ring of any finite-dimensional central division algebra
over a nonarchimedean local field.
