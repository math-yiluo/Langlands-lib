# Moving a cocycle to the kernel using a lifted cochain

Let `ξ` be a cocycle of `G` and let `q` be a group homomorphism from `G` to
`Q`. A cochain `g` whose image in `Q` trivializes the image cocycle gives
`Cocycle.kernelTwist ξ q g`, the lift of `ξ.twist g` to the actual kernel of
`q`. The quotient coboundary equation shows that the twist maps to the identity
on every test. Triviality of the kernel cocycle gives triviality of `ξ` by
inclusion and undoing the twist.

On a compatible cover over a changed base, suppose a cochain `f` trivializes
the base change of `ξ` and that the quotient image of `f` equals the pullback
of the image of `g`. Under the pullback point equivalences, their left ratio
lies in the original kernel on the test over the original base. Its lifted
point gives a cochain over the changed base. The twist identity and naturality
of the pullback point equivalence give the required coboundary equation for
the base change of `Cocycle.kernelTwist ξ q g`.

This is an internal fixed-cover form of the kernel step of the nonabelian
cohomology sequence used in Milne, *Algebraic Groups* (2017), Theorem 25.71,
printed p. 565 (`milne-2017-algebraic-groups`).
