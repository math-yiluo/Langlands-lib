# Actual pullback of supplied z-extensions

This internal construction implements the fiber product in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Lemma 11.4.3, printed
pp. 428–429 / PDF pp. 459–460, registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`. The original pages were read;
the authors' corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`) have no entry for Sections 11.4–11.5.

For actual supplied extensions `z` of `G` and `t` of `H`, and any
homomorphism `f : G ⟶ H`, `ZExtensionPullback.group z t f` is the actual
categorical pullback of `z.p ≫ f` and `t.p`. Its two projections satisfy
the required commuting equality.

`kernelGroup` is the binary product of the two supplied commutative kernel
groups. Its inclusion in the pullback is monic. `range_kernel` identifies
its full image with the scheme-theoretic kernel of the projection to `G`
on every test scheme, including nonreduced schemes. The proof factors the
two coordinates through the original kernels and uses the pullback
universal property. `quotient` proves that this projection is flat,
surjective and locally of finite presentation by base change and composition.

These results alone do not assert that the product kernel is induced, that
the pullback is connected reductive, or that its derived group is simply
connected. Those are separate structural steps in the proof of the
morphism-compatible domination statement.
