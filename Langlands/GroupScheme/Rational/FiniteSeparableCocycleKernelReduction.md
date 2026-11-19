# Kernel reduction for cocycles on finite separable covers

`Cocycle.TrivialityReflectsFrom` asks that a cocycle on every finite separable
cover be trivial if it has a trivializing cochain on the actual pullback of
that cover to the extension field.

The kernel reduction implements the neutral-fibre step of Milne, *Algebraic
Groups* (2017), Theorem 25.71, printed page 565. Consider a smooth surjective
homomorphism with a kernel satisfying this reflection property. Suppose that
each translate of the image of the local group points contains the image of a
base quotient point. A cocycle whose quotient and local extensions are both
trivial then has a trivializing cochain over its original cover.

The proof uses the translate condition to give the two trivializing cochains
the same quotient image locally. The fibre of the smooth surjection over the
corrected quotient cochain is smooth and nonempty over the cover field. A
point over a finite separable extension of that field lifts the cochain.
Refine both cochains along the induced maps of covers and form the kernel
cocycle using the lifted cochain. Its local triviality follows from the
matching quotient images. The kernel reflection hypothesis gives a global
trivialization on the refined cover, and fpqc reflection descends the
resulting triviality to the original cover.
