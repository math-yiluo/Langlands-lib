# Inversion in the D4 Weyl group

On an integral D4 root datum whose simple coroots span the cocharacter
lattice, `negAut_mem_weylGroup_of_D4` places full character and cocharacter
negation in the Weyl group. The proof evaluates the four simple reflections
of Mathlib's numbering in the order given by the Coxeter word
`s₀ s₁ s₂ s₃`. The Cartan entries determine the image of every simple root.
Three applications send each simple root to its negative. Since the
simple coroots span, an automorphism fixing all simple root indices is the
identity. Thus the cube equals the full negation automorphism.

This is the inversion property of the longest D4 Weyl element used in
Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.8,
printed p. 374. The calculation uses the actual integral root datum and the
four supplied simple roots.
