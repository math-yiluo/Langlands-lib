# Detecting a simple constituent on a finite-dimensional range

This internal algebraic lemma is for the proof of `CuspidalIsobaricSupportStatement`. It detects a simple subquotient
through a finite-dimensional compression of an algebra action. It is motivated
by the constituent comparison of normalized products in Badulescu–Renard (2010),
Definition 2.2, Remark 2.3 and Proposition 2.4, pp. 1123–1124 (PDF pp. 10–11).
The finite-dimensional compression criterion and its proof are derived here.

Fix an algebra element `p`. The compression of `a` on the range of `p` first
applies `a` and then applies `p`. Compare the determinant of one minus this
endomorphism for each `a`. Let `J` be a simple subquotient of the first module
with `p j₀ ≠ 0`. Evaluate each algebra element on a basis of the range of `p`
in the second module. If an element `a` vanishes on that basis but acts
nontrivially on `p j₀`, simplicity gives `c` with `c a p j₀ = j₀`. The compression
of `c a` then fixes `p j₀` in `J`. If the identity minus this operator were
invertible on the range of `p` in the first module, its restriction to the
intersection with the subspace defining the subquotient would also be invertible
by finite dimensionality. The restriction induces a surjective and hence
injective endomorphism of the image of that intersection in `J`. This contradicts
the nonzero fixed vector of the compression, which lies in that image. The
determinant therefore vanishes in the first module and equals one in the second.

Consequently evaluation on the basis factors the map `a ↦ a p j₀`. The image
of evaluation is an invariant subspace of a finite power of the second module
that surjects equivariantly onto `J`. Induction on the number of coordinates
extracts a subquotient of one copy. For the induction step, if the quotient map
kills the kernel of the tail projection, it descends to the image in the tail.
Otherwise its restriction to that kernel surjects by simplicity, and projection
to the first coordinate identifies the kernel with a subspace of one copy.
