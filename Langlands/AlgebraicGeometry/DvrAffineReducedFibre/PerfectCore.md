# The perfect core of a finitely generated field extension

Worker 594.

`perfectCore L p` is the intersection, taken in the subfield
lattice of `L`, of the images of every iterate of Frobenius.
In positive characteristic this consists of the elements that
have a `p^n`th root in `L` for every natural number `n`.

For a finitely generated field extension `L/k`, an element with
all those roots is algebraic over `k`. A transcendental element
would belong to a transcendence basis. Its `p^n`th root would
have minimal polynomial of degree `p^n` over the field generated
by that basis. The proof identifies the basis field with a
rational function field and uses Eisenstein at the prime
polynomial variable corresponding to that element. The degrees
cannot grow beyond the finite dimension of `L` over the basis
field. If `k` is algebraically closed, its elements have roots
of every positive degree and all algebraic elements of `L`
over `k` lie in its image. Thus the perfect core is exactly the
image of `k`.

The residue field at a prime of a finite-type algebra is the
fraction field of the quotient by the prime. When the map to
the local ring is local, this field is finitely generated over
the base residue field. Over an algebraically closed base
residue field, the perfect core computation verifies the
separable algebraicity hypothesis on the intersection of the
Frobenius images used in elimination of ramification.
[The Stacks Project, Theorem 15.117.18, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9).

This is a derived local prerequisite for the affine reduced
fibre theorem in Conrad's appendix to Prasad–Yu, *On
quasi-reductive group schemes*, author preprint, Theorem A.2
on printed and PDF p. 28. The registered source is
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
