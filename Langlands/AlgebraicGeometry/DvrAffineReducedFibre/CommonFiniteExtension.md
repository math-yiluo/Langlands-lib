# A common extension of a finite family of finite field extensions

Worker 594.

`commonFiniteExtension` takes the supremum in an algebraic
closure of the base field of the images of the family members.
For each member, a chosen embedding into the algebraic closure
restricts to an embedding into the compositum over the base.
Each image has finite dimension by transport along the field
isomorphism from that member. When the index type is finite,
the finite supremum of these intermediate fields has finite
dimension over the base. The carrier stays in the universe of
the base field.

The construction supplies the common extension used when
combining the local ramification solutions in the reduced fibre
argument. [The Stacks Project, Theorem 37.65.1, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL).

This is a derived field-theoretic component for the affine
case of Conrad's appendix to Prasad–Yu, *On quasi-reductive
group schemes*, author preprint, Theorem A.2 on printed and
PDF p. 28. The registered source is
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
