# Contraction of the free sheaf Čech nerve of a split presheaf arrow

This is an internal specialization of Mathlib's split
Čech nerve extra degeneracy and its alternating-complex homotopy equivalence
to the free sheaf constructions in `FreeNerve`.

Let J be a Grothendieck topology on a category C and R a commutative ring,
with `HasSheafify J (ModuleCat R)`. For an arrow f of Type-w-valued
presheaves, a `SplitEpi f.hom` is explicit data of a natural section of f
with its section identity. No local-surjectivity hypothesis or products
in C are required.

`freeCechExtraDegeneracy` applies `freeSheafFunctor J R` to the extra
degeneracy of the presheaf Čech nerve determined by the given section.
Mathlib constructs that degeneracy by inserting the chosen lift of the
common image into the first coordinate of a tuple. An extra degeneracy
is preserved by every functor; the free sheaf functor need not preserve
the limits that formed the nerve.

`freeCechHomotopyEquiv` is the resulting homotopy equivalence between
`freeCechChainComplex J R f` and the complex concentrated in degree zero
at the free sheaf on the target of f. It uses Mathlib's alternating-face
complex homotopy equivalence for an extra degeneracy in a preadditive
category with a zero object. Its forward chain map is the actual
`freeCechAugmentation J R f`; the simp theorem verifies this by
reflexivity. The final theorem applies the fact that a homotopy
equivalence induces isomorphisms on all homology objects, obtaining a
quasi-isomorphism for that same augmentation.

This construction treats globally split presheaf arrows. It does not
prove exactness for arbitrary locally surjective arrows, a Čech-to-derived
comparison, or acyclicity of restricted equivariant injectives. Those
are separate obligations.
