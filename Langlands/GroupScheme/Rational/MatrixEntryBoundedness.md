# Matrix entries and algebraic boundedness for closed representations

This derived coordinate unit works over any field with a valuative relation,
in arbitrary universe. It uses actual affine group schemes and actual matrix
representations on any finite index type, including the empty type.

`MatrixRepresentation.HasBoundedRationalEntries ρ B` says that each entry of
`ρ.rationalMatrix` has a nonzero uniform valuative bound on `B`. The bound may
depend on the entry. No boundedness of characteristic-polynomial coefficients
is assumed or derived here.

The inverse-entry comparison first identifies the inverse rational matrix
entries with evaluation of the existing global inverse-coordinate sections.
For a closed representation, the pullback on global functions is surjective.
Composing it with the canonical global-section comparison for the explicit
general linear coordinate algebra and its polynomial quotient gives a
surjective polynomial presentation of the source coordinate algebra.
The variables are entries and inverse entries. Their evaluations are exactly
the corresponding entries of `ρ.rationalMatrix` and its inverse. The bounded
evaluation subalgebra and polynomial induction from `AffineBoundedTransport`
therefore give a bound for every regular function.

For any inverse-stable set of rational points, the representation's monoid
homomorphism law transfers entry bounds at `g⁻¹` to inverse-entry bounds at `g`.
The whole-group corollary consequently needs only entry bounds. Its conclusion
is the existing `IsAlgebraicallyBounded F G.X Set.univ`, with no substitute
matrix-space boundedness predicate.

This formalizes the coordinate transport in Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), Definition 2.2.1 and Lemma 2.2.7 (printed pp.70–71,
PDF pp.101–102; registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`). The method uses the project's
two-matrix polynomial presentation of GL. The spectral-to-entry bound required
by `ReductiveSpectralBoundednessStatement` remains a separate proof obligation.
