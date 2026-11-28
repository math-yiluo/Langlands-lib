# Products on the central quotient

If two complex functions `f` and `b` on a group transform by the same unitary
scalar under each central left translation, their product `f * conj b` is
invariant under the centre. `centralCovariantProduct` descends that product to
the quotient. The descent writes two representatives as central translates and
cancels the two scalar factors using their common absolute value of one.

If both functions are continuous on an open subset invariant under the centre
and `f` vanishes on its complement, the descended product is Borel. Continuity
on the image of the open set follows from the quotient topology. The product
vanishes elsewhere.

For a finite measure on the quotient, integrability of the diagonal product
and a uniform bound `M` on the absolute value of `b` imply integrability of
the Borel mixed product. The bound uses `|f| ≤ 1 + |f|²`, so the descended
absolute value is at most `M` times one plus the absolute value of the
diagonal product.

The construction expresses the pairing at fixed central character used in the
compact-modulo-centre step of Deligne–Kazhdan–Vignéras, *Représentations des
algèbres centrales simples p-adiques*, §B.1.g, printed pp. 81–82.
