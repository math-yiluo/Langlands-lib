# Arithmetic Frobenius on finite unramified stages

Let \(F\) be a nonarchimedean local field and \(E\) a finite
Galois arithmetic-unramified intermediate field of its separable
closure. The residue action of \(\operatorname{Gal}(E/F)\) is
surjective. Both Galois groups have the same cardinality because
the residue degree equals the field degree. This gives the
isomorphism `finiteUnramifiedResidueEquiv`.

`finiteUnramifiedFrobenius` is the lift of the arithmetic residue
automorphism \(x\mapsto x^{|\kappa_F|}\). It generates the group
because its image generates the finite residue Galois group.
`finiteUnramifiedCyclicCoordinate` gives the actual multiplicative
coordinate in \(\mathbb Z/[E:F]\mathbb Z\) sending this Frobenius
to the class of \(1\), including in degree one.

For nested finite unramified stages, lift the larger Frobenius
to the separable closure. Both residue embeddings into the closure
commute with restriction of this lift. The larger stage sends an
embedded lower residue to its \(|\kappa_F|\)-th power. Faithfulness
of the lower residue action now identifies the restriction with
the lower arithmetic Frobenius.

These are the finite-stage forms of the distinguished generator
used in Serre, *Local Fields* (1979), Chapter XIII, §§2–3,
printed pp. 190–194. The proof uses the actual finite residue
Galois groups and the Library's spectral unramified criterion.
