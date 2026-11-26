# Determinants of cyclic matrix norms over fields

Arthur–Clozel, Chapter 1, Lemma 1.4 (printed p. 8), and
Henniart–Lemaire, I.6.12 (printed p. 53), take determinants of matrix
norms to get scalar norms. This module implements that implication for
the Library's cyclic norm over a field and derives its order formula
in the unramified \(p\)-adic case.

The fixed-field clause of `IsCyclicAlgebra` identifies the field fixed
by all automorphisms with the base field, so the extension is Galois.
The powers of the generator with exponents below \(l\) are distinct
and account for every automorphism by the degree formula. Determinants
commute with the entrywise automorphisms and turn the ordered matrix
product into the product of the corresponding scalar conjugates.
The latter product is the field norm after extension of scalars.
An association identifies that scalar norm with the determinant of
the base matrix because conjugation preserves determinants and the
embedding of fields is injective.

In the unramified case, the published norm-order formula multiplies
the order by the extension degree. Thus `IsNormAssociated.ord_determinant_eq`
compares the normalized orders for every associated pair in every rank.

`IsCyclicAlgebra.isAbelianGalois` gives the abelian Galois structure of a field extension with a cyclic-algebra generator.
