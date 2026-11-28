# Adjoint discriminants of matching regular elements

`divisionWeylDiscriminant` is the coefficient of \(X^d\) in the characteristic
polynomial of \(\operatorname{Ad}(g')-1\) on the central division algebra \(D\),
where \(d\) is the reduced degree of \(D\) and \(g'\) is a unit of \(D\).
`Corresponds.weylDiscriminant_eq` identifies it with the ordinary discriminant
`Langlands.BaseChange.weylDiscriminant` at a matching regular elliptic unit of
\(\mathrm{GL}_n(F)\). Then \(n=d\). In the local setting this also identifies
the residue-normalized absolute values used in Weyl integration.

The proof extends both adjoint defects to a finite Galois splitting field of
\(D\). Each defect becomes the conjugation defect of the image unit under the
respective matrix chart. The definition of the reduced characteristic
polynomial gives the same characteristic polynomial for both image matrices.
Its separability makes it squarefree, so the matrices are conjugate over the
splitting field. The resulting linear equivalence intertwines the adjoint
defects. Their characteristic polynomials agree after scalar extension and
therefore over the base field by injectivity. Taking the coefficient at the
common degree gives the comparison of discriminants.

This algebraic comparison implements the discriminant identity in the Weyl
pairing of Badulescu, *Correspondance de Jacquet–Langlands pour les corps
locaux de caractéristique non nulle* (2002), §6, printed pp. 745–746
(`badulescu-2002-jl-char-p`). It uses the coefficient convention of the
ordinary discriminant in `Langlands.BaseChange.WeylIntegrationData`.
