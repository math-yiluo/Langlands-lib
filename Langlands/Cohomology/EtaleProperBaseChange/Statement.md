# Proper base change for bounded torsion étale coefficients

Michael Artin, SGA 4, Tome 3, Exposé XII, defines the base-change
morphism in §4, printed pp. 84–85 (PDF pp. 87–88). Theorem 5.1(iii),
printed pp. 87–88 (PDF pp. 90–91), gives invertibility of the morphism
in every degree for a proper map and torsion abelian sheaves. Corollaire
5.2(iii), printed p. 89 (PDF p. 92), gives the geometric-fibre version.
Registered source ID `sga4-1973-tome3-deligne-xvii-original-scan`,
SHA-256 `702fa23766ccec841d31ce0f21dfaacff8d8d31d4153de386587a27a4c01107a`.
See also J. S. Milne, *Étale Cohomology* (1980), VI.2, Corollaries
2.3 and 2.5, printed pp. 223–224 (PDF pp. 237–238), registered ID
`milne-1980-etale-cohomology`, SHA-256
`0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232`.

## The map and proposition

The commuting square has vertical arrows \(f:Y\to S\) and \(f':Z\to T\),
and horizontal arrows \(g:T\to S\) and \(g':Z\to Y\). The map
`Langlands.Cohomology.etaleDerivedBaseChangeMap` is

\[
  g^* Rf_* F \longrightarrow Rf'_* g'^* F
\]

in bounded-below derived categories on the actual small étale sites.
It is the mate under \(g^*\dashv Rg_*\) of the image under \(Rf_*\) of
the unit \(F\to Rg'_*g'^*F\), followed by the identification of composite
direct images \(Rf_*Rg'_*\cong Rg_*Rf'_*\). This uses the first
construction in SGA 4 XII §4. The identification comes from the
comparison \(f'^*g^*\cong g'^*f^*\) of the exact derived inverse images
by uniqueness of right adjoints. The four derived-category universes
are independent.

`Langlands.Cohomology.EtaleProperBaseChangeStatement` assumes that the
square is Cartesian and \(f\) is proper. It takes a sheaf \(F\) of modules
over a commutative coefficient ring \(R\), with multiplication by some
positive integer equal to zero. It asserts that the map evaluated at
\(F\) in degree zero is an isomorphism. Exactness of inverse image
identifies each nonnegative cohomology map with the degreewise morphism
of Theorem 5.1(iii). The derived complexes of the two
degree-zero coefficient sheaves have zero negative cohomology.
This yields the derived formulation using the degreewise theorem.
After forgetting \(R\), higher direct image can be computed from the
same flasque resolution as for abelian sheaves. In particular, the
bounded torsion condition includes the \(\ell\)-power torsion
coefficient stages of the Harris tower without any condition on the
residue characteristic at this step.

The geometric-fibre specialization is used to compare relative
cohomology of abelian schemes with the cohomology of the geometric
abelian fibres. The arithmetic good-reduction application also uses
the smooth proper specialization statement for the specified
finite locally constant coefficients.
