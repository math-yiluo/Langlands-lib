# Regular rational points of maximal tori in the general linear group

`Langlands.GroupScheme.generalLinearMaximalTorusRegularPoint` proves the
regular point and scheme centralizer statement. [Statement](GeneralLinearMaximalTorusRegularPointStatement.md)

The matrix of the torus embedding over the torus's global sections gives
a characteristic polynomial \(p\) and a basic open defined by the
resultant of \(p\) and \(p'\). The Sylvester matrix uses degree bounds
\(n\) and \(\max(n-1,0)\), so the resultant commutes with every coefficient map.
At a field-valued point, monicity allows the derivative bound to be
reduced to its actual degree without changing the resultant. This makes
membership in the open equivalent to separability, even when the
derivative drops in degree.

Over a finite Galois splitting field, maximal split torus conjugacy
identifies the given torus with the diagonal torus. A diagonal matrix
with distinct nonzero entries has separable characteristic polynomial.
Its corresponding point shows that the basic open is nonempty. Zariski
density of the torus's rational points then gives a point in this open
over the ground field.

The same conjugation carries the chosen point to a diagonal matrix
\(\operatorname{diag}(d_i)\) with separable characteristic polynomial.
For \(i\ne j\), the difference \(d_j-d_i\) is a unit and stays a unit in
the global sections of every test scheme. The commutation equation for
a matrix \(M\) gives \(M_{ij}(d_j-d_i)=0\), so \(M\) is diagonal.
Transport along the conjugation and faithfully flat descent give
containment in the range of the original torus embedding. The reverse
containment follows from the commutativity of the torus. The closed
embedding is a monomorphism, so it represents the full centralizer.

This is a matrix refinement of the self-centralizer property for
maximal tori recalled in David Renard, *Représentations des groupes
réductifs \(p\)-adiques*, 9 July 2026, § V.2.1, printed p. 104
(PDF p. 110). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
