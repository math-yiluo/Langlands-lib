# Affine vector orbit maps with prescribed unipotent stabilizers

These internal consequences combine the actual Chevalley line-stabilizer
construction, the triviality of the character on a preserved line for a
unipotent group, and the actual affine vector action and orbit construction.
They use every relative scheme test, over any field and at every universe.

`Chevalley.exists_vector_stabilizer` applies `exists_line_stabilizer` to a closed
unipotent subgroup \(H\to G\), where \(G\) is affine and locally of finite type.
The representation restricted to \(H\) preserves the selected coordinate line.
The unipotent line-character result shows that \(H\) fixes the coordinate
vector. Conversely, fixing that vector preserves the line with scalar one.
Thus the range of \(H\) is exactly its vector stabilizer on every scheme test.
Neither smoothness of \(G\) nor smoothness of \(H\) is assumed here.

`Chevalley.exists_affine_vector_orbit` uses the same representation and
coordinate vector to construct an actual morphism into a finite vector group.
The images of \(g\) and \(h\) agree exactly when \(g^{-1}h\) lies in the subgroup's
range. This follows directly from `VectorOrbit.orbitMap_fibers` and the exact
vector-stabilizer equivalence.

`AffineVectorOrbit` bundles the finite representation, the chosen coordinate
vector, and these exact coset fibers. `affineVectorOrbit` chooses such data for
any closed unipotent subgroup under the same hypotheses.

`Chevalley.exists_closed_affine_vector_orbit` is conditional on the exact
published proposition `UnipotentAffineOrbitClosedStatement`, which this module
does not prove. Over an algebraically closed field, for smooth affine
unipotent \(G\), that input applies to the categorical vector action at the
chosen coordinate section. The affine target is the spectrum of a polynomial
algebra in finitely many variables, so its structure morphism is locally of
finite type. The resulting actual orbit map has closed underlying image and
retains the same all-test coset fibers.

All results are derived from the imported constructions. They do not assert
representability or affineness of a quotient; even the last theorem retains
Kostant–Rosenlicht as an explicit input.
