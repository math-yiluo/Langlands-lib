# A spanning representation with the same line stabilizer

`Langlands.GroupScheme.SpanningLineStabilizerStatement.{u}` is an internal
prerequisite for applying `FlagCoreDualLineStatement` to the representation
supplied by `Chevalley.exists_line_stabilizer`. Worker 1495 proposed this
interface; Worker 1489 formalized it. This file states the prerequisite and
does not prove it.

Let `k` be any algebraically closed field in universe `u`, let `G` be a smooth
affine group scheme over `k`, and let `ρ` be an actual representation on
`k^(n+1)` with distinguished coordinate vector `e_j`. The assertion produces
another actual representation `ρ'` on `k^(n'+1)` and a coordinate vector
`e_j'` with two properties:

1. On every relative scheme test `Z` and every point `x : Z ⟶ G.X`, the vector
   `ρ'(x)e_j'` is a unit multiple of `e_j'` if and only if `ρ(x)e_j` is a unit
   multiple of `e_j`. The units belong to the actual ring `Γ(Z.left, ⊤)`;
   neither nonzero scalars nor field-valued tests replace this condition.
2. The `k`-linear span of the vectors `ρ'(g)e_j'`, as `g` ranges over the
   actual rational sections of `G`, is the entire new coordinate space.
   `rationalMatrix` uses the published comparison
   `Γ(Spec k, ⊤) ≅ k`.

The two existential scalar witnesses in the equivalence are independent.
The assertion identifies the two stabilizer subfunctors and does not assert
an isomorphism of the whole representations. If a subgroup is the original
line stabilizer on all tests, the equivalence immediately makes it the new
line stabilizer on all tests as well. The statement does not assume `G`
connected or reductive and does not involve a torus or unipotent subgroup.

The provenance is an internal linear algebra reduction. The intended
construction takes the subspace spanned by `ρ(g)e_j` in the original
representation. The identity point puts the nonzero vector `e_j` in that
subspace. Multiplication of rational group points makes it stable under
`G(k)`. Smoothness gives reducedness, so rational-point detection over the
algebraically closed field can upgrade this to invariance under the actual
group-scheme representation. A basis containing `e_j` and a split coordinate
inclusion then give a representation through
`MatrixRepresentation.restrictCoordinates`. Its intertwining identity and
the split inclusion must prove the equivalence on arbitrary scheme tests,
and its coordinates must prove the spanning condition.

All of these construction and proof steps remain obligations of a proof of
the statement. No invariant affine cover or parent flag-step conclusion is
asserted here.
