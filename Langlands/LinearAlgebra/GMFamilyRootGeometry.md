# Root geometry for `(G, M)`-families

The tests in `GMFamilies` describe finite root arrangements in a Euclidean
space and their restrictions to Levi flats. `linearIndependent_simpleRoots`
proves independence for the published indecomposable-root definition. Positive
ambient roots are sums of indecomposables by finite induction on a positive
grading. Distinct ambient indecomposables have nonpositive mutual inner
product by crystallographic integrality and reflection. Splitting any
linear relation into its positive and negative parts proves independence.
An ambient chamber refining the point on the Levi flat gives an ambient
simple set. The ambient simple roots vanishing on the flat span its
orthogonal complement, and the other simple roots project to the restricted
indecomposables. A positive grading and induction on positive roots identify
those indecomposables. `span_simpleRoots_eq` shows that they span the
orthogonal complement of the common root kernel inside `a`.

`inter_leviRoots_parabolic` and `union_parabolic_of_local` identify the chambers
incident to a face with the local parabolics for its vanishing roots. A large
multiple of the face point plus a local regular point combines the specified
signs. `simpleRoots_inter_leviRoots` and `faceSpace_eq_orthogonal_simpleRoots`
identify the simple roots of the local chamber and the flat of the face.
These facts are intrinsic to the finite root model of `GMFamilies`.

`exists_inner_values` realizes prescribed inner products against a linearly independent family in a finite-dimensional real inner product space.
