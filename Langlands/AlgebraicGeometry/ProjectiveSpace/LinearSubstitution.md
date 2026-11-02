# Linear substitution on the actual projective coordinate ring

For every commutative ring `R : Type u` and natural number `n`,
`linearSubstitution R n f` is the `R`-algebra endomorphism of the actual
polynomial coordinate ring `ProjectiveCoordinateRing R n` obtained by
pulling polynomials back along the linear map
`f : (Fin (n+1) → R) →ₗ[R] (Fin (n+1) → R)`. It sends `X_i` to the actual
degree-one polynomial corresponding to `(LinearMap.proj i).comp f`, and
fixes every constant polynomial. No field or nontrivial-ring hypothesis
is needed.

`linearSubstitution_linearForm` proves that substitution sends the
polynomial of a linear functional `ℓ` to the polynomial of `ℓ.comp f`.
The proof expands `ℓ` in the standard coordinate dual basis, uses
linearity of the published `linearFormPolynomialEquiv`, and evaluates the
finite coordinate-basis reconstruction formula at `f v`. Polynomial
extensionality on the coordinate variables then proves that the identity
linear map induces the identity algebra homomorphism and that pullback
reverses composition:

`(linearSubstitution R n f).comp (linearSubstitution R n g)` equals
`linearSubstitution R n (g.comp f)`.

`gradedLinearSubstitution` packages the same map as a graded ring
homomorphism for the actual total-degree grading
`projectiveSpaceGrading R n`. The homogeneous-substitution theorem for
multivariable polynomials, with degree-one inputs, proves preservation of
every homogeneous piece. Its application, identity and reversed
composition formulas are proved from the algebra-homomorphism formulas.

For a linear equivalence `e`, substitution by `e` and substitution by
`e.symm` are inverse maps on every polynomial. The composition formula
and the two linear-equivalence inverse identities prove these equalities.
`linearSubstitutionEquiv` packages them as an actual polynomial
`R`-algebra equivalence.

`irrelevant_le_map_gradedLinearSubstitution` proves the irrelevant-ideal
condition required by Mathlib's `Proj.map` for substitution by a linear
equivalence. It suffices to check elements homogeneous of positive
degree. Substitute by the inverse linear equivalence; the resulting
element is still homogeneous of that positive degree and hence lies in
the irrelevant ideal. Its image under forward substitution is the
original element, so the original element lies in the image ideal.

This is internal algebraic support derived from the published
functional-to-degree-one-polynomial equivalence and Mathlib's polynomial,
grading and homogeneous-ideal APIs. This module does not construct a
scheme automorphism, compare an action on rational points, prove a torsion
bound, or prove the host representability statement. Those geometric
steps use the algebra constructed here in separate modules.
