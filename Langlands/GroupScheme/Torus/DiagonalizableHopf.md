# Diagonalizable groups and standard Hopf spectra

This internal comparison applies to every commutative ring `R` and every
additive commutative group `Λ`, in arbitrary universe `u`.

`hopfAlgebra R Λ` is the standard Hopf algebra on `AddMonoidAlgebra R Λ`.
The existing `Diagonalizable.groupScheme R Λ` instead obtains its group
structure by corepresenting the character functor `B ↦ Hom(Λ, Bˣ)`.
`hopfCogroupIso` compares these cogroup structures by the identity algebra map.
Applying the relative spectrum functor on group objects gives
`hopfSpecIso`, an isomorphism from the standard Hopf spectrum to the existing
actual diagonalizable group scheme over `Spec R`.

The implementation checks the counit and comultiplication on the generators
`single γ 1` using `AddMonoidAlgebra.algHom_ext`. The counit evaluates each
monomial to one and therefore agrees with the character functor's identity
point. The comultiplication sends a monomial to its tensor square, as proved
for the corepresentation in `Diagonalizable.comul_single`. These equalities
supply the unit and multiplication conditions for `Grp.mkIso`; preservation
of inversion follows from the group-object construction.

The provenance is internal: this identifies two existing structures on the
same group algebra using the Library's `Diagonalizable` and `Corepresented`
constructions and Mathlib's standard additive group-algebra Hopf structure
and Hopf-algebra/cogroup equivalence. No classification theorem is assumed.
This comparison does not establish a finite integer lattice, torus splitting,
field descent, or the unrestricted dynamic-centralizer reductivity theorem.
