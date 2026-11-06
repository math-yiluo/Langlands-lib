# The generic Lie element is not central

Author: Worker 1630.

This derived helper module proves that the generic Lie element of a group
scheme `G` over a field `k` has nonnilpotent adjoint differential, provided
the base change of `G` to an algebraic closure of `k` has a semisimple Lie
element whose Lie centralizer is not the whole Lie algebra. Here the generic
Lie element is the element over the function field of `𝔸^d` whose
coordinates are the coordinate functions. This is the "the generic element
is not central" step of the project's route to unirationality of the scheme
of maximal tori (SGA 3, Exposé XIV). The argument is the standard one: a
coefficient of the characteristic polynomial of a linear family of
endomorphisms is a polynomial in the coordinates. If it is nonzero as a
polynomial, it cannot vanish at algebraically independent coordinates. The
proof is written out here from Mathlib's `LinearMap.polyCharpoly` API and
affine-space API and the Library modules `NonnilpotentLocus`,
`AdjointDifferentialBaseChange`, `AdjointGenericConjugation` and
`RationalFunctionFieldAlgebra`. No external theorem is asserted.

## Linear algebra

Namespace `Langlands.LinearAlgebra`. Here `k` is a field, `V` a `k`-module,
`W` a finite-dimensional `k`-vector space, `φ : V →ₗ[k] End k W` a linear
family of endomorphisms, and `b` a basis of `V` indexed by a finite type `I`.

- `not_isNilpotent_endomorphismFamilyBaseChange_of_algebraicIndependent`:
  suppose that over some field extension `L` of `k` the scalar-extended
  family `endomorphismFamilyBaseChange φ L` has a nonnilpotent member. Let
  `K` be any field extension of `k` and `z ∈ K ⊗[k] V` a vector whose
  coordinates in the scalar-extended basis `Algebra.TensorProduct.basis K b`
  are algebraically independent over `k`. Then
  `endomorphismFamilyBaseChange φ K z` is not nilpotent.

  Proof: the Library lemma `exists_polyCharpoly_coeff_ne_zero_of_baseChange`
  gives an index `i < finrank k W` for which the `i`-th coefficient of
  `LinearMap.polyCharpoly φ b` is a nonzero multivariate polynomial. Suppose
  the member at `z` is nilpotent. Its characteristic polynomial is then
  `X ^ finrank`, so its `i`-th coefficient is `0`. Mathlib's
  `polyCharpoly_coeff_eval` and `polyCharpoly_baseChange` identify this
  coefficient with the evaluation of the `i`-th coefficient polynomial at
  the coordinates of `z`. Algebraic independence makes that polynomial zero,
  a contradiction.

## Coordinates of affine space

Namespace `Langlands.GroupScheme`.

- `appTop_inv_appTop_hom` and `appTop_hom_appTop_inv`: on global sections,
  the two composites of an isomorphism of schemes with its inverse are the
  identity.
- `algebraMap_rationalFunctionField_apply`: for the `k`-algebra structure
  `rationalFunctionFieldAlgebra` on the function field of
  `𝔸(m; Spec k)`, the image of a constant `a : k` is the germ at the generic
  point of the pullback of `a` along the structure morphism. Proof: the
  naturality of `Scheme.ΓSpecIso`, and the description of the canonical
  morphism `Spec 𝒪_{X,x} ⟶ X` on global sections by germs
  (`Lie.ΓSpecIso_hom_fromSpecStalk_appTop`, from `AdjointGenericConjugation`).
- `algebraicIndependent_rationalFunctionFieldCoordinate`: the coordinate
  functions `rationalFunctionFieldCoordinate k m` of `𝔸(m; Spec k)` are
  algebraically independent over `k` in its function field. Proof: the
  evaluation map `MvPolynomial m k → K(𝔸^m)` at the coordinate functions
  factors as the identification `MvPolynomial m k ≅ Γ(𝔸^m, ⊤)` coming from
  `AffineSpace.SpecIso`, followed by `germToFunctionField ⊤`. The factorization
  is checked on constants, by `algebraMap_rationalFunctionField_apply` and
  `AffineSpace.SpecIso_inv_over`, and on variables, by
  `AffineSpace.SpecIso_inv_appTop_coord`. The first map is an isomorphism.
  The second is injective because affine space is integral. So the
  evaluation map is injective.

## The adjoint family

Namespace `Langlands.GroupScheme.Lie`. Here `G` is a group scheme over
`Spec k` with affine, locally finite type structure morphism, and
`c : FiniteCoordinates G d`.

- `coordinateBasis c` (definition): the basis of the Lie kernel
  `Additive (lieKernel G k)` whose coordinate functionals are the
  coordinates of `c`, i.e. the standard basis of `Fin d → k` transported
  along `c`.
- `coordinateBasis_baseChange_repr`: for a field extension `K` of `k` and
  `z ∈ K ⊗[k] Additive (lieKernel G k)`, the coordinates of `z` in the
  scalar-extended coordinate basis are the `c`-coordinates of the
  scalar-extended Lie vector `kernelScalarExtension G K z`. Proof: induction
  on tensors, using the naturality of `c`.
- `not_isNilpotent_tangentMatrix_of_algebraicIndependent`: suppose that over
  some field extension `L` of `k` the scalar-extended adjoint differential
  family `adjointDifferentialFamily c` has a nonnilpotent member. Let `K` be
  a field extension of `k` and `X` a Lie vector of `G` over `K` whose
  `c`-coordinates are algebraically independent over `k`. Then the operator
  `Matrix.toLin' ((adjointRepresentation c).tangentMatrix K X)` is not
  nilpotent. Proof: apply the linear-algebra lemma to
  `z = (kernelScalarExtension G K).symm X`, whose coordinates are those of
  `X` by `coordinateBasis_baseChange_repr`. The Library identity
  `coordinateTensorEquiv_conj_adjointDifferentialFamily` conjugates the
  scalar-extended family at `z` to the tangent-matrix operator of `X`, and
  conjugation preserves nilpotence.
- `isAffineHom_baseChange_algebraicClosure` (instance): the base change of
  `G` along `algebraBaseMap k (AlgebraicClosure k)` has affine structure
  morphism. It is a pullback of `G.X.hom`.
- `exists_isSemisimpleElement_of_hasNoncentralGeometricSemisimpleElement`:
  restates the Library hypothesis `HasNoncentralGeometricSemisimpleElement G`
  (stated with `toAlgebraicClosure k`) as the existence of a semisimple Lie
  element with proper Lie centralizer in the base change along
  `algebraBaseMap k (AlgebraicClosure k)`. This is the form that the Library
  lemma `exists_nonnilpotent_adjointFamilyBaseChange` expects. The two base
  morphisms agree by definition.

## Main result

- `not_isNilpotent_tangentMatrix_genericLieElement`: assume
  `HasNoncentralGeometricSemisimpleElement G`. Let `K` be the function field
  of `𝔸(ULift (Fin d); Spec k)`. Then the adjoint differential of the
  generic Lie element `genericLieElement c` over `K`, the operator
  `Matrix.toLin' ((adjointRepresentation c).tangentMatrix K (genericLieElement c).toMul)`,
  is not nilpotent.

  Proof: `exists_nonnilpotent_adjointFamilyBaseChange`, applied at the
  algebraic closure of `k`, gives a nonnilpotent member of the
  scalar-extended adjoint family. The coordinates of the generic Lie element
  are the coordinate functions composed with `ULift.up`. They are
  algebraically independent by
  `algebraicIndependent_rationalFunctionFieldCoordinate`. Then apply
  `not_isNilpotent_tangentMatrix_of_algebraicIndependent`.

## Implementation notes

The final theorem is elaborated under
`set_option maxHeartbeats 2000000` and
`backward.isDefEq.respectTransparency true`. Instantiating
`exists_nonnilpotent_adjointFamilyBaseChange` at `AlgebraicClosure k`
exceeds the default heartbeat budget, apparently because Lean must unify the
ring structure `Field.toCommRing` with `AlgebraicClosure.instCommRing`. The
rest of the module uses
`backward.isDefEq.respectTransparency false`, as the neighbouring Library
modules do.
