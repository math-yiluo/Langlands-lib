# Weak association of contragredients, presented form

This module proves the presented form
`Langlands.ClassField.Global.RelativeWeilGroup.PresentedContragredientAssociationStatement.{u, uV, uP, uQ}`
of [AssociatedContragredientStatement](../AssociatedContragredientStatement.md).
The statement concerns a finite-dimensional complex representation `S` of the
class-indexed extension `RelativeWeilGroup c F E`, for any class family `c`, and
two actual cuspidal realizations `T`, `T'` of `GL_(r+1)` over `F` with
spectral presentations `P` and `P'`. If `T'` realizes the contragredient of `T`,
and `S` is weakly associated with the spectral system of `P`, then the
algebraic dual `FiniteRepresentation.dual S` is weakly associated with the
spectral system of `P'`.

Provenance: Henniart (2000), *Une preuve simple des conjectures de Langlands
pour GL(n) sur un corps p-adique*, §2.2 (printed p. 444), states that
association is preserved by the two contragredients. The route indicated there
is inversion of the Frobenius and Satake parameters. The Weil-side lemmas below
are elementary linear algebra. The automorphic side is the inverse-spectrum
theorem of the companion helper module
[ContragredientSphericalSpectrum](../ContragredientSphericalSpectrum.md), submitted
with this proof.

## Topology of the class-indexed extension

`RelativeWeilGroup c F E` is the published `ClassExtension (c F E)`. Its topology
is induced from the product of the idele class group of `E` and `E ≃ₐ[F] E`.
The definitions in
[RelativeWeilAssociation](RelativeWeilAssociation.md), and hence the target,
use the default Mathlib topology on `E ≃ₐ[F] E`, the Krull topology. The Library
proves `IsTopologicalGroup` for the extension only under the explicitly
installed discrete topology `relativeGaloisTopology`. These two topologies are
equal but not definitionally equal, so instance search cannot transfer that proof.

- `isTopologicalGroup_krull` proves `IsTopologicalGroup (RelativeWeilGroup c F E)`
  for the Krull topology. The extension `E/F` of number fields is
  finite-dimensional, so Mathlib's
  `krullTopology_discreteTopology_of_finiteDimensional` makes the Krull topology
  discrete. The action of `E ≃ₐ[F] E` on idele classes is then jointly
  continuous, because each `relativeIdeleClassAut F E σ` is continuous
  (`continuous_prod_of_discrete_left`). The cocycle is continuous on the
  discrete group `(E ≃ₐ[F] E) × (E ≃ₐ[F] E)`. The published
  `NormalizedTwoCocycle.Extension.topologicalGroup` then applies. The theorem is
  installed as a local instance only. It is needed by the published
  `FiniteRepresentation.isContinuous_dual_iff`.

## Euler polynomial of the inverse transpose

- `eulerPolynomial_transpose_of_mul_eq_one`: let `A, B` be endomorphisms of a
  finite-dimensional complex space with `B * A = 1`, and let
  `det(1 - X A) = ∏ (1 - z X)` for a size-`n` multiset `s` of units. Then the
  transpose of `B` on the dual space has Euler polynomial
  `∏ (1 - z⁻¹ X)`, that is `Eigenvalues.eulerPolynomial (s.map fun z => z⁻¹)`.

  Proof: let `M` be the matrix of `A` in a chosen basis. Then the matrix of `B` is
  `M⁻¹`, and the dual basis gives the transpose matrix
  (`LinearMap.toMatrix_transpose`). The characteristic polynomial is unchanged by
  transposition. Mathlib's `Matrix.charpoly_inv` expresses the characteristic
  polynomial of `M⁻¹` as `(-1)^d det(M)⁻¹` times the reversed characteristic
  polynomial of `M`. The reversed characteristic polynomial is the Euler
  polynomial `det(1 - X M)` (`Matrix.reverse_charpoly`). So the characteristic
  polynomial of the transpose of `B` is a constant `c` times
  `∏ (1 - z X)`. Its reverse, the Euler polynomial of the transpose of `B`, is
  `c` times the reverse of `∏ (1 - z X)`. The helper
  `PairedHecke.C_mul_eulerPolynomial_map_inv` of
  [PairedHeckeScalars](../../Representation/Unramified/PairedHeckeScalars.md) writes this reverse as
  `∏ (-z)` times `∏ (1 - z⁻¹ X)`. Both Euler polynomials take the value `1` at
  `0`, so evaluation at `0` shows that the total constant is `1`.

## Local components of the dual

Fix a finite place `v` of `F` and a continuous homomorphism
`ι : W_(F_v) → RelativeWeilGroup c F E`.

- `localComponent_dual_isUnramified`: if the local component `S ∘ ι` is trivial on
  the inertia subgroup, so is the local component of the dual. The dual acts by
  the transpose of `S(ι g)⁻¹`, and inertia is a subgroup.
- `localEulerPolynomial_dual`: if the Euler polynomial of `S` at
  `ι(Frob_v)` is `∏ (1 - z X)`, that of the dual is `∏ (1 - z⁻¹ X)`. The dual
  acts on `ι(Frob_v)` by the transpose of `S(ι(Frob_v)⁻¹)`, so the previous lemma
  applies with `A = S(ι(Frob_v))` and `B = S(ι(Frob_v)⁻¹)`.
- `IsUnramifiedMatchAt.dual`: the published unramified matching condition
  `IsUnramifiedMatchAt S v (Eigenvalues.eulerPolynomial s)` implies the
  condition for the dual with `s.map fun z => z⁻¹`. For every place `w` of `E`
  above `v`, the condition asserts that some map `ι` with
  `IsLocalRelativeWeilMap v w e ι` exists for some reciprocity candidate `e`. It
  also asserts that every such pair `e, ι` gives an unramified local component
  with the stated Euler polynomial. The existence part does not involve `S` and
  is reused. The two previous lemmas are applied to each such map. The local
  maps are not changed.

## The presented form

`presentedContragredientAssociation` proves the target proposition at all four
universe levels. The published `isWeaklyAssociated_iff_exists_finset` turns the
hypothesis into continuity of `S`, rank `r + 1`, and a finite set `U` containing
the exceptional set of `P` outside of which the unramified match holds. The
conclusion is proved through the same lemma:

- Continuity of the dual is `FiniteRepresentation.isContinuous_dual_iff`, using
  `isTopologicalGroup_krull`.
- The rank of the dual is `FiniteRepresentation.rank_dual`.
- The finite set is `U ∪ P'.exceptional`. It contains the exceptional set of
  `P'`.
- At a place `v` outside it, `v` lies outside both exceptional sets.
  `CuspidalOperatorRealization.eigenvalues_eq_map_inv_of_isContragredientOf`
  shows that the spectrum of `P'` at `v` is the inverse of the spectrum of `P` at
  `v`. `IsUnramifiedMatchAt.dual` then transfers the match of `S` at `v`.

No arithmetic-class, unitarity or irreducibility hypothesis on `S` is used. The
supplied local relative Weil maps, presentations and contragredient relation
are those of the statement.

## The class form from presentation existence

`classContragredientAssociation_of_dualPresentationExistence` proves
`ClassContragredientAssociationStatement.{u, uV, uP, uQ}` from one hypothesis
`hex : Langlands.Automorphic.CuspidalDualPresentationExistenceStatement.{u, uP, uQ}`
(the published statement of
[CuspidalDualPresentationExistenceStatement](../CuspidalDualPresentationExistenceStatement.md)):
for every `F : Type u` with `Field F`, `NumberField F` and
`CompactSpace (AdeleQuotient F)`, every `r`, and every pair
`T T' : CuspidalOperatorRealization F r` with
`T'.realization.IsContragredientOf T.realization`, a presentation
`CuspidalSpectralPresentation.{u, uP} T` gives
`Nonempty (CuspidalSpectralPresentation.{u, uQ} T')`. It has no unitarity
premise. This theorem does not prove the class form unconditionally; a proof of
that statement is the subject of task 38e20519-c46d-4ada-8c60-a8037975fae1.

Proof: choose representatives `T` of `π` and `T'` of `π'`
(`IsoClass.exists_representative`). The published
`isWeaklyAssociatedClass_isoClass_iff` gives a presentation `P` of `T` whose
spectral system is weakly associated with `S`.
`CuspidalOperatorRealization.isoClass_isContragredientOf_iff` turns the class
relation into `T'.realization.IsContragredientOf T.realization`. Then `hex`
supplies a presentation `P'` of `T'` in universe `uQ`. The presented form
gives weak association of the dual of `S` with the spectral system of `P'`, and
`isWeaklyAssociatedClass_isoClass_iff` turns this back into the class relation
for `π'`.
