# Extensions of multiplicative-type groups with connected quotient are commutative

This module treats the connected case of part 1 of
[`MultiplicativeTypeFieldExtensionStatement`](MultiplicativeTypeFieldExtensionStatement.md)
(SGA 3, Exposé IX, Proposition 8.2 (i)). It proves:

> Let `k` be a field, `i : H ⟶ G` a monomorphism and `p : G ⟶ K` an fppf
> quotient map with kernel the range of `i`
> (`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p`). If `H` and `K`
> are of multiplicative type (`IsMultiplicativeType`) and `K` is connected
> (`ConnectedSpace K.X.left`), then `G` is commutative (`IsCommMonObj G.X`).

This is `isCommMonObj_of_connectedSpace`. With `G` commutative, the commutative
case of part 1 then shows that `G` is of multiplicative type. No smoothness or
reducedness is assumed: `H` and `K` may be infinitesimal.

## Contents

### The diagonalizable case (`Langlands.GroupScheme.CentralExtensionHopfSpec`)

* `isExtension_diagonalizable φ π hz hq`: let `φ : K[Λ'] ⟶ A` and
  `π : A ⟶ K[Λ]` be maps of commutative Hopf algebras over a field `K`.
  Suppose `Spec π` is a closed subgroup and `Spec φ` is an fppf quotient map
  with kernel the range of `Spec π`. Then `φ` and `π` satisfy
  [`ConnectedExtensionHopf.IsExtension`](../../Algebra/ConnectedExtensionHopf.md).
  The proof is that of the Library's `CentralExtensionHopfSpec.isCentralExtension`
  without the centrality field, using the general lemmas of
  [`CentralExtensionHopfSpec`](CentralExtensionHopfSpec.md):
  - `faithfullyFlat_of_isFppfQuotient` gives injectivity of `φ`;
  - `surjective_of_isClosedSubgroup` gives surjectivity of `π`;
  - `comp_eq_of_range_kernelι` gives `π ∘ φ = ε`;
  - `exists_eq_of_lTensor_comul_eq` gives the invariants.
* `isCommMonObj_of_diagonalizable_connected`: let `E` be a group scheme over a
  field `K` with affine total space, `z : Z ⟶ E` a closed subgroup, and
  `p : E ⟶ T` an fppf quotient map with kernel the range of `z`. If
  `Z ≅ D_K(Λ)`, `T ≅ D_K(Λ')` and `T` is connected, then `E` is commutative.
  1. As in `CentralExtensionHopfSpec.isSplitTorus_of_split`, transport `z` and
     `p` to Hopf algebra maps `π`, `φ` on the coordinate Hopf algebra
     `A = AffineCoordinates.hopfAlgebra E`, and apply
     `isExtension_diagonalizable`.
  2. `T.X.left` maps homeomorphically onto `(D_K(Λ')).X.left = Spec K[Λ']`, so
     `Spec K[Λ']` is connected. Its idempotents are therefore `0` and `1`, by
     `Diagonalizable.SmoothConnectedCriteria.eq_zero_or_one_of_connectedSpace`.
  3. `ConnectedExtensionHopf.isCocomm` makes `A` cocommutative. Mathlib's
     instance `isCommMonObj_spec_asOver_spec` makes `Spec A` commutative. The
     monoid isomorphism `Spec A ≅ E` (`AffineCoordinates.hopfSpecIso`) and the
     Library's `isCommMonObj_of_iso` transport commutativity to `E`.

### Base change and descent (`Langlands.GroupScheme`)

* `geometricallyConnected_of_connectedSpace`: a connected affine group scheme
  of finite type over a field is geometrically connected. The proof repeats the
  private lemma `geometricallyConnected_of_connected_affine` of
  [`SmoothConnectedGeometryProof`](../SmoothConnectedGeometryProof.md). That
  lemma uses the Library's
  `GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent`:
  the identity component is open and geometrically connected, and for a
  connected group it is everything.
* `baseChangeCompIso'`: base change along `c ≫ b` is base change along `b`,
  then along `c`. This is the isomorphism used privately in
  [`Torus/BaseChange`](BaseChange.md).
* `diagonalizableBaseChangeIso g eH`: if `H` becomes `D_L(N)` over `L`, then
  over any field `E` with `g : L →+* E` it becomes `D_E(N)`
  (`Diagonalizable.baseChangeIso`).
* `isCommMonObj_of_connectedSpace`: the main theorem.
  1. `K` is geometrically connected. It is affine and of finite type because it
     is of multiplicative type (`IsMultiplicativeType.isAffineHom`,
     `IsMultiplicativeType.locallyOfFiniteType`).
  2. Let `L₁` split `H` and `L₂` split `K`. Take a common extension `E` of `L₁`
     and `L₂` over `k` (`TorusBaseChange.commonExtension`), and base change
     along `b : Spec E → Spec L₁ → Spec k`. Over `E`, `H ≅ D_E(N)` and
     `K ≅ D_E(M)` (`diagonalizableBaseChangeIso`). For `K` this uses
     `Spec E → Spec L₂ → Spec k`, which equals `b` by compatibility of the two
     embeddings.
  3. The base-changed `i` is a closed subgroup. Over a field `i` is one
     (`IsFppfQuotient.isClosedSubgroup_of_field` from
     [`CentralDiagonalizableExtensionSplit`](CentralDiagonalizableExtensionSplit.md)),
     and this is stable under base change (`IsClosedSubgroup.baseChange`).
     `IsFppfQuotient.baseChange` and `SubgroupFunctor.range_baseChangeHom`
     give the fppf quotient over `E`.
  4. The base-changed `G` is affine. Its `p` is affine by
     `IsFppfQuotient.isAffineHom_of_isAffineHom_kernel` (same module), since
     the base-changed `H` is diagonalizable. The base-changed `K` is affine
     too.
  5. The base-changed `K` is connected. Geometric connectedness is stable
     under base change, and `Spec E` is a point
     (`GeometricallyConnected.connectedSpace_of_subsingleton`).
  6. `isCommMonObj_of_diagonalizable_connected` makes the base-changed `G`
     commutative. `isCommMonObj_of_baseChange` descends commutativity along
     the faithfully flat quasi-compact map `b` (`fieldExtension_fpqc`, twice).

## Dependencies

This module imports two modules written for the same result:

- [`ConnectedExtensionHopf`](../../Algebra/ConnectedExtensionHopf.md), the
  algebraic core;
- [`CentralDiagonalizableExtensionSplit`](CentralDiagonalizableExtensionSplit.md),
  for `isClosedSubgroup_of_field` and `isAffineHom_of_isAffineHom_kernel`.

## Provenance

Internal to this project. The statement is the connected case of SGA 3, Exposé
IX, Proposition 8.2 (i), as in Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, Corollary 12.42 (printed p.244). See the page of
`MultiplicativeTypeFieldExtensionStatement`. The proof replaces Milne's rigidity argument by the
Hopf-algebra argument of `ConnectedExtensionHopf`, after base change to a
common splitting field.
