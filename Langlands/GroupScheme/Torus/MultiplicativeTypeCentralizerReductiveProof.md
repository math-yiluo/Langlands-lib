# Centralizers of multiplicative-type groups in connected reductive groups: proof

The theorem `Langlands.GroupScheme.multiplicativeTypeCentralizerReductive` proves exactly
the published proposition
`Langlands.GroupScheme.MultiplicativeTypeCentralizerReductiveStatement.{u}`, imported from
[`Torus.MultiplicativeTypeCentralizerReductiveStatement`](MultiplicativeTypeCentralizerReductiveStatement.md).
It holds in every universe `u`. It covers every field `k`, every connected reductive `G`
over `Spec k`, every commutative `H` with `IsMultiplicativeType H.toGrp`, every
homomorphism `i : H.toGrp ⟶ G`, and every closed representative `j : C ⟶ G` of
`torusCentralizer i`. It adds no hypotheses. The conclusion is the statement's
`∃ hC : Smooth C.X.hom, IsConnectedReductive (identityComponent C)`.

The module adds no axioms and has no proof holes. Besides the main theorem it contains
five helper declarations in the namespace
`Langlands.GroupScheme.MultiplicativeTypeCentralizer`. Each is described below.

## Route

`IsMultiplicativeType H.toGrp` supplies a field extension `K` of `k`, a finitely generated
abelian group `Λ`, and an isomorphism `e` from the base change of `H` to `K` onto the
diagonalizable group `D(Λ)` over `K`. The proof does not pass to an algebraic closure. It
proves both conclusions over `K`, where the acting group is `D(Λ)`, and then brings them
back to `k`.

## The split case over a field

The helpers work over a field `K`. They take a group scheme `G` over `Spec K`, a
commutative `H`, an isomorphism `e : H.toGrp ≅ D(Λ).toGrp`, a homomorphism
`i : H.toGrp ⟶ G`, and a representative `j : C ⟶ G` of `torusCentralizer i`.

- `splitAction e i` is the conjugation action of `H` on `G` through `i`
  (`AutomorphicAction.conjugation i`, module [`AutomorphicAction`](../AutomorphicAction.md)), with the acting group changed to `D(Λ)` by
  restricting along `e.inv` (`AutomorphicAction.restrict`).
- `splitAction_fixedSubgroup` proves that the fixed subgroup functor of `splitAction e i`
  is `torusCentralizer i`. It rewrites with the published
  `AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer`, then uses
  `AutomorphicAction.fixedSubgroup_restrict_iso` from
  [`Rational.KernelCentralizerSmooth`](../Rational/KernelCentralizerSmooth.md):
  restricting along an isomorphism does not change the fixed subgroup.
- `smooth_of_split` assumes that `G` is smooth and affine and that `j` is a closed
  subgroup. It concludes `Smooth C.X.hom`. It applies the published
  `Diagonalizable.fixedSubgroup_smooth_of_actingIso` (same module) to the unconditional
  theorem `Diagonalizable.FixedSmooth.fixedSubgroupSmooth` from
  [`Torus.DiagonalizableFixedSmoothProof`](DiagonalizableFixedSmoothProof.md). That
  theorem is the smoothness part of CGP Proposition A.8.10(2) for `D(Λ)`-actions.
  It is applied to the conjugation action, with the acting group identified with
  `D(Λ)` through `e`.
- `exists_affineQuotient_of_split` assumes that `G` is smooth and affine and that `j`
  represents `torusCentralizer i`; it needs neither closedness of `j` nor smoothness of
  `C`. It produces a
  `HomogeneousQuotientFromEmbedding.HomogeneousQuotient j` whose quotient scheme is
  affine over `K`. This follows the geometric argument in the proof of CGP Proposition
  A.8.12, step by step, for the action `a = splitAction e i`:
  1. `AutomorphicAction.AffineFiniteTypeCocycleModelProof.affineFiniteTypeCocycleModel`
     gives a cocycle model `M` of `a` that is affine and locally of finite type over `K`.
     This is the Library form of CGP Lemma A.8.13.
  2. `Diagonalizable.cocycleModelActionRelationSmooth` (module
     [`Torus.CocycleModelActionRelationSmoothProof`](CocycleModelActionRelationSmoothProof.md))
     shows that the action relation `G × M → M × M` of `M` is smooth.
  3. `SchemeAction.smoothActionAffineOrbit` (module
     [`SmoothActionAffineOrbitProof`](../SmoothActionAffineOrbitProof.md)) is applied at
     the base point of `M`, the trivial cocycle. It gives an affine scheme `O`, a smooth
     surjective `p : G.X ⟶ O`, and an open immersion `f : O ⟶ M.scheme` with
     `p ≫ f = M.orbit`. The open immersion is a monomorphism, also in `Over`.
  4. `CocycleModel.affineHomogeneousQuotientOfOrbit` and
     `affineHomogeneousQuotientOfOrbit_isAffineHom` (module
     [`AutomorphicAction.AffineCocycleQuotient`](../AutomorphicAction/AffineCocycleQuotient.md))
     turn this orbit into the homogeneous quotient and prove that it is affine. Their
     fixed-subgroup hypothesis comes from `splitAction_fixedSubgroup` and the given
     representation.
- `isConnectedReductive_of_split` assumes `IsConnectedReductive G`, a closed
  representative `j`, and `C` smooth and affine. It concludes
  `IsConnectedReductive (identityComponent C)`. It takes the affine quotient from
  `exists_affineQuotient_of_split` and applies the unconditional theorem
  `affineHomogeneousQuotientReductive` from
  [`Reductive.AffineHomogeneousQuotientProof`](../Reductive/AffineHomogeneousQuotientProof.md):
  a smooth closed subgroup of a connected reductive group with an affine homogeneous
  quotient has connected reductive identity component.

## The main theorem

Let `b = Spec.map (CommRingCat.ofHom (algebraMap k K))`. By `fieldExtension_fpqc` (module
[`BaseChangeReflection`](../BaseChangeReflection.md)), `b` is surjective, flat and
quasi-compact.

1. `connectedReductiveFieldExtensionStatement` (module
   [`Reductive.FieldExtensionProof`](../Reductive/FieldExtensionProof.md)) gives
   `IsConnectedReductive G_K` for the base change `G_K` of `G` along `b`.
2. `torusCentralizer_baseChange` (module
   [`Torus.MaximalBaseChangeForwardReduction`](MaximalBaseChangeForwardReduction.md))
   identifies the centralizer of the base-changed homomorphism with the base change of
   `torusCentralizer i`. With `SubgroupFunctor.IsRepresentedBy.baseChange` (module
   [`SubgroupBaseChange`](../SubgroupBaseChange.md)), the base change of `j` represents
   the centralizer of the base change of `i`. `IsClosedSubgroup.baseChange` (same module)
   shows that it is still a closed subgroup.
3. `smooth_of_split` applies over `K` with the isomorphism `e`, so `C_K` is smooth.
   `smooth_of_baseChange` (module
   [`Rational.UnipotentRadicalProperties`](../Rational/UnipotentRadicalProperties.md))
   descends smoothness along the fpqc morphism `b`. This gives the witness
   `hC : Smooth C.X.hom`.
4. With this witness the proof rebuilds the affineness instance that the statement
   derives (closed immersion `j` composed with the affine structure morphism of `G`,
   then `Over.w`). This is the same construction, so `identityComponent C` is the
   statement's object.
5. `isConnectedReductive_of_split` applies over `K`, so the identity component of `C_K`
   is connected reductive. `IdentityComponent.baseChangeIso C (algebraMap k K)` (module
   [`IdentityComponent`](../IdentityComponent.md)) identifies it with the base change of
   `identityComponent C`, and `IsConnectedReductive.of_iso` (module
   [`Dynamic.CentralizerReductiveTransport`](../Dynamic/CentralizerReductiveTransport.md))
   transports reductivity along this isomorphism. Finally
   `IsConnectedReductive.of_fieldExtension` (module
   [`Reductive.SemisimpleFieldReflectionProof`](../Reductive/SemisimpleFieldReflectionProof.md))
   descends connected reductivity from `K` to `k`.

## Provenance

The statement's Markdown records the source: Conrad, *Reductive group schemes* (2014),
Remark 3.1.5, field case, resting on Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
second edition (2015), Propositions A.8.10(2) and A.8.12. The proof follows that source.
Smoothness of the fixed locus is A.8.10(2). Reductivity of its identity component follows
the proof of A.8.12: an affine finite-type cocycle model (Lemma A.8.13), smoothness of the
action relation, an affine orbit of the trivial cocycle, and then the criterion that a
smooth closed subgroup with an affine homogeneous quotient has reductive identity
component. Each step is a published, proved Library theorem; this module only assembles
them.

The source works over an algebraically closed field, where `H` is diagonalizable. The
proof instead works over the extension `K` given by `IsMultiplicativeType`, where `H` is
already isomorphic to `D(Λ)`, and descends both conclusions with the Library's fpqc
smoothness descent and its field-extension reflection of connected reductivity. This
change of route is internal to the proof. The torsion of `Λ` is not removed: the
diagonalizable inputs allow any finitely generated `Λ`, including torsion divisible by the
characteristic.
