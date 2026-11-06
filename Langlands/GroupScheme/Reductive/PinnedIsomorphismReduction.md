# Reduction of the pinned Isomorphism Theorem to three prerequisites

Author: Worker 1416.

This internal assembly proves two transport lemmas and a conditional result,
and bundles the hypotheses of the conditional result into one proposition.

- `Langlands.GroupScheme.IsRootDatumOf.precomp_torusIso` and
  `Langlands.GroupScheme.IsMaximalTorus.precomp_torusIso` move a root datum
  and maximality of a torus embedding along an isomorphism of tori.
- `Langlands.GroupScheme.PinnedIsomorphism.Prerequisites` is the proposition

  ```text
  SplitCommonTorusIsomorphismStatement.{u} ∧ PinnedRootScalingStatement.{u} ∧
    PinnedAutomorphismRigidityStatement.{u}
  ```

- `PinnedIsomorphism.exists_iso` (existence) and `PinnedIsomorphism.iso_ext`
  (uniqueness) are the two halves of the conditional result, and
  `PinnedIsomorphism.pinnedIsomorphismStatement_of_prerequisites` derives
  the published `PinnedIsomorphismStatement.{u}`
  ([`PinnedIsomorphismStatement`](PinnedIsomorphismStatement.md)) from
  `Prerequisites.{u}`.

The three hypotheses, in this order, are:

- `SplitCommonTorusIsomorphismStatement`
  ([`SplitIsomorphismStatement`](SplitIsomorphismStatement.md)): two
  connected reductive groups over a field with a common split maximal torus
  and root data matched by a bijection of indices are isomorphic over the
  torus;
- `PinnedRootScalingStatement`
  ([`PinnedRootScalingStatement`](PinnedRootScalingStatement.md)): for any
  units `c a`, one for each simple root of a pinned group, some automorphism
  is the identity on the pinned torus and multiplies each chosen simple-root
  vector by `c a`;
- `PinnedAutomorphismRigidityStatement`
  ([`PinnedRigidityStatement`](PinnedRigidityStatement.md)): an automorphism
  of a pinned group that is the identity on the pinned torus and fixes every
  chosen simple-root vector is the identity.

All three are published statements, and the module proves none of them. The
conclusion is the unchanged target statement, with every binder and the full
conclusion.

The module also uses the torus isomorphism of a root-datum equivalence from
[`PinningLattice`](PinningLattice.md) (Worker 1467):
`SplitPinning.torusIsoOfRootDatumEquiv p q e : p.torus ≅ q.torus`, with its
character equation `torusIsoOfRootDatumEquiv_character` (the inverse
character pullback is `e.weightEquiv`), its cocharacter equation
`torusIsoOfRootDatumEquiv_cocharacter` (the cocharacter map is
`e.coweightEquiv.symm`), the root and coroot equations
`torusIsoOfRootDatumEquiv_root` and `torusIsoOfRootDatumEquiv_coroot`, and
the extensionality lemma `IsSplitTorus.iso_ext_of_character_congr`.

## Provenance

The assembly is internal. It follows Conrad's derivation of the Isomorphism
Theorem: B. Conrad, *Reductive group schemes* (2014), SGA3 summer school
notes, printed page = PDF page. Theorem 6.1.17 (p.197) is stated there as
"an immediate consequence of Theorem 6.1.16 and the arguments with the
Z-basis ∆ of X(T/Z_G) in the proof of Corollary 6.1.15". In this module,
the common-torus Isomorphism Theorem plays the role of Theorem 6.1.16(1)
for isomorphisms with the identity on the torus. The scaling statement is
the Z-basis argument of the proof of Corollary 6.1.15 (p.196), which
adjusts an isomorphism by an element of `(T/Z_G)(S)` until it matches the
pinnings. The rigidity statement is the faithfulness of Corollary 6.1.15
(p.195), which Conrad takes from Proposition 6.1.13(2) (p.194). The
transport lemmas and the bookkeeping are internal and add no claim from
the literature.

## The transport lemmas

Work over a field `k : Type u` with commutative group schemes `T`, `T'`
over `Spec k`, a group scheme `H` with an `IsAffineHom H.X.hom` instance, an
isomorphism `t : T ≅ T'` and a homomorphism `j : T'.toGrp ⟶ H`. Write
`groupHom t.hom ≫ j` for the composite `T.toGrp ⟶ T'.toGrp ⟶ H`. A private
helper checks the square `j ≫ 𝟙 = groupHom t.symm.hom ≫ (groupHom t.hom ≫ j)`;
this is the commuting square that the published transport lemmas expect,
for the isomorphism `t.symm` of tori and the identity of `H`.

`IsRootDatumOf.precomp_torusIso` assumes a root datum `Q` of `j` (indexed by
any `J'`), a root datum `P` on the actual lattices of `T` (indexed by any
`J`) whose pairing is the actual lattice pairing `latticePairing T`, and an
equivalence `e : RootPairing.Equiv P Q` whose weight map is
`characterLattice.congr t`. It concludes `IsRootDatumOf (groupHom t.hom ≫ j) P`.

Proof. The pairing condition is the hypothesis on `P`. From the hypothesis
on `e`, `characterLattice.congr t (P.root a) = Q.root (e.indexEquiv a)`
(by `RootPairing.Equiv.root_weightMap_apply`), and
`characterLattice.congr t` carries `P.reflection a` to
`Q.reflection (e.indexEquiv a)` (by Mathlib's
`RootPairing.Equiv.weightEquiv_reflection`).

- *Roots.* `roots_image_of_transport`
  ([`Rational.CrossTorusLieTransport`](../Rational/CrossTorusLieTransport.md)),
  applied to the square above, gives
  `characterLattice.congr t.symm '' roots j = roots (groupHom t.hom ≫ j)`.
  With `roots j = range Q.root`, the root equation and the bijectivity of
  `e.indexEquiv`, this image is `range P.root`.
- *Reflections.* For an index `α`, the root datum `Q` gives a `k`-point `n`
  of `H` normalizing `j` whose action on characters is
  `Q.reflection (e.indexEquiv α)`. `IsNormalizingPoint.transport`
  ([`Rational.CrossTorusWeylTransport`](../Rational/CrossTorusWeylTransport.md)),
  applied to the same square, shows that `n` also normalizes
  `groupHom t.hom ≫ j`, with the torus automorphism conjugated by `t`. Its
  action on characters is `P.reflection α`: after applying the injective map
  `characterLattice.congr t`, this is the reflection equation above, and
  unfolding `characterAut` and `characterLattice.congr` closes the goal.

`IsMaximalTorus.precomp_torusIso` says that if `i : T'.toGrp ⟶ H` is a
maximal torus then so is `groupHom t.hom ≫ i`. It is the published
`IsMaximalTorus.iso_comp` ([`Torus.MaximalTransport`](../Torus/MaximalTransport.md))
applied to the isomorphism `T.toGrp ≅ T'.toGrp` underlying `t`, built by a
private helper.

## Existence

`PinnedIsomorphism.exists_iso` takes pinnings `p : SplitPinning G` and
`q : SplitPinning H` of group schemes over `Spec k` with affine structure
morphisms, the common-torus statement, the scaling statement, an
equivalence `e : RootPairing.Equiv p.rootDatum q.rootDatum`, and the
hypothesis that `e.indexEquiv` matches the supports of the bases. It gives a
`SplitPinning.Iso p q` whose torus component is
`t := p.torusIsoOfRootDatumEquiv q e` and whose index bijection is
`e.indexEquiv`.

1. **Moving `H` onto the torus of `p`.** By `IsRootDatumOf.precomp_torusIso`
   (with `Q = q.rootDatum`, `P = p.rootDatum` and the character equation of
   `t`), `p.rootDatum` is a root datum of `groupHom t.hom ≫ q.inclusion`, and
   by `IsMaximalTorus.precomp_torusIso` this composite is a maximal torus of
   `H`.
2. **The common-torus isomorphism.** Apply
   `SplitCommonTorusIsomorphismStatement` with `G₁ = G`, `G₂ = H`, the split
   torus `p.torus`, `i₁ = p.inclusion`, `i₂ = groupHom t.hom ≫ q.inclusion`,
   `P₁ = P₂ = p.rootDatum` and the identity bijection of `p.rootIndex`. It
   gives `ψ : G ≅ H` with `p.inclusion ≫ ψ.hom = groupHom t.hom ≫ q.inclusion`.
3. **Simple-root vectors.** For a simple root `a` of `p`, write `s a` for the
   simple root `e.indexEquiv a` of `q`. By
   `lieKernelHomLinear_mem_weightSpace_of_transport`
   ([`Rational.CrossTorusLieTransport`](../Rational/CrossTorusLieTransport.md))
   and the square of step 2, the differential
   `Lie.targetMapLinear ψ.hom` sends `p.pinning.rootVector a` into the weight
   space of `characterLattice.congr t (p.rootDatum.root a)`, which is
   `q.rootDatum.root (s a)` by the root equation of `t`. The inverse of the
   trivialization of that line gives `c a : k` with
   `dψ (p.pinning.rootVector a) = c a • q.pinning.rootVector (s a)`
   (`RootPinning.trivialization_apply_val`). Here `c a ≠ 0`: otherwise
   `dψ` kills `p.pinning.rootVector a`, and applying the differential of
   `ψ.inv` (`Lie.targetMapLinear_hom_inv`) makes that vector zero, against
   `RootPinning.rootVector_ne_zero`.
4. **Scaling.** The scaling statement for `p` and the units `(c a)⁻¹` gives
   `σ : G ≅ G` with `p.inclusion ≫ σ.hom = p.inclusion` and
   `dσ (p.pinning.rootVector a) = (c a)⁻¹ • p.pinning.rootVector a`.
5. **Assembly.** Put `groupIso := σ ≪≫ ψ`. The square holds because
   `p.inclusion ≫ σ.hom ≫ ψ.hom = p.inclusion ≫ ψ.hom`. By
   `Lie.targetMapLinear_comp`
   ([`Rational.RootKernelIdentityWeights`](../Rational/RootKernelIdentityWeights.md)),
   the differential of `σ ≫ ψ` sends `p.pinning.rootVector a` to
   `(c a)⁻¹ • c a • q.pinning.rootVector (s a) = q.pinning.rootVector (s a)`.
   The root and coroot fields are the root and coroot equations of `t`, and
   the support field is the hypothesis on `e`.

## Uniqueness

`PinnedIsomorphism.iso_ext` assumes the rigidity statement and two pinned
isomorphisms `f f' : SplitPinning.Iso p q` with equal torus components and
equal index bijections. It concludes `f = f'`.

Proof. Let `σ := f.groupIso ≪≫ f'.groupIso.symm`, an automorphism of `G`.

- *Identity on the torus.* By the square of `f`,
  `p.inclusion ≫ σ.hom = groupHom f.torusIso.hom ≫ q.inclusion ≫ f'.groupIso.inv`.
  `torusTransport_inverse_square`
  ([`Rational.CrossTorusWeylTransport`](../Rational/CrossTorusWeylTransport.md))
  rewrites `q.inclusion ≫ f'.groupIso.inv` as
  `groupHom f'.torusIso.inv ≫ p.inclusion`. Since the torus components are
  equal, this is `groupHom (f'.torusIso.hom ≫ f'.torusIso.inv) ≫ p.inclusion =
  p.inclusion`.
- *Fixed simple-root vectors.* Since the index bijections are equal, `f` and
  `f'` send the simple root `a` to the same simple root of `q`. So the
  root-vector fields of `f` and `f'` give
  `dσ (p.pinning.rootVector a) = d(f'.groupIso.inv) (q.pinning.rootVector _)
  = p.pinning.rootVector a`, by `Lie.targetMapLinear_comp` and
  `Lie.targetMapLinear_hom_inv`.

Rigidity gives `σ = Iso.refl G`, hence `f.groupIso.hom ≫ f'.groupIso.inv = 𝟙`
and `f.groupIso = f'.groupIso`. All other fields of `SplitPinning.Iso` are
propositions, so `f = f'` after destructuring both structures and
substituting the three equalities.

## The target

`pinnedIsomorphismStatement_of_prerequisites` takes `Prerequisites.{u}` and
the data of `PinnedIsomorphismStatement`: a field `k`, `G`, `H`, `p`, `q`, `e`
and the support hypothesis. `exists_iso` gives `f` with `f.torusIso = t` and
`f.indexEquiv = e.indexEquiv`, and the character and cocharacter equations of
`t` give the first two conditions. For another `f'` with the three
conditions, the character condition says that `f'.torusIso` and `t` induce
the same map on characters, so `IsSplitTorus.iso_ext_of_character_congr`
(applied to the split torus of `p`) gives `f'.torusIso = f.torusIso`. The
index bijections agree with `e.indexEquiv`, and `iso_ext` gives `f' = f`.
The cocharacter condition on `f'` is not used for uniqueness.

All declarations have the universe parameter `u`.
`IsRootDatumOf.precomp_torusIso` has two more universe parameters, for its
index types `J` and `J'`. All declarations use only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.
