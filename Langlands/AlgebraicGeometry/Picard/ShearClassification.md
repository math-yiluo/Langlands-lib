# Classifying the shear pullback of a Picard-zero family

Module `Langlands.AlgebraicGeometry.Picard.ShearClassification` is a helper
module for the proof of
`Langlands.AbelianScheme.FieldDualSchemeMapAdditivityStatement`. Let `B/S` be an
abelian scheme with `hB : HasDualScheme B`, let `T : Over S`, and let `L` be a
rigidified family on `T ×_S B` with `IsPicardZeroFamily B L`. The module pulls
the underlying bundle of `L` back along the shear map
`(t, b, b') ↦ (t, b * b')` on `(T ×_S B) ×_S B`, and classifies the result by a
map `φ : T ×_S B ⟶ B^∨`. It then shows that `φ` factors through the projection
to `T`. Everything is in the namespace `Langlands.AbelianScheme`.

Several results take explicit proofs of unproved Library propositions as
arguments:

* `preservation : pullbackTensorComparisonIsIsoStatement`, which makes
  `LineBundle.tensor` available;
* `classification : PicardZeroLineBundleClassificationStatement`;
* `stability : PicardZeroPullbackStatement`;
* `globalFunctions : Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctions`.

The module proves no instance of these propositions.

## Definitions and small lemmas

* `poincarePullback B hB φ` is the underlying line bundle of
  `RigidifiedLineBundle.relativePullback B.X.hom (unitSection B) _ φ` applied
  to `poincareFamily B hB`. `poincarePullbackComp B hB h φ` identifies its
  pullback along the induced map of `h : V ⟶ W` with
  `poincarePullback B hB (h ≫ φ)`.
* `rigidificationIso L` is the isomorphism `ε^* L ≅ O` of a rigidified line
  bundle given by its rigidification.
* `shearBundle B L` is the pullback of the underlying bundle of `L` along
  `shear B (relativeFst B T) (relativeSnd B T)`, a bundle on
  `(T ×_S B) ×_S B`.
* `unitSection_shear`: the unit-section map of `(T ×_S B) ×_S B` followed by
  this shear map is the identity.
* `unitPoint B T : T ⟶ relativeOver B T` is the unit section of `T ×_S B`
  as a morphism over `S`. `unitPoint_left_eq_relativeSection`, `unitPoint_fst` and
  `unitPoint_snd` give its underlying morphism and its two components (the
  identity of `T` and the identity point of `B`).

## Classification

* `exists_shearBundle_iso preservation B hB classification stability L hL`
  gives `φ : relativeOver B T ⟶ dualScheme B hB` and an isomorphism
  `shearBundle B L ≅ poincarePullback B hB φ ⊗ pr^* L` of line bundles on
  `(T ×_S B) ×_S B`, where `pr` is the projection to `T ×_S B` and `L` stands
  for its underlying bundle. It applies `classification` to the shear bundle,
  whose Picard-zero hypothesis is `isGeometricallyPicardZero_shear`, and then
  simplifies the restriction along the unit section with `unitSection_shear`.
* `shearRestrictIso preservation e h t`: given such an isomorphism `e`, a
  morphism `h : V ⟶ relativeOver B T`, and a trivialization `t` of `h^* L`,
  the pullback of the shear bundle along the induced map of `h` is isomorphic
  to `poincarePullback B hB (h ≫ φ)`. It combines
  `LineBundle.pullbackTensorObjIso`, `poincarePullbackComp`,
  `LineBundle.pullbackTrivialIso` and `LineBundle.tensorTrivialIso`.
* `unitPointIso preservation e` identifies the underlying bundle of `L` with
  `poincarePullback B hB (unitPoint B T ≫ φ)`. It is `shearRestrictIso` along
  `unitPoint B T` with the trivialization `rigidificationIso L`. The shear map
  restricted along `unitPoint` is the identity by `relativeSpace_map_shear`,
  `unitPoint_fst`, `unitPoint_snd` and `shear_one`.

## Rigidity of the classifying map

* `nonempty_shear_iso B stability K L hL a c`: over an algebraically closed
  field `K`, with `s : Spec K ⟶ S` and points `a : Over.mk s ⟶ T`,
  `c : Over.mk s ⟶ B.X`, the pullbacks of `L` along `shear B a c` and along
  the induced map of `a` are isomorphic. The pullback along `a` is Picard-zero
  by `stability`, hence translation invariant by
  `isTranslationInvariant_of_isGeometricallyPicardZero`. By
  `shearTranslationIso` the shear pullback is its translate.
* `nonempty_iso_trivial_overMk K s F`: every line bundle on `Spec K` is
  trivial (`LineBundle.nonempty_iso_trivial_of_unique`).
* `comp_unitPoint_eq_of_algClosed`: for a geometric point
  `x : Spec K ⟶ T ×_S B` with `K` algebraically closed,
  `x ≫ φ = x ≫ pr_T ≫ e_T ≫ φ` on underlying morphisms. Both `x` and the
  point `x2 = x ≫ pr_T ≫ e_T` give isomorphic pullbacks of `P`. The
  isomorphism goes through `shearRestrictIso` at `x` and at `x2`, the
  trivializations of `L` at both points, and `nonempty_shear_iso`.
  `RigidifiedLineBundle.nonempty_iso_of_forget_iso` (module
  `RigidifiedCarrierIso`) upgrades it to an isomorphism of rigidified bundles.
  Injectivity of the classifying map `dualPointClass_injective` then gives
  `x ≫ φ = x2 ≫ φ`.
* `eq_relativeFst_unitPoint_comp preservation stability globalFunctions hL e`:
  `φ = relativeFst B T ≫ unitPoint B T ≫ φ`. By the previous lemma, applied at
  an algebraic closure of each residue field, the underlying maps of `φ` and
  of `pr_T ≫ e_T ≫ φ` agree on all points. `globalFunctions` shows that
  `pr_T : T ×_S B ⟶ T` induces isomorphisms on sections over every open of
  `T`. The published `Langlands.AlgebraicGeometry.factorizationOfGlobalFunctions`
  then gives equality of morphisms of schemes.

## Provenance

Internal formalization of the rigidity step in the proof of the theorem of the
square. Pulled back along the group law, a Picard-zero family has classifying
map constant along the fibres of `T ×_S B ⟶ T`. Compare Edixhoven, van der
Geer and Moonen, *Abelian Varieties* (registered
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), Chapter VI, (6.2),
printed p.88 (PDF p.92), for rigidified line bundles and the classification of
line bundles on `X_T` modulo pullbacks from `T`. The
Lean form of that classification is the separate proposition
`PicardZeroLineBundleClassificationStatement`.
