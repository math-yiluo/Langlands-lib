# Identity and composition of canonical dual base change

This module constructs the identity and composition comparisons for actual
rigidified-family pullback and proves the resulting equations for the canonical
dual-scheme base-change maps. These are derived consequences of the existing
fibre-product constructions, rigidified pullback coherence and universal Picard
classification. No additional base-change coherence proposition is assumed.

The namespace is `Langlands.AbelianScheme`, with arbitrary schemes in universe
`u`. Let `A` be an abelian scheme over `S`, and let `b : S' ⟶ S` and
`c : S'' ⟶ S'`. Write `A_b`, `A_c,b` and `A_d` for the actual pullbacks
`(baseChange b).obj A`, `(baseChange c).obj A_b` and
`(baseChange (c ≫ b)).obj A` respectively. The imported comparison
`baseChangeCompIso b c A` is directed from `A_d` to `A_c,b`.
All products and maps below use the existing parameter-first relative space
`T × A` over the appropriate base.

## Identity for actual families and classes

For `T : Over S`, `familyBaseChangeSpaceMap_id` identifies the actual
identity-base total-space map with the composite of the map induced by
`(baseChangeIdIso A).hom : A_id ⟶ A` and the relative-space map induced by
`(Over.mapId S).inv.app T : T ⟶ (Over.map (𝟙 S)).obj T`.
The proof compares the two fibre-product projections. Its second component
uses the underlying-scheme projection formula for the group-scheme identity
comparison.

`familyBaseChangeIdIso` lifts this equality to a natural isomorphism of
functors on actual rigidified line bundles:

```
familyBaseChange id A T ≅
  relativePullback A ((Over.mapId S).inv.app T) ⋙
    homFamilyPullback (baseChangeIdIso A).hom T.
```

Here and below `relativePullback A` abbreviates the existing
`RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
(unitSection_comp A)`; the Lean uses its full expression. The equality of total
maps first gives `pullbackCongr`; the inverse of `pullbackComp` then gives the
displayed composite. Section compatibility follows from preservation of the
unit and naturality of the actual relative section.

`rigidifiedClassesBaseChange_id` is the same comparison on isomorphism classes:
identity-base class pullback is `homClassesPullback` along the abelian-scheme
identity comparison after class pullback along the parameter comparison.
Its proof uses quotient induction and the component of `familyBaseChangeIdIso`.
It asserts equality of classes, with the necessary parameter transport retained.

## Composition for actual families and classes

Set `h_T = (Over.mapComp c b).hom.app T` for `T : Over S''`. This map goes
from the parameter regarded directly over `S` to the parameter regarded over
`S` successively through `S'`. Write `F_b(T)` for the existing actual
`familyBaseChangeSpaceMap b A T`, with the abelian scheme and parameter
adjusted as required by its type. Then `familyBaseChangeSpaceMap_comp` proves

```
F_c(T) ≫ F_b((Over.map c).obj T) =
  (homFamilySpaceMap (baseChangeCompIso b c A).inv).app T ≫
    F_(c ≫ b)(T) ≫ (relativeSpace A.X.hom).map h_T.
```

The proof expands the actual total-space maps and compares both projections.
The second projection uses `GroupScheme.baseChangeCompIso_inv_fst` and the
actual structure map of `A_b`.

`familyBaseChangeCompIso` is the natural isomorphism

```
familyBaseChange b A ((Over.map c).obj T) ⋙
  familyBaseChange c A_b T ≅
    (relativePullback A h_T ⋙ familyBaseChange (c ≫ b) A T) ⋙
      homFamilyPullback (baseChangeCompIso b c A).inv T.
```

It collapses the successive pullback functors using the existing proved
`RigidifiedModule.pullbackCoherence`, applies the total-space equality through
`pullbackCongr`, and expands the direct route using two inverse composition
comparisons. Every section square is proved from the actual relative section.
The construction includes the parameter maps, whose underlying scheme maps
are identities for `h_T`.

`rigidifiedClassesBaseChange_comp` descends the components of this isomorphism
by quotient induction. Thus for a class `q` on the successive old-base
parameter, the successive class pullback equals

```
homClassesPullback (baseChangeCompIso b c A).inv T
  (rigidifiedClassesBaseChange (c ≫ b) A T
    (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
      (unitSection_comp A) h_T q)).
```

No choice of a representative is equated with a different representative.

## Parameter equations

`baseChangeParameterMap_id` identifies the identity-base parameter projection,
after `(Over.mapId S).inv`, with `Over.pullbackId.hom`.

For a map `p : T ⟶ (Over.pullback c).obj ((Over.pullback b).obj P)`,
`baseChangeParameterMate_comp` proves the actual slice-morphism equation

```
h_T ≫ baseChangeParameterMate b (baseChangeParameterMate c p) =
  baseChangeParameterMate (c ≫ b)
    (p ≫ (Over.pullbackComp c b).inv.app P).
```

The proof uses extensionality on slice morphisms and the explicit adjunction
formula for `Over.pullbackComp`. `baseChangeParameterMap_comp` is its
specialization to `p = id`, expressing the composite of the two actual
parameter projections after `h_T` as the direct mate of the inverse slice
comparison.

## Classified dual-scheme equations

These equations retain the named propositions
`PicardZeroPullbackStatement` (stability) and
`PicardZeroUniversalBaseChangeStatement` (universality). They also take
`HasDualScheme` proofs for the actual schemes occurring in each equation.
The duals and Poincare families are the existing chosen universal objects.

Write `D(A)` for `dualScheme A hA` and `β_b` for
`(dualSchemeBaseChangeIso universality b A hA hAb).hom`, and similarly for
other bases. `dualSchemeBaseChangeIso_id` proves

```
β_id = Over.pullbackId.hom.app D(A) ≫
  dualSchemeMap homPicardZeroPullback (baseChangeIdIso A).hom hAid hA.
```

`dualSchemeBaseChangeIso_comp_inv` proves, on the successive base-changed
parameter,

```
(Over.pullback c).map β_b ≫ β_c =
  (Over.pullbackComp c b).inv.app D(A) ≫ β_(c ≫ b) ≫
    dualSchemeMap homPicardZeroPullback (baseChangeCompIso b c A).inv hAc hAd.
```

`dualSchemeBaseChangeIso_comp` gives the equivalent equation on the direct
base-changed parameter:

```
(Over.pullbackComp c b).hom.app D(A) ≫
  (Over.pullback c).map β_b ≫ β_c =
    β_(c ≫ b) ≫
      dualSchemeMap homPicardZeroPullback (baseChangeCompIso b c A).inv hAc hAd.
```

The first two classified equations use injectivity of `dualPointClass`.
The existing classification formulas for dual base change and dual maps reduce
them to the proved class laws and the parameter equations above. The forward
composition equation then follows by composing the inverse-comparison equation
with `Over.pullbackComp.hom` and cancelling the canonical isomorphism.

## Provenance and scope

This is an internal derived prerequisite for varying-base polarized moduli.
Its constructions reuse `FamilyBaseChange`, `HomFamilyPullback`,
`RigidifiedClassPresheaf`, `DualBaseChangeClasses`,
`DualAbelianBaseChangeNaturalityProof` and `AbelianScheme.BaseChangeCoherence`.
It adds no translation of a new literature statement; its provenance is the
explicit comparison of these existing constructions and their universal
classification properties.

The family and class laws hold over arbitrary schemes without flatness or
reducedness assumptions. The dual equations remain conditional on the named
Picard propositions and actual dual existence. This module does not prove
those propositions or existence hypotheses. It does not yet lift these
scheme equations to every choice of dual evaluation data, prove polarized
multiplier coherence, construct Harris PEL representability or scheme levels,
or perform coefficient descent. Those remain separate steps of the host task.
