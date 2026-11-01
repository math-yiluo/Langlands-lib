# Singleton and cohomology coherence for actual geometric pullback

This module proves compatibility of the existing derived geometric
identity/composition comparisons with singleton coefficients. It then
transports the existing derived global-section laws to actual coefficient
sheaves and ordinary small-etale cohomology, and constructs natural
successive pullbacks at both levels.

## Parameters and notation

Let `X`, `Z`, and `V` be schemes in `Scheme.{u}`, let `f : Z ⟶ X` and
`g : V ⟶ Z` be arbitrary scheme morphisms, and let `R : Type u` be a
commutative ring. `ModuleSheaf X R` is the actual category of
`ModuleCat.{u} R`-valued sheaves on `X.smallEtaleTopology`. The chosen
derived categories of sheaves have independent localization morphism
universes `wX`, `wZ`, and `wV`; derived coefficient modules use `wR`.
Singleton identities require only `wX`; the sheaf/cohomology identities
also use `wR`. Composition uses the corresponding three sheaf universes.
There are no etaleness, flatness, finiteness, affineness, or Noetherian
hypotheses on the scheme morphisms or schemes.

Write `L_f = EtaleInverseImage.inverseImage f R` for the constructed exact
geometric inverse image. The ordinary coefficient comparisons are

```text
alpha = (inverseImageId R X).hom : L_id ⟶ Id,
c = (inverseImageComp R f g).hom : L_f ⋙ L_g ⟶ L_(g≫f).
```

Write `D_f` for `EtaleDerivedInverseImage.functor f R` and `D_f+` for
its bounded-below restriction `plusFunctor f R`. These are the actual
localizations of the termwise exact inverse-image functors. Write
`S_X^n` for the actual derived singleton functor in degree `n : ℤ`,
and `S_X^{n,+}` for its bounded-below version. The existing isomorphisms
`singleIso f R n` and `plusSingleIso f R n` identify
`D_f(S_X^n F)` with `S_Z^n(L_f F)`, and similarly in the bounded-below
category. Below, `sigma_f` denotes their hom components at the relevant
sheaf. The derived coefficient identity and composition isomorphisms are
`functorId`, `functorComp`, `plusFunctorId`, and `plusFunctorComp`, all
constructed before this module.

## Compatibility on singletons

`functorId_hom_app_single` proves, for every integer `n` and every actual
coefficient sheaf `F`,

```text
(functorId R X).hom.app (S_X^n.obj F)
  = sigma_id.app F ≫ S_X^n.map (alpha.app F).
```

`plusFunctorId_hom_app_single` proves the same formula in the
bounded-below derived category with `plusSingleIso`, `plusFunctorId`,
and `S_X^{n,+}`.

The unbounded proof expands the existing singleton comparison through the
localization factors and evaluates the derived identity comparison on the
singleton complex. The formula for applying a natural transformation to a
singleton complex and the complex singleton identity comparison reduce the
equation to naturality of `singleMapHomologicalComplex` for the identity
functor. The inverse and hom singleton comparisons cancel. The bounded-below
proof applies the faithful inclusion into the unbounded derived category;
its preimage-isomorphism formulas give the proved unbounded identity.

`functorComp_hom_app_single` proves

```text
(functorComp R f g).hom.app (S_X^n.obj F) ≫ sigma_(g≫f).app F
  = D_g.map (sigma_f.app F) ≫ sigma_g.app (L_f.obj F)
      ≫ S_V^n.map (c.app F).
```

`plusFunctorComp_hom_app_single` proves the corresponding equation with
bounded-below derived objects and `plusSingleIso`. The order is geometric
pullback along `f`, then along `g`, corresponding to `g ≫ f`.

The unbounded proof uses the existing complex-representative formula for
`functorComp`, the actual localization-factor formula for each singleton
comparison, and Mathlib's composition/natural-transformation formulas for
`singleMapHomologicalComplex`. Naturality of the localization factor for
`L_g` at the singleton-complex comparison for `L_f` identifies the remaining
maps. Functoriality, cancellation of isomorphism components, and preservation
of identities finish the equation. A finite local heartbeat limit is used
for checking this proof. The bounded-below proof again uses faithful
inclusion and its preimage-isomorphism formulas.

## Derived sections of coefficient sheaves

Write `RGamma_X = EtaleDerivedSectionsPlus.rightDerivedFunctor X R` and
`RGamma_X^sh = EtaleDerivedSectionsPlus.derivedSections X R`.
Thus `RGamma_X^sh = S_X^{0,+} ⋙ RGamma_X`. Write `P_f^sh` for the existing
`EtaleDerivedGlobalPullback.sheafDerivedPullback f R`. It is the actual
bounded-below derived global-section pullback evaluated on singleton
sheaves, followed by `RGamma_Z` applied to `plusSingleIso f R 0`.

`sheafDerivedPullback_id` proves

```text
P_id^sh.app F ≫ RGamma_X^sh.map (alpha.app F) = identity.
```

The proof combines the two images under `RGamma_X`, replaces their composite
by the bounded-below singleton identity formula, and applies the existing
`derivedPullback_id` at the singleton coefficient.

`compositeSheafDerivedPullback R f g` constructs the natural transformation

```text
RGamma_X^sh ⟶ (L_f ⋙ L_g) ⋙ RGamma_V^sh
```

by composing `P_f^sh`, its left-whiskered successor `P_g^sh`, and the inverse
functor associator. `sheafDerivedPullback_comp` proves its component law

```text
P_f^sh.app F ≫ P_g^sh.app (L_f.obj F) ≫ RGamma_V^sh.map (c.app F)
  = P_(g≫f)^sh.app F.
```

The proof moves the first singleton comparison across the existing derived
pullback by naturality. It combines the coefficient maps under `RGamma_V`,
uses `plusFunctorComp_hom_app_single`, and then applies the existing
`derivedPullback_comp` at the singleton object.
`compositeSheafDerivedPullback_eq` evaluates this law at every sheaf to prove
the natural-transformation equation

```text
compositeSheafDerivedPullback R f g ≫ whiskerRight c RGamma_V^sh
  = P_(g≫f)^sh.
```

## Ordinary cohomology

For `q : ℕ`, write `H_X^q = EtaleDerivedSections.cohomology X R q` and
`P_f^q = EtaleDerivedGlobalPullback.cohomologyPullback f R q`. These are
the existing ordinary small-etale cohomology functors and pullbacks. The
existing `EtaleDerivedSectionsPlus.homologyNatIso X R q` identifies the
homology in degree `q` of `RGamma_X^sh` with `H_X^q`. The pullback `P_f^q`
is the homology of `P_f^sh` transported through those isomorphisms.

`cohomologyPullback_id` proves, for every nonnegative degree and sheaf,

```text
P_id^q.app F ≫ H_X^q.map (alpha.app F) = identity.
```

`compositeCohomologyPullback R f g q` constructs the natural transformation
`H_X^q ⟶ (L_f ⋙ L_g) ⋙ H_V^q` from successive existing pullbacks and the
inverse associator. `cohomologyPullback_comp` proves

```text
P_f^q.app F ≫ P_g^q.app (L_f.obj F) ≫ H_V^q.map (c.app F)
  = P_(g≫f)^q.app F.
```

The proofs expand the existing homology transport, use naturality of the
homology isomorphisms, combine homology images of maps, and apply the
proved sheaf-derived identity/composition laws. Inverse and hom components
of the intervening isomorphisms cancel.
`compositeCohomologyPullback_eq` proves the natural-transformation equality

```text
compositeCohomologyPullback R f g q ≫ whiskerRight c H_V^q
  = P_(g≫f)^q
```

by evaluating the component law at every coefficient sheaf.

## Provenance and scope

This is internal categorical infrastructure. It derives the displayed
compatibilities from the previously constructed geometric inverse images,
their actual complex and derived coefficient comparisons, and the existing
derived global-section laws. It uses the pinned Mathlib implementations in
`Algebra/Homology/Additive.lean` (complex singleton identity, composition,
and natural-transformation formulas),
`Algebra/Homology/DerivedCategory/Basic.lean` (localization of singletons),
`Algebra/Homology/DerivedCategory/ExactFunctor.lean` (derived singleton
comparison and localization factors), and
`Algebra/Homology/DerivedCategory/Plus.lean` (bounded-below singletons).
No desired identity, composition equation, or comparison is an input.

The new laws concern ordinary global sections on the actual small-etale
site, with all integer singleton degrees and all nonnegative ordinary
cohomology degrees. They do not establish full coherence among arbitrary
iterated derived coefficient comparisons, shift compatibility, agreement
with the older etale-restriction construction, coefficient-ring coherence,
compact supports, smooth group actions, or Harris specialization. Those
remain separate obligations of the wider framework.
