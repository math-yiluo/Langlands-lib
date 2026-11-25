# Germ cohomology through neighbourhood cohomology

This module is a derived helper. Its definitions and proofs are
internal. They use the published analytic étale site, the ordinary direct image
`etaleUnderlyingSheaf`, the ordinary site points `underlyingTopologyPoint` and the
germ cohomology `etaleUnderlyingGermCohomology` from
`Langlands.Sheaf.Equivariant.AnalyticOpenEtaleGerms`, together with the section
cohomology `sectionsDerived` from `Langlands.Sheaf.Equivariant.TwistedGlobalSections`.

The classical fact behind it is Milne, *Étale Cohomology* (Princeton, 1980),
Chapter III, Proposition 1.13, printed p. 88 (source `milne-1980-etale-cohomology`).
It says that `R^i π_* F` is the sheaf associated with the presheaf
`U ↦ H^i(U ×_X X', F)`. Taking stalks, the stalk at `y` is therefore the filtered
colimit of `H^i` over the neighbourhoods of `y`. This module does not formalize
Milne's proposition. It proves directly the elementwise consequence that is
needed: degree-`q` germ cohomology vanishes if and only if every degree-`q` class
over a neighbourhood dies over a smaller neighbourhood. Like Milne's proof, the
Lean proof uses an injective resolution and the exactness of the fibre functor.

## Homology of complexes of modules (`Langlands.Cohomology.PointGerms`)

These lemmas hold for a homological complex `L` of `ModuleCat.{w} R` over a ring
`R` and an arbitrary complex shape `c`.

- `homologyπ_apply_eq_zero_iff`: the homology class of a cycle `y` in degree `n`
  is zero exactly when `L.iCycles n y` is the image of an element of
  `L.X (c.prev n)` under the differential.
- `homologyMap_homologyπ_apply_eq_zero_iff`: for a morphism of complexes
  `φ : L ⟶ L'`, the class of `y` is sent to zero by `homologyMap φ n` exactly
  when `φ.f n (L.iCycles n y)` is a boundary in `L'`.
- `exists_iCycles_eq`: every element of `L.X n` killed by the outgoing
  differential is `L.iCycles n` of some cycle.
- `d_iCycles_apply`: a cycle is killed by the outgoing differential.

Each lemma is proved through Mathlib's identification of short-complex cycles and
homology in `ModuleCat` with the kernel and its quotient by the image.

## Germ complexes at a site point (`Langlands.Cohomology.PointGerms`)

Let `C` be a category with a Grothendieck topology `J`, let `Φ : J.Point.{w}` be
a point, and let `K` be a homological complex of presheaves `Cᵒᵖ ⥤ ModuleCat.{w} R`.

- `sectionsComplex K X` is the complex of sections over `X`.
  `sectionsComplexMap K f` is restriction along `f : Y ⟶ X`.
- `germComplex Φ K` is the complex obtained by applying the presheaf fibre
  `Φ.presheafFiber` degreewise.
- `toPresheafFiber_eq_of_hom`: if `f : Y ⟶ X` carries a fibre element `y` to
  `x`, then the germ of `p` at `x` equals the germ of `P.map f.op p` at `y`.
- `app_map_apply` is the elementwise naturality of a morphism of presheaves of
  modules.

These two theorems assume `LocallySmall.{w} C`:

- `germComplex_exactAt_iff`: the germ complex is exact in degree `n` if and only
  if the following holds for every object `X`, every `x : Φ.fiber.obj X` and every
  `z` in degree `n` over `X` with `d z = 0`. There must be an arrow `f : Y ⟶ X`,
  an element `y : Φ.fiber.obj Y` mapped to `x`, and an element `w` in degree
  `c.prev n` over `Y` with `d w = z|_Y`. The proof represents germs by sections,
  using joint surjectivity of `Φ.toPresheafFiber`. It refines two
  neighbourhoods to a common one by cofilteredness of the category of elements of
  `Φ.fiber`, and it turns equality of germs into equality after restriction with
  `toPresheafFiber_eq_iff'`.
- `germComplex_exactAt_iff_homology`: the same condition, stated with classes.
  The germ complex is exact in degree `n` if and only if, for every `X`, every
  `x : Φ.fiber.obj X` and every class `a` in degree `n` of `sectionsComplex K X`,
  there are `f : Y ⟶ X` and `y` mapped to `x` such that
  `homologyMap (sectionsComplexMap K f) n a = 0`. The proof goes through
  surjectivity of `homologyπ` and the lemmas of the previous section.

## Restriction of section cohomology (`Langlands.Sheaf.Equivariant.TwistedOver`)

- `sheafSectionsRestriction J R f`, for `f : V ⟶ U` in `C`, is the natural
  transformation `sheafSectionsModule J R U ⟶ sheafSectionsModule J R V` given by
  restricting sections of the underlying presheaf along `f`.
- `sectionsDerivedMap J R f q`, under `HasSheafify` and `EnoughInjectives`, is
  the right derived natural transformation
  `sectionsDerived J R U q ⟶ sectionsDerived J R V q` of
  `sheafSectionsRestriction J R f`. It is the restriction map on cohomology over
  objects.

## The analytic criterion (`Langlands.Sheaf.Equivariant.Analytic`)

`isZero_etaleUnderlyingGermCohomology_iff`: let `X` be an object of the
localized category `LocalizedCategory` of saturated atlas presentations over a
complete non-archimedean field `K`. Let `y` be an ordinary point, `q`
a degree, and `F` an étale sheaf of `ModuleCat.{max u (v + 1) uL} R`-modules. Then
`(etaleUnderlyingGermCohomology X R y q).obj F` is zero if and only if the
following holds for every ordinary open `U` containing `y` and every class `a` in
`(sectionsDerived (etaleTopology X) R (openEtaleObject X U) q).obj F`: there is an
open `V ≤ U` containing `y` such that
`(sectionsDerivedMap (etaleTopology X) R (openEtaleMap X (homOfLE h)) q).app F a = 0`.

Proof. Fix the injective resolution `I = injectiveResolution F`. Let `L` be the
complex of presheaves underlying `etaleUnderlyingSheaf` applied to `I`. Then:

1. `I.isoRightDerivedObj` applied to the composite of `etaleUnderlyingSheaf` with
   the fibre at `y` shows that the germ cohomology is zero if and only if
   `germComplex Φ L` is exact in degree `q`. Here `Φ = underlyingTopologyPoint X y`.
2. `I.isoRightDerivedObj` applied to sections over `openEtaleObject X U` gives an
   isomorphism `hsec U` from section cohomology over `U` to the degree-`q`
   homology of `sectionsComplex L U`.
3. `InjectiveResolution.rightDerived_app_eq` identifies `sectionsDerivedMap` along
   `openEtaleMap X f` with `homologyMap (sectionsComplexMap L f) q`, conjugated by
   these isomorphisms.
4. `germComplex_exactAt_iff_homology` for `Φ` finishes the proof. The fibre
   of `Φ` over an open `U` is `ULift (PLift (y ∈ U))`, and the arrows between
   opens are inclusions.

## Scope

All results are statements about sheaf and derived-functor cohomology. The
criterion compares germ cohomology only with cohomology over ordinary open
neighbourhoods. It makes no claim about Galois neighbourhoods, finite étale
coverings, or group cohomology. It also asserts no vanishing of any specific
germ cohomology.
