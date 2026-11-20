# Zariski separation of ordinary polarized full-level data under rigidity

This module proves the uniqueness half of the Zariski sheaf property of the moduli functor
`moduliFunctor P g d n hd hn`, assuming that polarized automorphisms are trivial. It
introduces no statement and no new hypothesis beyond the rigidity assumption, which appears
as an explicit argument of each separation theorem.

## Rigidity hypothesis

Every separation result below takes the hypothesis

```
hrig : ∀ (T : LevelBase n) (c : Datum P T.obj g d n) (α : PolarizedIso c c),
  α = PolarizedIso.refl c
```

This is the hypothesis of `ModuliZariskiSheafOfRigidityStatement`, and at large level the
conclusion of `PolarizedIso.eq_refl_of_cubicFieldEmbedding`. Here `P : Prerequisites.{0}`.
Covers are families `U : I → S.obj.Opens` with `I : Type` and `iSup U = ⊤`. The restriction
to `U i` is `Datum.pullback` along `(S.openι (U i)).hom = (U i).ι`. This is the restriction
map of `moduliFunctor`.

## Main results

- `Datum.isomorphic_of_isomorphic_restrict hrig U hU a b h`: let `a b` be data over a
  level base `S`. Suppose that for every `i` the restrictions `a.pullback (U i).ι` and
  `b.pullback (U i).ι` are polarized-isomorphic (`Isomorphic`). Then `a` and `b` are
  polarized-isomorphic.
- `Moduli.eq_of_pullback_eq hrig U hU t t' h`: two classes `t t' : Moduli P S.obj g d n`
  with equal restrictions `Moduli.pullback (S.openι (U i)).hom` for every `i` are equal.
- `moduliFunctor_separated hrig hd hn U hU t t' h` is the same statement written with
  `(moduliFunctor P g d n hd hn).map (S.openι (U i)).op`. This is exactly the uniqueness
  part of `LevelBase.IsZariskiSheaf`.

The selected definition is `glueAbelianIso hrig U hU a b e`. It takes local polarized
isomorphisms `e i : PolarizedIso (a.pullback (U i).ι) (b.pullback (U i).ι)` and returns the
glued isomorphism `a.abelian ≅ b.abelian` of abelian schemes over `S`.
`baseChange_glueAbelianIso` states that its base change along each `(U i).ι` is
`(e i).abelianIso.hom`.

## Auxiliary results

- `etaleCoverOfOpens U hU` is Mathlib's open cover `X.openCoverOfIsOpenCover U hU`, viewed
  as a small étale covering family with `Cover.changeProp`. Open immersions are étale.
- `hom_ext_of_opens`: two homomorphisms of abelian schemes over `X` are equal if their base
  changes along every `(U i).ι` are equal. This is the Library's
  `GroupScheme.Descent.EtaleCoverHomDescent.groupHom_ext` applied to the underlying group
  schemes.
- `pullbackTuple_injective_of_opens`: two ordered tuples of torsion sections are equal if
  their pullbacks (`pullbackTuple`) along every `(U i).ι` are equal. The proof compares the
  underlying sections on Mathlib's open cover (`Scheme.Cover.hom_ext`) using
  `pullbackTuple_fst`.
- `grpIso` and `ofGrpIso` convert between isomorphisms of abelian schemes and isomorphisms
  of their underlying group schemes.
- `PolarizedIso.restrict e q` restricts `e : PolarizedIso (a.pullback f) (b.pullback f)`
  along `q`. Its endpoints are the direct pullbacks along `q ≫ f`. It is built from
  `PolarizedIso.pullback` and the comparisons `Datum.pullbackCompIso`.
  `PolarizedIso.groupHom_restrict` identifies its underlying homomorphism with the Library's
  `GroupScheme.Descent.pullHom`. `PolarizedIso.restrict_eval` evaluates it on a test point
  `pullback.lift x z _`, using `GroupScheme.Descent.pullHom_eval`.
- `PolarizedIso.eq_of_rigid`: if every polarized automorphism of `b` is the identity, any two
  polarized isomorphisms `a ≅ b` are equal. Indeed `α.symm.trans β` is the identity, so the
  abelian-scheme isomorphisms agree; the remaining fields are propositions.
- `PolarizedIso.eval_eq_of_rigid` handles base maps `c = c'` that are equal but not
  syntactically equal. Under rigidity, polarized isomorphisms over `c` and over `c'` take the
  same values on test points.
- `levelBaseOfOpenImmersion S f` is the source of an open immersion `f` into `S`, as a level
  base. Local noetherianity comes from `isLocallyNoetherian_of_isOpenImmersion`, and the
  level stays a unit under `f.appTop`.

## Proof of the separation theorem

Choose `e i : PolarizedIso (a.pullback (U i).ι) (b.pullback (U i).ι)`.

1. *Compatibility* (`eval_compatible_of_rigid`, `compatible_of_rigid`). The Library's gluing
   `EtaleCoverHomDescent.iso` needs the following condition. Let
   `x : Z ⟶ pullback a.abelian.X.hom (U i).ι` and
   `y : Z ⟶ pullback a.abelian.X.hom (U j).ι` be test points with
   the same image in `a.abelian`. Then `e i` and `e j` must send `x` and `y` to the same
   point of `b.abelian`. To prove it, let `W = pullback (U i).ι (U j).ι`. The base
   coordinates of `x` and `y` give `m : Z ⟶ W`. Restrict `e i` along `W ⟶ U i` and `e j`
   along `W ⟶ U j`; the two composites `W ⟶ S` agree by `pullback.condition`. `W` is a
   level base (`levelBaseOfOpenImmersion`), so rigidity over it identifies the two restricted
   isomorphisms (`eval_eq_of_rigid`). `restrict_eval` turns this into the required equation.
   The inverse maps are handled by the same lemma for `b, a` and `(e i).symm`.
2. *Gluing* (`glueAbelianIso`). `EtaleCoverHomDescent.iso` over `etaleCoverOfOpens U hU`
   glues the underlying group-scheme isomorphisms of the `e i`. `ofGrpIso` turns the result
   into an isomorphism of abelian schemes. `baseChange_glueAbelianIso` follows from
   `EtaleCoverHomDescent.baseChange_hom`.
3. *Polarization.* Write `Φ` for the glued isomorphism. We check the equation
   `a.polarization = Φ.hom ≫ b.polarization ≫ a.dualWitness.map P b.dualWitness Φ.hom` with
   `hom_ext_of_opens`. Over `U i`, compose both sides with the dual base-change comparison
   `a.dualWitness.baseChangeIso`, which is an isomorphism. The left side becomes
   `(a.pullback (U i).ι).polarization`. On the right, `DualWitness.baseChangeIso_naturality`
   moves the comparison past the dual map, and `baseChange_glueAbelianIso` replaces the base
   change of `Φ` by `e i`. The result is the polarization equation of `e i`.
4. *Level.* `pullbackTuple_map` and `baseChange_glueAbelianIso` show that the pullback of
   `mapTuple Φ.hom a.level.sections` along `(U i).ι` equals the image of
   `pullbackTuple (U i).ι a.level.sections` under `e i`. By the level equation of `e i`,
   this is `pullbackTuple (U i).ι b.level.sections`. `pullbackTuple_injective_of_opens` then
   gives the global level equation.

`Moduli.eq_of_pullback_eq` follows by choosing representatives (`Quotient.inductionOn`,
`Quotient.exact`, `Quotient.sound`). `moduliFunctor_separated` is the same statement,
because the restriction maps of `moduliFunctor` are `Moduli.pullback`.

## Provenance

Internal. Two standard facts underlie the module. Morphisms of schemes glue along an open
cover. Isomorphisms between objects without nontrivial automorphisms are unique, so local
isomorphisms agree on overlaps. The module expresses these facts in the Library's
vocabulary and makes no literature claim. Mumford, Fogarty and Kirwan, *Geometric
Invariant Theory*, 3rd ed. (1994), obtain the fine moduli scheme at large level directly
(Theorem 7.9, printed p.139). The Zariski sheaf property of the represented functor is then
automatic; this module isolates its separation half. The étale-family gluing comes from the
Library's `GroupScheme.Descent.EtaleCoverHomDescent`.
