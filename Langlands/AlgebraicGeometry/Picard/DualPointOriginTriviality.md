# Recognizing the origin of a chosen dual by triviality of the Poincaré pullback

This helper module proves that a point of a chosen dual scheme whose Poincaré
pullback is trivial is the origin. The point may be a `T`-point, a base point, or
a point given by any fibre product of the Poincaré projection. All declarations
are in namespace `Langlands.AbelianScheme`. The Lean code is Worker 1165's
`section Origin` of their draft support module for the parent task
`32297f48-3cfc-421a-978e-b84e073ffacc`, moved here unchanged so that both proofs
can import it. It imports `Picard/DualKernelPullback`, `Picard/RigidifiedCarrierIso`,
`Picard/PicardZeroPullbackProof` and `Modules/PullbackTensorProof`.

## Statements

`S` is an arbitrary scheme, `A` an abelian scheme over `S`, and
`hA : HasDualScheme A` a chosen dual `D := dualScheme A hA` with its rigidified
Poincaré family `poincareFamily A hA` and origin `dualOrigin A hA`. For
`T : Over S`, a `T`-point of `D` is an over-morphism `p : T ⟶ D`. The origin over
`T` is `(Over.homMk T.hom : T ⟶ Over.mk (𝟙 S)) ≫ dualOrigin A hA`. A base point
of `D` is the case `T = Over.mk (𝟙 S)`, that is, a section of `D → S`.

- `dualPoint_eq_origin_of_forget_iso' A hA p e`: for a `T`-point `p`, if the
  underlying line bundle of the parameter pullback `dualPointFamily A hA p` is
  isomorphic to the trivial line bundle on `(relativeSpace A.X.hom).obj T`, then
  `p` is the origin over `T`.
- `dualPoint_eq_origin_of_forget_iso A hA p e`: the base-point case, with
  conclusion `p = dualOrigin A hA`.
- `dualPointFibreComparison A hA p`: for a `T`-point `p`, the canonical morphism
  from `(relativeSpace A.X.hom).obj T` (which is `pullback T.hom A.X.hom`) to the
  fibre `pullback (pullback.snd A.X.hom D.hom) p.left` of the Poincaré projection
  over `p.left`. Its components are the pullback lift
  `(pullback.snd T.hom A.X.hom, pullback.fst T.hom A.X.hom ≫ p.left)` into
  `A ×_S D` and `pullback.fst T.hom A.X.hom` to `T.left`.
- `dualPointFibreComparison_comp A hA p`: composing it with the first projection
  of the fibre and the symmetry `A ×_S D ≅ D ×_S A` gives
  `(relativeSpace A.X.hom).map p`.
- `dualPoint_eq_origin_of_fibre_iso' A hA p e`: for a `T`-point `p`, if the
  restriction
  `fibreLineBundle ((baseChange D.hom).obj A) (poincareLineBundle A hA) p.left`
  of the actual Poincaré line bundle to the fibre over `p.left` is isomorphic to
  the trivial line bundle, then `p` is the origin over `T`.
- `dualPoint_eq_origin_of_fibre_iso A hA p e`: the base-point case, with
  conclusion `p = dualOrigin A hA`.
- `dualPoint_eq_origin_of_isPullback A hA t q f h e`: let `t : T ⟶ D`, and let
  `h` say that `X` with `q : X ⟶ (A ×_S D)` and `f : X ⟶ T.left` is a pullback
  of the Poincaré projection `((baseChange D.hom).obj A).X.hom` along `t.left`.
  If `e : q^* (poincareLineBundle A hA).obj ≅ SheafOfModules.unit X.ringCatSheaf`,
  then `t` is the origin over `T`.

## Implemented proof

`dualPoint_eq_origin_of_forget_iso'`. The unit section of the relative space over
`T` has the projection as retraction (`relativeSection_projection`). Hence the
published `RigidifiedLineBundle.nonempty_iso_of_forget_iso`, with the published
`pullbackTensorComparisonIsIso`, upgrades the line-bundle isomorphism `e` to an
isomorphism of rigidified line bundles between `dualPointFamily A hA p` and the
relative trivial family over `T`. So the class
`dualPointClass picardZeroPullback A hA p` equals the class of the origin over `T`
(`dualPointClass_origin`), and `dualPointClass_injective` gives the equality of
points.

`dualPoint_eq_origin_of_forget_iso` and `dualPoint_eq_origin_of_fibre_iso` apply
the primed versions with `T = Over.mk (𝟙 S)` and rewrite `Over.homMk (𝟙 S)` to
the identity, checked with `Over.OverMorphism.ext`.

`dualPointFibreComparison_comp` is checked componentwise with `pullback.hom_ext`
and the lift equations.

`dualPoint_eq_origin_of_fibre_iso'`. Let `ψ` be the comparison map and `b` the
composite of the first fibre projection with the symmetry, so that
`(relativeSpace A.X.hom).map p = ψ ≫ b`. The underlying line bundle of
`dualPointFamily A hA p` is the pullback of the Poincaré carrier along
`(relativeSpace A.X.hom).map p`. The proof rewrites along this equation, splits
the pullback along `ψ ≫ b` with `LineBundle.pullbackComp`, and recognizes the
pullback along `b` as `fibreLineBundle` (again by `LineBundle.pullbackComp`).
This turns it into the `ψ`-pullback of the fibre bundle. By `e` this is the
`ψ`-pullback of the trivial bundle, which is trivial
(`LineBundle.pullbackTrivialIso`). The forget-iso theorem concludes. No
isomorphism of schemes between the relative space and the fibre is needed.

`dualPoint_eq_origin_of_isPullback`. Let `i := h.isoPullback`, so `i.inv ≫ q` is
the first projection of the chosen pullback (`IsPullback.isoPullback_inv_fst`).
The fibre bundle of the previous theorem is the pullback of `P` along that
projection. `Scheme.Modules.pullbackCongr` and `Scheme.Modules.pullbackComp`
identify it with `i.inv^* q^* P`. By `e` this is `i.inv^*` of the unit, and
`Langlands.Scheme.Modules.pullbackUnitIso` identifies that with the unit.
`ObjectProperty.isoMk` lifts this isomorphism of sheaves to line bundles, and
`dualPoint_eq_origin_of_fibre_iso'` concludes.

## Provenance and scope

These are the standard consequences of the universal property of the chosen
Poincaré family: a `T`-point of the dual is the origin over `T` when its
pulled-back Poincaré bundle is trivial. Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, use this in (9.5), printed p.128 (PDF p.132), where the
universal property of `P` makes `i(a)` factor through the origin. The theorems
prove only this direction. The converse, that the origin has trivial pullback, is
`dualPointClass_origin` in the published Library.
