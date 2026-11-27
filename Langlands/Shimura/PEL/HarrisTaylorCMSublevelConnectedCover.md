# Étale-local sublevel lifting of unpointed normalized CM classes on connected bases

## Scheme-theoretic lemmas

* `Langlands.AlgebraicGeometry.surjective_componentι_comp_cover`: for a finite étale
  cover `Y` of a connected scheme `S` with `Y` locally Noetherian, the inclusion of
  any connected component of `Y` followed by the covering map is surjective. The
  component is open (locally Noetherian components, `componentOpen`) and closed
  (`isClosed_connectedComponent`); its image is closed because finite morphisms are
  universally closed (`Scheme.Hom.isClosedMap`) and open because étale morphisms are
  flat and locally of finite presentation, hence universally open
  (`Scheme.Hom.isOpenMap`). A nonempty clopen subset of the connected `S` is all of
  `S`.
* `Langlands.AlgebraicGeometry.range_subset_range_componentι`: a geometric point
  `y : Spec Ω ⟶ X` of a locally Noetherian scheme lands in the component of the image
  of the unique point of `Spec Ω`, so it lifts through that component's inclusion.
* `HarrisGeometricPoint.ofHom a k` is the geometric point with the field of `a` and
  morphism `k`; `ofHom_self` records `a.ofHom a.hom = a`.

## Testing at one point

`unpointedClassTowerPullback_exists_sublevel_of_point`: let `f : T ⟶ S` be a
morphism of connected admissible CM bases (`AdmissibleCMBaseCategory`), `v` an
unpointed class at level `U` on `S` (an element of `unpointedClassTower`), `t` a
geometric point of `T` and `s'` a morphism from the spectrum of the field of `t` to
`S` with `t.hom ≫ f.hom.left = s'`. Suppose that at the geometric point
`t.ofHom s'` the class `v` is the normalized class of a representative `x`, that
`eta` is a frame in the level orbit of `x`, and that the image of `π₁(T, t)` under
`fundamentalGroupMap f.hom.left` fixes the raw orbit of `eta` at the smaller level
`U'`. Then `(unpointedClassTower T).map (inclusion) w = (unpointedClassTowerPullback
f).app U v` for some unpointed class `w` at level `U'` on `T`.

Proof. Substituting `s' = t.hom ≫ f.hom.left`, the point `t.ofHom s'` is the pushed
point `t.comp f.hom.left`. The value at `t` of the unpointed pullback is the aligned
pointed pullback (`geometricFamilyPointPullback`) of `v` at the pushed point, so
`classTowerBaseChangeAlong_exists_sublevel` of the module
`HarrisTaylorCMSublevelPointLift` provides a pointed class `z` at level `U'` over `t`
whose image is that value. Take `w` the compatible family extending `z`
(`geometricFamilyExtension`). Families agree when their values at `t` agree
(`geometricFamilyEvaluationEquiv` is a bijection); the value of the image of `w` at
`t` is the image of `z`, because the canonical comparison at `t` with itself is the
identity (`geometricClassComparison_refl`).

## The connected theorem

`unpointedClassTower_exists_sublevel_etaleCover`: for every connected admissible
CM base `S`, original Harris levels `U' ≤ U` and unpointed class `v` at level `U` on
`S`, there are a connected admissible CM base `T`, a morphism `f : T ⟶ S` whose
underlying scheme morphism is étale and surjective, and an unpointed class `w` at
level `U'` on `T` with `(unpointedClassTower T).map (inclusion) w =
(unpointedClassTowerPullback f).app U v`.

Proof. Take the geometric point `s0 = HarrisGeometricPoint.ofResidue` at a point of
`S` (nonempty, being connected). By `classOf_surjective` the value of `v` at `s0` is
the class of a representative `x`; choose a frame `eta` in its level orbit, whose raw
orbit at `(hodgeLevelFunctor D C).obj U` is then fixed by `π₁(S, s0)`. With the
rational PEL conditions `hodgeRationalPELConditions`, simplicity of `A` and
finiteness of `A` over `ℚ`, the module `WeilFrameLevelCovers` gives the finite étale
cover `Y` of `S` whose fibre over `s0` is the monodromy orbit of the raw orbit of
`eta` at `(hodgeLevelFunctor D C).obj U'`, with the lift `y0` of that raw orbit. `Y` is
locally Noetherian (`LocallyOfFiniteType.isLocallyNoetherian`). Let `c0` be the
connected component of `Y` containing the image of `y0` and `T` the component scheme
over `Spec F`; it is admissible by `componentwiseAdmissibleCMBase_of_relativeDual`
with the published `relativeDualSchemeExistence` and `relativeDualSchemeGeometry`.
The morphism `f` is the component inclusion followed by the covering map: étale as a
composite of an open immersion and an étale map, surjective by
`surjective_componentι_comp_cover`. The lift `y0` factors through the component
(`range_subset_range_componentι`, `IsOpenImmersion.lift`), giving a geometric point
`t` of `T` with `t.hom ≫ f.hom.left = s0.hom`. By `fundamentalGroupMap_smul_eq_of_factor`
the image of `π₁(T, t)` fixes `y0`, hence, by `weilAdelicFrameOrbitCoverPoint_smul_eq`,
the raw orbit of `eta` at the smaller level. The point lemma above, at `s' = s0.hom`
(for which `t.ofHom s'` is `s0`), produces `w`.

Provenance: internal. The construction follows the informal route of Harris and
Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties* (2001), III.1,
p. 91 (Library source `harris-taylor-2001-geometry-cohomology-simple-shimura`), for
the finite étale transition maps between levels: on a connected
base with a geometric point a level structure is a monodromy-invariant orbit of
frames, and the finer orbits inside it form a finite continuous monodromy set,
realized by a finite étale cover over which the class acquires a finer level
structure. The Lean proof uses only the component of the cover through the
distinguished lift.
