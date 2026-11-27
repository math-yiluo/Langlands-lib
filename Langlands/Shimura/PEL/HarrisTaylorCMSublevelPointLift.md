# Pointed lifting of pulled normalized CM classes to a smaller level

The setting is the aligned pointed pullback of normalized CM polarized classes,
`classTowerBaseChangeAlong` of the module `HarrisTaylorCMPolarizedAlignedBaseChange`,
for a morphism `b : T ⟶ S` of quasi-separated schemes, structure maps
`p : S ⟶ Spec F` and `q : T ⟶ Spec F` with `hp : b ≫ p = q`, a geometric point `t` of
`T` and its image `t ≫ b` (the square equation is `rfl`), together with the named
prerequisites of that construction (torsion units, roots-of-unity finiteness and
étaleness, Lie naturality on `S`, constrained dual data for pullbacks, pair
additivity).

`numericalClassOf_congr` records that the normalized class
`HarrisNumericalWeilLevel.classOf x hx hn` depends only on the representative `x`,
not on the condition proofs.

`classTowerBaseChangeAlong_exists_sublevel`: let `U' ≤ U` be original Harris levels,
`x` a representative at level `U` over the point `t ≫ b` satisfying the determinant
and numerical conditions, and `eta` a Weil frame of `x.1` at `t ≫ b` whose raw
orbit at the scalar level `(hodgeLevelFunctor D C).obj U` is the level structure
`x.2`. If every element of the image of `π₁(T, t)` under
`fundamentalGroupMap b t (t ≫ b) rfl` fixes the raw orbit of `eta` at the smaller
scalar level `(hodgeLevelFunctor D C).obj U'`, then the aligned pullback of the
class of `x` is the image, under the forgetting transition at
`CompactOpenLevel.inclusion`, of a class at level `U'` over `t`.

Proof. After `subst hp` the aligned pullback is the published
`classTowerBaseChange`, and its value at the class of `x` is the class of
`levelDataBaseChange U x` (`classBaseChange_classOf`, definitional). Write `Y` for
the pulled polarized action, the first component of `levelDataBaseChange U x`, and
`frameBC` for the published comparison `weilAdelicFrameBaseChange` of frames of `Y`
at `t` with frames of `x.1` at `t ≫ b`. The raw orbit
`q' = (weilAdelicFrameRightOrbitBaseChange U').symm (mk U' eta)` is fixed by
`π₁(T, t)`: applying the orbit comparison and `RightOrbit.map_smul` with the
published equivariance `weilAdelicFrameBaseChange_monodromy`, the translate of `q'`
by `σ` maps to `fundamentalGroupMap … σ • mk U' eta`, which is `mk U' eta` by
hypothesis. So `⟨Y, q'⟩` is a representative at level `U'`; it satisfies the
determinant and numerical conditions of the pulled representative
(`levelDataBaseChange_objectCondition`,
`HarrisNumericalWeilLevel.levelDataBaseChange_numericalObjectCondition`), and its
class is the required `z`. Its image under the forgetting transition is the class
of `mapRepresentative (inclusion) ⟨Y, q'⟩`; this representative equals
`levelDataBaseChange U x`. The first components agree definitionally; for the level
structures, the transition translates by the element
`scalarEquiv 1` (`hodgeLevelFunctor_map_element`), the pulled orbit of `x.2` is
`(weilAdelicFrameRightOrbitBaseChange U).symm (mk U eta)` by `heta`, and both sides
are the raw `U`-orbit of `frameBC.symm eta` by `RightOrbit.translate_mk`, `map_one`
and `right_one`. `numericalClassOf_congr` concludes.

Provenance: internal. The lemma combines the published pullback of normalized
classes (`classTowerBaseChange`, `levelDataBaseChange`) with the published pointed
frame base change and its monodromy equivariance; it is the pointed form of the
observation that the image of `π₁(T, t)` determines which finer level structures
descend over `T`.
