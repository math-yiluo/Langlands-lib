# The geometry of the intersection of two rational parabolics

Authors: Worker 59, Worker 49 and Worker 3976. The integrated module keeps
Worker 59's more general Borel-pair helpers and one proof of the common exact
geometry target. Worker 49's common-torus helper and Worker 3976's
`IsParabolicSubgroup.isCommonTorusParabolicPair_baseChange_toAlgebraicClosure`
have the same conclusion as `isCommonTorusParabolicPair_baseChange hG j j' hj hj'`
here; their duplicate declarations are consolidated into that helper.

Module `Langlands.GroupScheme.Absolute.ParabolicIntersectionGeometryProof` proves
the published proposition
`Langlands.GroupScheme.ParabolicIntersectionGeometryStatement.{u}` (Worker 1349)
without any remaining hypothesis. It is a helper module for the proof of
`Langlands.GroupScheme.ParabolicIntersectionTorusStatement.{u}` in
`Langlands.GroupScheme.Absolute.ParabolicIntersectionTorusProof`. Every step is
an internal deduction from results already proved in the Library, listed below.

## Declarations

`exists_range_eq_dynamicParabolic_of_isBorelPair` works over an algebraically
closed field `k : Type u`. It takes a connected reductive `G`, a split torus `T`
with `j : T.toGrp ⟶ G`, a smooth closed subgroup `i : P ⟶ G`, and an actual map
`b : B ⟶ P` with `IsBorelPair (b ≫ i) j`. It produces an integral cocharacter
`ζ : cocharacterLattice T` with

`SubgroupFunctor.range i = Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ j)`,

an equality of subgroup functors on every test scheme. The published
`absoluteBorelOvergroupCocharacter` (Workers 146, 1272 and 1240) states only the
field-point consequence. Its proof, however, goes through this functor-level
equality, and this lemma repeats that proof without the final evaluation at
field points. It applies
`AbsoluteBorelOvergroup.exists_regularCocharacter_support_and_inverters` to get a
regular cocharacter `ν` whose positive roots lie in the tangent root support
`S` of `range i`, together with support-preserving Weyl inverters. Then
`AbsoluteBorelOvergroup.exists_cocharacter_of_rootSupport_negators` averages `ν`
to a `ζ` with `α ∈ S ↔ 0 ≤ ⟨α, ζ⟩` for every actual root `α`. Finally
`borelOvergroup_eq_dynamicParabolic_of_rootSupport` turns this equivalence into
the stated equality.

`isCommonTorusParabolicPair_of_borel` works over an algebraically closed field
`K`. It takes a connected reductive `G`, smooth closed subgroups `j : P ⟶ G` and
`j' : P' ⟶ G`, and maps `f : B ⟶ P`, `f' : B' ⟶ P'` such that `f ≫ j` and
`f' ≫ j'` are Borel subgroups. It proves `IsCommonTorusParabolicPair j j'`
(the predicate of Worker 1240's module `ParabolicIntersectionCommonTorus`).
`twoBorelCommonMaximalTorus` supplies one maximal torus `t : T.toGrp ⟶ G` with
factorizations `g ≫ (f ≫ j) = t` and `g' ≫ (f' ≫ j') = t`. Since `K` is
algebraically closed, `T` is split by
`IsTorus.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting`.
Then `(f ≫ j, t)` and `(f' ≫ j', t)` are Borel pairs, witnessed by `g` and `g'`.
The previous lemma, applied once to each, gives the two cocharacters `ν`, `ν'`
of the same torus `T`.

`isCommonTorusParabolicPair_baseChange` works over any field `k`. For a connected
reductive `G` and parabolic subgroups `j`, `j'` (published
`IsParabolicSubgroup`), it proves that the base changes `bc.map j` and
`bc.map j'` to `AlgebraicClosure k` form a common-torus parabolic pair. Here
`bc = GroupScheme.baseChange (toAlgebraicClosure k)`.
`IsConnectedReductive.baseChange_of_algebraicExtension` makes `bc.obj G`
connected reductive. Smoothness of `bc.obj P` and `bc.obj P'` is smoothness of
a pullback of a smooth morphism. `IsClosedSubgroup.baseChange` keeps the
inclusions closed. The field `exists_isBorelSubgroup` of `IsParabolicSubgroup`
is exactly a Borel subgroup of `bc.obj G` factoring through `bc.map j`, and
likewise for `j'`. The previous lemma then applies.

`parabolicIntersectionGeometry : ParabolicIntersectionGeometryStatement.{u}`
applies the published conditional reduction
`parabolicIntersectionGeometry_of_commonTorus` (Worker 1240). It supplies the
two hypotheses that reduction needs: the Library proof `dynamicConnected` of
`DynamicConnectedStatement`, and the previous lemma as the common-torus input.
The conclusion is the published statement. The actual pullback
`pullback j j'` is smooth over `k`, its base change to `AlgebraicClosure k` is
connected, and that base change has a maximal torus of the ambient base-changed
group factoring through it.

## Scope and route

There are no restrictions on the field: it may have any characteristic and need
not be perfect. The universe `u` is the universe of the statement. No splitness,
minimality or nonemptiness assumption is added. The route differs from
Worker 1240's sketch of `hTorus`, which goes through
`SplitParabolicCocharacterStatement`. Instead it uses the Borel overgroup
recognition above. This needs only a Borel pair inside each parabolic, which is
exactly the data from `twoBorelCommonMaximalTorus`. The proof uses neither
`ParabolicDynamicStatement` nor `SplitParabolicCocharacterStatement`.
`set_option backward.isDefEq.respectTransparency false` matches the setting of
`BorelOvergroupCocharacterProof`, whose proof the first lemma repeats.

Classical sources for the assembled facts: Borel–Tits, *Groupes réductifs*
(1965), §2.4 (two Borel subgroups contain a common maximal torus) and
Corollary 4.5 (connectedness of `P ∩ P'`). This module does not follow their
proof of 4.5. Connectedness and smoothness come from the dynamic description in
the cited reduction.
