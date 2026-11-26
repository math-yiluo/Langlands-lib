# The universal CM class and its representatives on connected components

## Source

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp. 90–91 (one-based PDF pp. 98–99),
defines \(X_U(S)\) for a locally Noetherian \(F\)-scheme \(S\) as the
product of \(X_U(S_i)\) over the connected components \(S_i\) of \(S\).
For a connected \(S\) with a geometric point \(s\), \(X_U(S,s)\) is the
set of equivalence classes of quadruples \((A,\lambda,i,\bar\eta)\): an
abelian scheme of dimension \(dn^2\), a polarisation, a compatible
action of \(B\) satisfying the Rosati condition, and a
\(\pi_1(S,s)\)-invariant \(U\)-orbit of isomorphisms of level structure.
Two quadruples are equivalent if an isogeny carries the first action
and orbit to the second and the first polarisation to a \(\mathbb
Q^\times\)-multiple of the second. Page 91 states that for sufficiently
small \(U\) the functor is represented by a smooth projective scheme
\(X_U/F\). III.2, printed p. 98 (PDF p. 106), uses the universal abelian
variety \(\pi : A \to X_U\). The book is registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Because the moduli problem is taken up to rational polarized isogeny,
a representing scheme carries a universal *class*, not a universal
abelian scheme. This module extracts that class from the Library's
exact representing evidence, chooses actual representatives on the
connected components of the represented level, and proves how the
representatives and their classes behave under pullback and under the
level maps. It assumes representing evidence and proves no
representability.

## Inputs

The setting is that of `Langlands.Shimura.PEL.HarrisTaylorCMSchemeLevels`:
the central simple data `D`, the signature charts `C`, the named tensor,
Picard, duality, polarization and Weil prerequisites, and the moduli
presheaf `smallLevelClassPresheafTower`, the transpose of
`disconnectedClassTowerPresheaf` restricted to sufficiently small
levels. A `CMLevelRepresentation U` consists of a componentwise
admissible CM base `rep.base`, smoothness and an actual projective
embedding of its structure map, and a natural isomorphism
`rep.represents` from its lifted Yoneda functor to the moduli presheaf
at `U`. The level `U` of `cmSchemeTower q` is the representing scheme of
`chosenCMLevelRepresentation q U`.

## Pointwise pullback of a representative

`geometricFamilyPointPullback_classOf` concerns a morphism `b : T ⟶ S`
of quasi-separated schemes satisfying the unit and roots-of-unity
hypotheses of the existing pullback, structure maps `p`, `q` to
`Spec F` with `b ≫ p = q`, and a geometric point `a` of `T`. The existing pointed pullback
`geometricFamilyPointPullback` at `a` sends the class `classOf x hx hn`
of an actual representative `x` at the point `a.comp b` to the class
of `levelDataBaseChange … x`. This is the actual base change of the
polarized abelian scheme with its action and of its level orbit, using
the given dual data. The determinant and numerical conditions of the
base change are supplied by the existing
`levelDataBaseChange_objectCondition` and
`levelDataBaseChange_numericalObjectCondition`. After substituting
`q = b ≫ p` the equation holds by definition.

## The universal class and its pullback law

`cmUniversalClass rep` is `uliftYonedaEquiv rep.represents.hom`, the
value of the representing isomorphism at the lifted identity of
`rep.base` (`cmUniversalClass_eq`). It is an element of the moduli
presheaf at `rep.base`, that is a function assigning to each connected
component `c` of the level a class in the unpointed tower
`unpointedClassTower` of the component `componentCMBase rep.base c`.

`cmUniversalClass_pullback` is the Yoneda formula: for every actual
morphism `a : S ⟶ rep.base` of componentwise admissible bases, the
moduli pullback of the universal class along `a` is
`rep.represents.hom.app (op S) (ULift.up a)`.
`cmUniversalClass_pullback_presheaf` states the same with
`disconnectedClassTowerPresheaf`. `cmUniversalClass_pullback_component`
evaluates it on a component `c` of `S`: for any component `d` of the
level and any proof that `a` maps `c` into `d`, the value is the
existing `unpointedClassTowerPullback` of the universal class on `d`
along `componentCMBaseHomTo a c d e`, the restriction of `a` to these
components.

## Representatives

`cmUniversalComponentClass rep c a` is the universal class on the
component `c` evaluated at a geometric point `a` of that component by
`unpointedClassTowerEvaluationIso`; it lies in the existing pointed
normalized tower, whose values are `HarrisNumericalWeilLevel.IsoClass`.
That class satisfies `HarrisNumericalWeilLevel.ClassCondition`: it is
the class of an actual representative with the determinant and
numerical conditions. `cmUniversalComponentModel` chooses one by
`Classical.indefiniteDescription`, and
`cmUniversalComponentRepresentative rep c a` is the chosen element of
`HarrisLevelData` at `U`. Its first component is a positive polarized
abelian scheme with its action of `A` (the PEL and polarization data);
its second is its level orbit at the point `a`.
`cmUniversalComponentRepresentative_good` and
`cmUniversalComponentRepresentative_numerical` record the determinant
condition and the dimension and central trace conditions.

`cmUniversalComponentRepresentative_classOf` proves that the class of
the representative is the pointed universal class.
`cmUniversalComponentRepresentative_classOf_iff` describes the
equivalence relation: another satisfying representative `y` has the
same class exactly when there are `q : ℚˣ`, an isomorphism of
abelian schemes with action up to isogeny from the chosen
representative to `y` that carries the polarization to the
`q`-multiple in the sense of `PolarizedWeilLevel.Multiple`, and whose
transport `PolarizedWeilLevel.levelIso` carries the chosen level orbit
to that of `y`. This is the existing `classOf_eq_iff`, so the selection
changes no relation.

`cmUniversalClass_component_eq` recovers the universal class on each
component from the representative at any geometric point, as the
inverse evaluation of its class.

`cmUniversalComponentPoint rep c` is a geometric point of the component
`c` obtained from the algebraic closure of the residue field at a point
(each component is nonempty). `cmUniversalRepresentative rep c` is the
representative at this point, and `cmUniversalAbelianFamily rep c` is
its underlying abelian scheme over the component `c`
(`cmUniversalAbelianFamily_eq`). The family is thus a componentwise
assembly: an abelian scheme over each connected component of the
represented level, whose class with its polarization, action and level
recovers the universal class on that component.

## Compatibility under pullback

`cmUniversalClass_pullback_representative` writes the pulled-back
universal class on a component `c` of `S` as the pullback along the
restricted component map of the inverse evaluation of the class of the
representative over the image component `d`.
`cmUniversalClass_pullback_baseChange` evaluates it at an arbitrary
geometric point `t` of the component `c`. For every fibre-functor path
from the chosen point of `d` to the image of `t`, the value is the class
of the actual base change, along the restricted component map, of the
chosen representative over `d` with its level orbit moved along the
path by `HarrisTaylorLieWeilLevel.pointMapRepresentative`. Moving the
orbit keeps the same polarized abelian scheme with action. The proof
uses `classGeometricPointTowerIso_eq_path`, by which the canonical
point comparison equals the transport along any path, and
`geometricFamilyPointPullback_classOf`. Thus the representatives are
compatible with pullback at the level of their rational polarized
isogeny classes with level structure.

## Compatibility along the level maps

For a pointwise family `R` of representations,
`cmUniversalClass_transition` proves that pulling back the universal
class of `R V` along the actual transition
`(representedCMBaseTower R).map k` gives the image of the universal
class of `R U` under the moduli map of `k`. The proof applies the
pullback law and `representedCMBaseTower_map_classes` at the identity.
`cmUniversalClass_transition_component` is the same statement on a
component `c` of the source level with image component `d`.

`cmUniversalRepresentative_transition` combines these: at every
geometric point `t` of the component `c`, the class of the actual base
change of the representative over `d` (with its orbit moved along any
path, as above) equals the class of
`HarrisNumericalWeilLevel.mapRepresentative k` applied to the
representative of `R U` over `c` at `t`. The latter is the same
polarized abelian scheme with action, with its level orbit pushed along
the original level arrow. By `cmUniversalComponentRepresentative_classOf_iff`
and `classOf_eq_iff`, the two representatives are therefore related by
a rational polarized isogeny respecting the level structures.

## The chosen representations

For a proof `q` of `CMRepresentabilityStatement`, `cmSchemeTower_obj`
and `cmSchemeTower_map` identify the levels and transitions of
`cmSchemeTower q` with the representing schemes and the underlying
scheme maps of `representedCMBaseTower` for
`chosenCMLevelRepresentation q`. `cmSchemeTowerUniversalClass q U` and
`cmSchemeTowerAbelianFamily q U` are the universal class and the
abelian family at these levels; all results above apply to them, and
the transition results apply with `R = chosenCMLevelRepresentation q`.

The relative powers of the family and their maps are in
[HarrisTaylorCMUniversalPowers](HarrisTaylorCMUniversalPowers.md).
