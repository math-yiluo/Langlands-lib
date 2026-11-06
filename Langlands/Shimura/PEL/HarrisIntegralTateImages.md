# Integral Tate images from normalized Harris Weil frames

## Provenance and purpose

This is an internal construction from the published Harris integral pairing,
actual Weil frames, opposite right orbits and rational-isogeny transport. It
introduces a concrete source integral span and a frame-normalization condition,
then proves that equality of the original normalized fixed level orbits forces
both rational-isogeny arrows to preserve the full integral Tate image. The
normalization condition compares a source lattice with the actual integral
Tate rationalization; preservation by the rational isogeny is a conclusion.
No external existence theorem is used or claimed in this module.

The source construction reuses `HarrisIntegralPairing` and
`Global.IntegralFiniteAdeles`. The frame and orbit constructions reuse
`HarrisPolarizedWeilClasses`, `PolarizedWeilLevelClasses`, `WeilFrame`,
`WeilFrameIsogeny`, `WeilLevelIsogeny`, `InvariantOrbits` and `OrbitTransport`.
The final argument uses the actual rational Tate linear equivalence in
`AbelianScheme.Tate.Rational`.

## Arithmetic source and integral span

All arithmetic carriers have universe zero. The inputs are totally real and
totally complex number fields `E` and `F`, their quadratic extension structure,
the displayed compatible algebra structures on `A`,
`D : CentralSimpleUnitaryData E F A n`, and the existing Harris signature
charts `C`. The rational source remains the actual regular module `A`, with
its original form `D.harrisHodgePELForm C`.

Write `Af = Global.FiniteAdeles ℚ`,
`Rf = Global.integralFiniteAdeles ℚ`, and `Vf = Af ⊗[ℚ] A`.
The `Rf`-module structure on `Vf` is restriction of its `Af`-module structure
along the actual subring inclusion. If
`L = D.harrisHodgePELIntegralLattice C`, then
`harrisHodgePELIntegralAdeleSpan` is the submodule

`Λf = span_Rf {1 ⊗ x | x ∈ L}`

of this actual `Vf`. The published `L` is the integer lattice constructed for
the unchanged Harris form, rather than an additional lattice parameter.
`harrisHodgePELIntegralAdeleSpan_tmul` proves membership of each displayed
generator by `Submodule.subset_span`.

Let `G` be the original group
`ScalarExtensionSimilitudes A A Af (D.harrisHodgePELForm C)`.
`harrisIntegralAdeleStabilizer` is the subgroup of those `g` satisfying

`g(v) ∈ Λf ↔ v ∈ Λf` for every `v : Vf`.

The identity and composition laws are immediate from this equivalence. The
inverse law evaluates it at `g.symm(v)`. The definition is an actual subgroup
of the original similitude group. This module does not assert that this
subgroup is compact or open, or that a sufficiently small original level
lies in it.

## Actual frames and normalization

For frames, the additional inputs are the named tensor, Picard and duality
prerequisites `P : PolarizedFiniteLevel.Prerequisites`, a quasi-separated
scheme `S`, the relative finite Weil transition statement, the rational
profinite-integer/finite-adele comparison `h`, a field `Ω`, and an actual map
`s : Spec Ω ⟶ S`. The objects `X` are the published
`PositivePolarizedAction` objects. They contain the actual abelian scheme,
rational algebra action, constructed dual data, actual geometric
polarization and its positive auxiliary left-involution compatibility.
Every local star structure in this module is the original
`auxiliaryStarRing D C`.

For an actual Weil-compatible adelic frame `eta` of `X`,
`HarrisIntegralFrameCondition` states, for every `v : Vf`,

`v ∈ Λf ↔ ∃ a : Full(T_X), toRational(a) = eta(v)`.

Here `Full(T_X)` is literally
`GroupScheme.Tate.Full X.actionObj.abelianScheme.toGrp (Over.mk s)`.
`toRational` is the actual full integral Tate rationalization, with index
predicate `fun _ => True`; it is not a prime-to subset or an independently
chosen lattice. The displayed condition identifies membership in the
source span with membership in the full image of that map.

`harrisIntegralFrameCondition_right` proves invariance under the original
opposite right action at a member of `harrisIntegralAdeleStabilizer`.
The original action has `right eta g` evaluating to `eta(g(v))`. One
direction composes the stabilizer membership equivalence with normalization;
the other evaluates at `g.symm(v)` and uses the inverse identities.
No action convention is changed.

`harrisIntegralFrameCondition_of_orbit_eq` then proves that two frames in
the same original `U`-right orbit have equivalent normalization conditions,
provided `U` is contained in the stabilizer. It uses the original
`RightOrbit.mk_eq_mk` to obtain the translating member of `U`, and applies
the preceding invariance theorem.

## Normalization of original fixed levels

For levels, retain all original inputs to `PolarizedWeilLevel.levelTower`:
finiteness of every finite-etale-cover fibre at `s`, the torsion finite-etale
statement, invertibility of every positive torsion index in `Γ(S, ⊤)`, and
the finite and etale structure-map instances for the corresponding roots
of unity. The geometric monodromy actions and original opposite right
orbits are precisely those used by that tower.

For `K : FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)` and
`x : (levelTower X).obj K`, `HarrisIntegralLevelCondition` says that there
exists an actual normalized Weil frame `eta` with
`RightOrbit.mk K.toSubgroup eta = x.val`. Thus `x` remains a geometrically
fixed orbit of the original tower, not an element of a new quotient.

`harrisIntegralLevelCondition_iff` proves that, when
`K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C`, this condition is
equivalent to normalization of any supplied representative of `x.val`.
The forward direction compares the witness and that representative using
the equal-orbit theorem. The reverse direction uses the supplied
representative as the normalization witness.

## Both actual integral-image preservation assertions

`harrisIntegralLevelCondition_integralImages` additionally takes the original
`PositivePairAdditivity`, two actual positive polarized objects `X` and `Y`,
a level `K` contained in the stabilizer, a rational unit `q`, an isomorphism
`e : X.actionObj ≅ Y.actionObj`, and the original
`PolarizedWeilLevel.Multiple X Y q e` equation. This is a rational-isogeny
isomorphism of the original rational algebra-action category; it is not
assumed to arise from an isomorphism of abelian schemes.

For normalized original fixed levels `x` and `y`, assume the literal original
level-transport equality

`PolarizedWeilLevel.levelIso ... X Y K q e he x = y`.

Write `r` for the actual rational Tate map of
`RationalAlgebraAction.underlyingIso e`. The theorem proves both assertions:

- For every full integral Tate element `a` of `X`, there is a full integral
  Tate element `b` of `Y` with `r(toRational(a)) = toRational(b)`.
- For every full integral Tate element `b` of `Y`, there is a full integral
  Tate element `a` of `X` with `r⁻¹(toRational(b)) = toRational(a)`.

In Lean both maps are written as the actual `Tate.rationalHomMap`, using
respectively the `.hom` and `.inv` of the same underlying rational isomorphism.
The theorem needs neither connectedness nor local noetherianness of `S`,
nor algebraic closedness or characteristic zero of `Ω`, beyond its displayed
original tower hypotheses.

The implemented proof chooses normalized frame representatives `eta` and
`xi`. Taking underlying values of the original `levelIso` equality gives the
original `RightOrbit.map` equality. Rewriting the representatives and using
`RightOrbit.map_mk` identifies the orbit of the actual transported frame
`f(eta)` with that of `xi`. The equal-orbit normalization theorem proves
normalization of `f(eta)`.

For the forward assertion, evaluate `eta.symm` at `toRational(a)`. Source
normalization puts this vector in `Λf`; transported normalization supplies
`b`. The actual `weilAdelicFrameIsogeny` evaluation formula identifies its
image with the rational map of `e.hom`, giving the first equality. For the
reverse assertion, evaluate `f(eta).symm` at `toRational(b)`. Transported
normalization puts this vector in `Λf` and source normalization supplies
`a`. Injectivity of the actual `Tate.rationalIso` and its inverse identities
then give the displayed equality for `e.inv`. These steps use only the
original frame maps and actual integral rationalizations.

## Remaining obligations

This module does not prove existence of normalized frames for arbitrary
Harris representatives, a change to a normalized integral model, or existence
of suitable compact-open stabilizing levels. It also does not remove
rational-isogeny denominators: both preservation assertions are conclusions
on actual Tate images, while reflection to an actual abelian-scheme
isomorphism is a further theorem.

The original determinant condition, conjugated reflex scalar convention,
normalized rational-isogeny moduli comparison, ambient polarized PEL
representability, output admissibility, smoothness and division-case
projectivity are unchanged. No representing scheme is constructed here.
The exact `DivisionCMRepresentabilityStatement` remains open.
