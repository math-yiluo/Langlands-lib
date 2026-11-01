# Composition of actual Harris polarized level pullback

This derived unit constructs the actual action comparison between direct and
successive pointed pullback of Harris polarized level representatives. It
proves its geometric polarization multiplier is one, identifies its level map
with the existing geometric Tate comparison, and obtains composition of the
ambient rational-isogeny quotient maps and original-index tower maps. It also
proves the law for the choice-independent tower maps constructed from existence
of actual dual-evaluation inputs.

## Data and hypotheses

The arithmetic data are the totally real number field `E`, totally complex
quadratic extension `F`, central simple unitary datum `D` on `A`, and signature
charts `C` of the imported Harris construction. The star operation is the
constructed positive auxiliary left involution. The alternating form is
`D.harrisHodgePELForm C`. Indices are the original `HarrisLevel D` and their
opposite-group transporter arrows, through `hodgeLevelFunctor D C`.

Let `b : T ⟶ S` and `c : R ⟶ T` be morphisms between arbitrary
quasi-separated universe-zero schemes. Let `t : Spec Ω ⟶ R` be a field-valued
point. Finite fibres are supplied for each of `t`, `t ≫ c`, `(t ≫ c) ≫ b`
and `t ≫ (c ≫ b)`. No algebraic closedness, connectedness, flatness or reducedness
condition is added. All indexed torsion orders are assumed invertible on each
of `S`, `T` and `R`; their roots-of-unity group schemes are assumed finite and
etale. The imported torsion finite-etaleness statement is explicit.

The named tensor and Picard construction premises remain: pullback tensor
comparison, tensor composition, unit coherence, associativity, left-unitor
comparison, symmetry, Picard-zero pullback, the Mumford-bundle Picard-zero
property, and universal base change. Integral dual-base-change naturality,
full polarization stability, relative finite-Weil transition and the rational
profinite-integer/finite-adele comparison remain explicit as well.
`PositivePairAdditivity` on `S`, `T` and `R` supplies the ordered-pair
additivity needed for the respective actual dual maps. Only the `R` premise
is needed for the representative comparison; all three are used for quotient
and tower maps.

Independent families `dualB`, `dualC` and `dualD` supply
`PositivePullbackDualData` for `b`, `c` and `c ≫ b`. Each bundle is indexed by
the actual pullback of its source abelian scheme and contains dual-scheme
existence, dual geometry, an inverse Poincare bundle with tensor evaluation,
and endomorphism additivity. The family for `c` is evaluated at the actual
positive polarized action produced by the first pullback. No family contains
an arbitrary output polarized action, polarization, level, isomorphism or
composition law. The actual pullback construction obtains faithfulness from
a frame in the input level orbit.

## The actual representative comparison

Let `x` be a Harris level representative at the source point `(t ≫ c) ≫ b`
and original level `U`. Write `P_b`, `P_c` and `P_d` for the existing
`levelDataBaseChange` with the corresponding dual families. Put

```text
x_d = P_d (levelDataPointEq (Category.assoc t c b) ... U x)
x_c = P_c (P_b x).
```

The equality transport retains `x.1`, the actual positive polarized action,
definitionally. It changes only the fixed-level orbit along the associativity
equality of the two point presentations. The two new representatives have the
actual directly and successively pulled abelian schemes respectively, with
their constructed polarizations and equivariant rational algebra actions.

`levelDataBaseChangeCompIso U x` constructs an isomorphism

```text
x_d.1.actionObj ≅ x_c.1.actionObj
```

by specializing `RationalAlgebraAction.pullbackCompIso b c x.1.actionObj`.
Its underlying rational isomorphism is the rationalization of the actual
abelian-scheme direct-to-successive base-change comparison. It retains the
actual endpoints; it does not identify the two representative records.

`levelDataBaseChange_comp_multiple` proves the existing geometric predicate

```text
PolarizedWeilLevel.Multiple ... addR x_d.1 x_c.1 1
  (levelDataBaseChangeCompIso ... U x).
```

Here `1` is a rational unit. The proof applies
`rationalDualBaseChangeHom_comp_multiple` to the rationalization of the
source integral polarization, retaining the four actual dual-evaluation
endpoints: source, first pullback, direct pullback and successive pullback.
Three uses of `rationalDualBaseChangeHom_homToHom0` identify the rational maps
with the constructed integral polarizations. Thus multiplier one is proved
in the actual dual-pullback predicate using `dualHom0`, not supplied as a
compatibility assumption.

`levelIso_pullbackComp` identifies the polarized rational-isogeny level map
of this comparison, on every fixed-level orbit of `x_d.1`, with
`Tate.weilAdelicLevelBaseChangeComp` using the same source polarization and
three dual families. After subtype extensionality the proof compares maps on
right orbits by `RightOrbit.map_congr`, using the scalar-extension similitude
group of the Harris form. Extensionality on compatible frames and their
underlying linear equivalences reduces the equation to
`Tate.rationalHomMap_ofHom` for the actual base-change comparison and
`Tate.weilAdelicFrameBaseChangeComp_apply`. Thus this identifies maps on actual
frames before taking invariant level orbits.

`levelDataBaseChange_comp_related` proves that `x_d` and `x_c` are related
by the existing polarized rational-isogeny setoid at `t`. Its witness is the
unit one, `levelDataBaseChangeCompIso`, the proved geometric multiplier, and
the orbit equality. For the last component, `levelIso_pullbackComp` and
`Tate.weilAdelicLevelBaseChange_comp` give the required equation. The Tate
formula expresses the point transport as the inverse equivalence for the
opposite associativity equality; this is the same equality transport used
by `levelDataPointEq`. The setoid relation is not changed or replaced.

## Quotients and towers

Write `F_b`, `F_c` and `F_d` for `ambientClassBaseChange` at the indicated
points, and `E_a` for `ambientClassPointEq (Category.assoc t c b)`. At every
original Harris level `U`, `ambientClassBaseChange_comp` proves the equality
of functions

```text
F_c U ∘ F_b U = F_d U ∘ E_a U.
```

Quotient induction reduces the formula to representatives. The representative
formulas for pullback and equality transport, followed by `Quotient.sound`
and the symmetry of the proved direct-to-successive relation, give the law.
No quotient map or quotient-composition theorem is an extra input.

For the original Harris transporter category,
`ambientClassTowerBaseChange_comp` proves equality of natural transformations

```text
F_b ≫ F_c = E_a ≫ F_d,
```

where `E_a` is now `ambientClassTowerPointEq`. Extensionality in `U` and a
quotient class reduces this to the component equality. Both sides are already
natural transformations of the actual ambient polarized class towers, so the
law includes every existing level transition and Hecke transporter arrow.
It is not only an objectwise assertion with unspecified arrow maps.

Finally, `ambientClassTowerBaseChangeOfExists_comp` proves the same law for
the choice-independent constructor supplied by
`HarrisPolarizedBaseChangeChoice`. Its inputs are existence of the actual
dual-evaluation bundle for every relevant source positive polarized action
for each of `b`, `c` and `c ≫ b`. The proof applies the preceding tower law
to the three families selected by classical choice in that constructor. No
additional `dualB`, `dualC` or `dualD` parameter remains in this theorem, and
it does not prove these existence inputs.

## Provenance and boundary

This is an internal derivation from the imported actual dual abelian-scheme
base-change coherence, geometric Tate composition coherence, constructed
Harris polarized pullbacks, and the quotient universal property. It is not a
new translation of a numbered literature theorem; its arithmetic conventions
are inherited from the imported Harris constructions. The actual identity
law and equality transports are in `HarrisPolarizedBaseChangeIdentity`.

This unit concerns ambient polarized classes. Restriction to the Harris Lie,
determinant and dimension conditions, the moduli functor's representability,
scheme levels and coefficient descent remain separate obligations. No
invariance of dimension under all rational isogenies is asserted. None of the
named tensor, Picard, polarization, torsion or Weil premises is discharged
here.
