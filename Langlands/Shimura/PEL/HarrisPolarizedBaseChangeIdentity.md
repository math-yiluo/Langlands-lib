# Identity of actual Harris polarized level pullback

This derived unit proves the identity law for the actual pointed pullback of
ambient Harris polarized rational-isogeny classes constructed in
`HarrisPolarizedClassBaseChange`. The result is an equality of functions at
every original Harris level and an equality of natural transformations on the
whole original Harris transporter category. The two point presentations
`t ≫ 𝟙 S` and `t` are compared by their canonical equality. The pulled-back
polarized representatives need not be equal as records.

The arithmetic data are the totally real number field `E`, totally complex
quadratic extension `F`, central simple unitary datum `D` on `A`, and signature
charts `C` used by the imported Harris construction. The star operation is its
constructed positive auxiliary left involution. The form is
`D.harrisHodgePELForm C`, and the level indices are the original `HarrisLevel D`
with their opposite-group transporter arrows, reindexed by
`hodgeLevelFunctor D C`.

The base is an arbitrary quasi-separated universe-zero scheme `S`. The point
`t : Spec Ω ⟶ S` is field-valued; algebraic closedness and connectedness are
not required. Finite fibres for both `t` and `t ≫ 𝟙 S` are explicit inputs.
All named construction premises remain: pullback tensor comparison,
composition, unit coherence, associativity, left-unitor comparison and
symmetry; Picard-zero pullback, the Mumford-bundle Picard-zero property and
universal base change; integral dual-base-change naturality and full
polarization stability; relative finite-Weil transition; the rational
profinite-integer/finite-adele comparison; torsion finite etaleness;
invertibility of every indexed torsion order and finite etale roots of unity
on `S`. `PositivePairAdditivity` supplies ordered-pair additivity of the actual
dual maps for positive polarized actions on `S`.

A family `dualData` supplies `PositivePullbackDualData ... (𝟙 S) X` for each
source positive polarized action `X`. Its dual-scheme existence, geometry,
inverse Poincare bundle, tensor evaluation and endomorphism additivity are
indexed by the actual identity pullback of the same abelian scheme. No
independent output polarization or level is a field of that bundle. The
existing construction uses these inputs to construct the pulled polarization
and actual compatible fixed-level orbit. Its faithfulness witness comes from
a frame contained in the source orbit.

`levelDataPointEq` transports an actual Harris level representative along an
equality `s = r` of two points over the same field. Its first component is
definitionally the same positive polarized action; only its fixed-level orbit
is transported, using the existing `Tate.weilAdelicLevelPointEq`. This is the
equality transport needed for the identity and later associativity formulas.
It does not select a path between unequal points. `ambientClassPointEq` and
`ambientClassTowerPointEq` are the corresponding equality transports of the
ambient quotient and the whole tower. They reduce to identity after
substitution of the point equality. Their component lemmas show that the
quotient transport acts by `levelDataPointEq` and that tower components are
the corresponding quotient maps. Separate finite-fibre witnesses disappear
by proof irrelevance after substitution.

Write `I = 𝟙 S`, let `x` be a source representative at `t ≫ I`, and write
`P_I x` for `levelDataBaseChange ... I ... U x`. The actual action isomorphism

```text
i = RationalAlgebraAction.pullbackIdIso x.1.actionObj
```

runs from the actual pulled action to the source action. The theorem
`levelDataBaseChange_id_multiple` proves

```text
PolarizedWeilLevel.Multiple ... addS (P_I x).1 x.1 1 i.
```

This is the existing geometric rational dual-pullback predicate, with rational
unit one. The proof specializes `rationalDualBaseChangeHom_id_multiple` to the
rationalization of the actual source polarization. The integral recovery
formula `rationalDualBaseChangeHom_homToHom0` identifies its pulled map with
the actual polarization used in `P_I x`. Thus the multiplier is proved by the
actual dual identity comparison, rather than supplied as an extra hypothesis.

`levelIso_pullbackId` identifies the polarized rational-isogeny level map
attached to `i` with the actual geometric Tate identity comparison
`weilAdelicLevelBaseChangeId`, on every fixed-level orbit of the pulled object.
The proof passes to the underlying right orbits and uses
`RightOrbit.map_congr`. Frame extensionality reduces the comparison to
`rationalHomMap_ofHom` for the actual abelian-scheme identity comparison.
The right action is the same scalar-extension similitude action on both
sides; fixed-orbit proof components are removed by subtype extensionality.

`levelDataBaseChange_id_related` then proves the actual target setoid relation
between `P_I x` and `levelDataPointEq (Category.comp_id t) ... U x`. Its witness
is precisely the rational unit one, `i`, and the proved geometric multiplier.
For its remaining orbit equation, `levelIso_pullbackId` identifies the
isogeny level map, and `Tate.weilAdelicLevelBaseChange_id` gives the identity
pullback formula at the canonical point equality. This proves the relation in
the existing polarized-isogeny setoid without changing that relation.

`ambientClassBaseChange_id` states, at every original Harris level `U`,

```text
ambientClassBaseChange ... I ... dualData addS addS U
  = ambientClassPointEq ... addS (Category.comp_id t) hs ht U.
```

Quotient induction, the two representative formulas and `Quotient.sound`
reduce this equality to `levelDataBaseChange_id_related`.
`ambientClassTowerBaseChange_id` follows by extensionality in the level and
quotient class. Since both sides are natural transformations of the original
Harris tower, the equality includes all its existing level and Hecke arrows.
Finally `ambientClassTowerBaseChangeOfExists_id` proves the same law when only
`dualExists : ∀ X, Nonempty (PositivePullbackDualData ... I X)` is supplied.
It applies the proved law to the family selected by classical choice inside
the existing choice-independent constructor. This does not prove `dualExists`.

The provenance is an internal derivation from the imported actual dual
base-change coherence, geometric Tate identity coherence, constructed
polarized pullback and quotient universal property. This unit is not a
separate translation of a numbered literature theorem; its Harris conventions
are inherited from those constructions. It concerns ambient polarized
classes before any Lie, determinant or dimension restriction. Composition of
base maps, the restricted Harris moduli functor, its representability and
scheme levels, and coefficient descent remain separate obligations. None of
the named tensor, Picard, polarization, torsion or Weil premises is discharged
here.
