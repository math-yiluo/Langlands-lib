# The actual affine Iwahori–Tits datum

This unit defines the fixed-data assertion for the `G(F)^0` branch of
Kaletha–Prasad Theorem 7.5.3(1),(2). It proves only intrinsic subtype and
projection identities. It does not prove that the assertion holds.

The original source is *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
Definition 2.6.23 for the zero subgroups; Definition 7.4.1(4) for the generated
parahoric; Lemma 7.5.2 and Theorem 7.5.3, printed pp. 260–261 / PDF pp. 291–292.
The corrections of 1 November 2024, `kaletha-prasad-2024-corrections`,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p. 35, replace the printed saturation intersection by
`⋂ n ∈ N, n I n⁻¹`. The published generic `TitsSystem.IsSaturated` already
has that corrected formula.

All declarations are in `Langlands.Geometry.Building.ParahoricBuildingData`.
The field universe `u` is arbitrary. The supplied `P : ParahoricBuildingData G`
and the field, valuation and topology assumptions are exactly the actual-object
context of `IwahoriDoubleCosetStatement`. No new reductivity, connectedness,
normality or geometric hypothesis is inserted into that context.

## Actual groups and internal adapters

| Declaration | Exact meaning |
| --- | --- |
| `parahoricInZero P Ω` | `(P.parahoric Ω).subgroupOf P.zeroSubgroup`, a subgroup of the actual `G(F)^0`. Here `P.parahoric Ω` is the existing supremum of the mapped `P.centralizerZero` and `P.sharpFixer Ω`. |
| `normalizerInZero P` | `(normalizerPoints P.i).subgroupOf P.zeroSubgroup`, the actual normalizer restricted inside that ambient group. |
| `normalizerInZeroEquiv P` | The multiplicative equivalence with `P.normalizerZeroComponent`, swapping the two subtype membership proofs. Both types have the same rational-point value. |
| `parahoricInZero_map P Ω hΩ` | Under `hΩ : P.parahoric Ω ≤ P.zeroSubgroup`, the image of `parahoricInZero` under `P.zeroSubgroup.subtype` equals the full generated `P.parahoric Ω`. |
| `affineTitsProjection P` | `P.affinePartMk.comp P.normalizerInZeroEquiv.toMonoidHom`. Thus its Weyl group is literally `P.affinePart` and its full quotient value is literally `QuotientGroup.mk' P.normalizerZero`. |

The last definition and all subsequent declarations have the explicit fixed-data
instance argument `[P.normalizerZero.Normal]`. No normality proof is constructed.
`affineTitsProjection_coe` gives the equality with the full quotient projection
for every `n : P.normalizerInZero`; `affineTitsProjection_equiv_symm` gives
equality with `P.affinePartMk n` for every `n : P.normalizerZeroComponent`.
Both proofs are definitional reflexivity. `normalizerInZeroEquiv` also has
reflexive inverse and multiplication proofs. `parahoricInZero_map` applies
Mathlib's `Subgroup.map_subgroupOf_eq_of_le`.

These are internal adapters between existing objects, not source structural
assertions. Restriction alone is an intersection: it does not prove that the
generated full parahoric lies in `P.zeroSubgroup`. That containment is retained
as a field of the actual predicate.

## Comparison, Tits axioms and saturation

`IsAffineWeylComparison P e` asserts, for the supplied multiplicative equivalence
`e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots`,

```text
∀ n : P.normalizerZeroComponent,
  ↑(e (P.affinePartMk n)) = P.apartment.normalizerAffineEquiv ↑n.
```

The equality is in the group of affine automorphisms of the actual apartment.
It is imposed on every normalizer representative. The comparison is neither an
arbitrary abstract group identification nor a different action chosen for the
Tits datum.

`chamberSimpleInAffinePart P e C` is exactly
`e ⁻¹' AffineRootSystem.chamberSimpleReflections P.affineRoots C`.
Those geometric reflections are the actual coroot reflections of positive
indivisible chamber-simple affine roots, as defined in the paired
`AffineChamberReflections` module. KP Definitions 1.3.18–19 and Proposition
1.3.22, PDF pp. 53–54, supply this geometric meaning. In rank zero this set is
empty; no nonempty generating set is required.

`AffineIwahoriTitsWith P C e` is a Prop-valued structure with four fields:

1. `parahoric_le_zero : P.parahoric C ≤ P.zeroSubgroup`;
2. `action_compatible : P.IsAffineWeylComparison e`;
3. `tits : Langlands.Group.IsTitsSystem B N π S`, with the literal data
   `B = P.parahoricInZero C`, `N = P.normalizerInZero`,
   `π = P.affineTitsProjection`, `S = P.chamberSimpleInAffinePart e C`;
4. `saturated : Langlands.Group.TitsSystem.IsSaturated B N`.

The generic Tits predicate retains surjectivity, the exact kernel, generation,
involutivity and both BN axioms for every normalizer representative.
The theorem `AffineIwahoriTitsWith.saturation_formula` unfolds the last field
without a mathematical proof obligation:

```text
(⨅ n : P.normalizerInZero,
   (P.parahoricInZero C).map
     (MulAut.conj (n : P.zeroSubgroup)).toMonoidHom)
  = P.parahoricInZero C ⊓ P.normalizerInZero.
```

This is the subgroup intersection `⋂ n, n I n⁻¹ = I ∩ N` in `G(F)^0`.
`AffineIwahoriTits P C` existentially quantifies the comparison `e` and asserts
`P.AffineIwahoriTitsWith C e`. The definitions supply the concrete data;
containment, action comparison, the Tits axioms and saturation are assertions
still to be proved. There is no assertion about the separate `G(F)^♮` branch
or independence of the chosen torus or chamber.

## Retained consumer obligations

The later global target must conclude the normality witnesses and this fixed
predicate from only the apartment axioms and the chamber premise. This module
does not discharge those normalities, actual-action kernel and range comparisons,
geometric generation, chamber transitivity, or the structural assertions of
Theorem 7.5.3. Facet stabilizers and generated facet parahorics need the separate
Proposition 7.5.5 comparison.

The unchanged global `IwahoriDoubleCosetStatement` and
`ParahoricDoubleCosetStatement` additionally need the component extension,
normalizing chamber representatives and the generic double-coset transports
with their values on every full normalizer representative. None is proved here.
The future validity predicate for corrected Axiom 4.1.9 is stronger input and
does not discharge these apartment-only Chapter 7 statements.
