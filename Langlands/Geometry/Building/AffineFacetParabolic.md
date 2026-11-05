# Actual facet stabilizers and generated parahorics

This fixed-data definition records both assertions of Kaletha–Prasad
Proposition 7.5.5: the facet-generated reflection subgroup is the affine facet
stabilizer, and the generated full facet parahoric is the corresponding standard
parabolic of the actual Iwahori–Tits system. It proves only consequences of these
assertions by subtype transport; it does not prove Proposition 7.5.5.

The source is *Bruhat–Tits Theory: A New Approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Proposition 7.5.5, printed pp. 261–262 / PDF pp. 292–293.
The standard parabolic formula is Definition 1.4.4(1), in the Tits-system
discussion of §1.4. The authors' 1 November 2024 corrections,
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 33–36, leave Proposition 7.5.5 unchanged and correct the Chapter 7
assumptions and the consumer proof of 7.8.1(2).

All declarations below are in
`Langlands.Geometry.Building.ParahoricBuildingData`, for arbitrary field universe
`u` and the same actual `P` and field assumptions as the unchanged closing
double-coset statements. `[P.normalizerZero.Normal]` is an explicit fixed-data
instance argument permitting the actual quotient group operations. It is not
proved or assumed by a new global premise.

## Reflection subgroup and full parahoric

`facetSimpleInAffinePart P e C Fa` is exactly
`e ⁻¹' AffineRootSystem.facetSimpleReflections P.affineRoots C Fa`,
where `e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots`.
Its reflections come from the positive indivisible chamber-simple roots `ψ`
satisfying `∀ x ∈ Fa, ψ x = 0`. The intrinsic lemma
`facetSimpleInAffinePart_subset` applies the geometric subset lemma and shows
that this is a subset of `P.chamberSimpleInAffinePart e C`. It asserts no
generation or stabilizer theorem. In rank zero both sets are empty and their
generated subgroup is trivial.

`FacetParabolicComparisonWith P C Fa e` is a Prop-valued structure whose fields
are exactly:

| Field | Assertion |
| --- | --- |
| `face` | `AffineRootSystem.IsFaceOf P.affineRoots Fa C`. This includes that `Fa` is a nonempty facet in the closure of `C`. |
| `parahoric_le_zero` | `P.parahoric Fa ≤ P.zeroSubgroup`, for the existing generated full parahoric. |
| `weyl_stabilizer` | `(Subgroup.closure (P.facetSimpleInAffinePart e C Fa)).map P.affinePart.subtype = P.affineFacetStabilizer Fa`. This is equality inside the full `P.IwahoriWeylGroup`. |
| `parabolic_eq` | `(P.parahoricInZero Fa : Set P.zeroSubgroup) = TitsSystem.standardParabolic (P.parahoricInZero C) P.affineTitsProjection (P.facetSimpleInAffinePart e C Fa)`. |

Writing `B = P.parahoricInZero C`, `π = P.affineTitsProjection` and
`X = P.facetSimpleInAffinePart e C Fa`, the last field has the literal formula

```text
↑(P.parahoricInZero Fa) = {g | ∃ w ∈ Subgroup.closure X, g ∈ cell B π w},
cell B π w =
  {g | ∃ n : P.normalizerInZero, π n = w ∧
    ∃ b ∈ B, ∃ b' ∈ B, g = b * ↑n * b'}.
```

Thus it specifies a union of Iwahori Bruhat cells with the same actual
normalizer quotient as the Tits predicate. The identity with the generated
full parahoric is explicit: `FacetParabolicComparisonWith.parahoric_image`
states

```text
(P.parahoricInZero Fa).map P.zeroSubgroup.subtype = P.parahoric Fa.
```

It applies the containment field and the intrinsic restriction lemma.
`FacetParabolicComparisonWith.parahoric_eq_bruhat_cells` then states, in
`rationalPoints G`,

```text
↑(P.parahoric Fa) =
  P.zeroSubgroup.subtype '' TitsSystem.standardParabolic B π X.
```

Its proof rewrites `parabolic_eq` and the preceding subgroup-image identity.
This explicitly compares both ambient groups; it uses no structural proof.

The right side of `weyl_stabilizer` is literally the existing
`(P.normalizerZeroComponent ⊓ P.normalizerStabilizer Fa).map
(QuotientGroup.mk' P.normalizerZero)`. The stabilizer is setwise.
`P.zeroFixer Fa`, the pointwise fixer intersected with `P.zeroSubgroup`, is a
separate definition and is not used or equated with either side here.
No equality between the generated full parahoric and a pointwise fixer is
hidden in the notation.

## Common chamber and retained obligations

`CommonChamberFacetParabolics P C F₁ F₂` existentially quantifies one
multiplicative comparison `e` and asserts

```text
P.AffineIwahoriTitsWith C e ∧
P.FacetParabolicComparisonWith C F₁ e ∧
P.FacetParabolicComparisonWith C F₂ e.
```

The two facets therefore use the same chamber Iwahori, geometric comparison
and actual quotient projection. The action comparison in the Tits conjunct
applies to every `n : P.normalizerZeroComponent`; its projection has the same
full quotient value on every representative. No representatives are selected
by an existential choice of a section. The full quotient and its component
groups are retained, including in the stabilizer equality.

The global target must derive this predicate and normality witnesses from only
the apartment, chamber and common-chamber face premises. The facet stabilizer
theorem, both parahoric containments, the standard-parabolic equality and all
Tits assertions remain future proof obligations.

The closing `ParahoricDoubleCosetStatement` concerns every element of the full
normalizer, including representatives outside `G(F)^0`. Applying this fixed
comparison there still requires the component extension and normalization
comparisons, generic parabolic double-coset transports, and their values on
every full normalizer representative. The unchanged
`IwahoriDoubleCosetStatement` has the analogous retained obligations. This unit
neither assumes nor proves either closing target. The future validity
predicate for corrected Axiom 4.1.9 does not discharge these apartment-only
Chapter 7 obligations.
