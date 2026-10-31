# Compact Whittaker synthesis from group tests

This internal helper defines and studies the actual character-weighted subgroup
integral of a compactly supported locally constant group test. It retains the
supplied subgroup Haar measure. The final theorem synthesizes every element of
the published compact induction of a scalar character. This is a group-test
synthesis result; it does not establish a matrix Fourier identity, weighted
extraction, or the matrix-to-rank-one gamma comparison.

For a topological group `G`, subgroup `H`, supplied measure `μH`, and unit-valued
character `χ : H →* ℂˣ`, the definition is

```text
characterOrbitIntegral H μH χ φ g
  = ∫ h : H, χ(h)⁻¹ φ(h g) dμH(h).
```

The standing setting is a Hausdorff topological group, a closed
subgroup with a Borel measurable space, and a supplied Haar measure on that
subgroup which is also right invariant. The character is continuous. No
unitarity, regularity assumption on the Haar measure, quotient measure,
normalization of subgroup volumes, or second countability is imposed.
Individual elementary lemmas omit assumptions they do not use.

`characterOrbitIntegrable` proves absolute Bochner integrability at every `g`.
The map `h ↦ h g` is a closed embedding of the closed subgroup followed by a
homeomorphism, so the pullback of the compact support of `φ` is compact.
Multiplication by the continuous inverse character retains that compact support,
and continuity with compact support gives integrability.

`characterOrbitIntegral_left` proves
`Aφ(p g) = χ(p) Aφ(g)` for `p : H`, by the actual right-Haar substitution
`h ↦ h p`. The character factors cancel in the units of `ℂ`. The additive
lemma uses the preceding integrability result. Scalar multiplication and right
translation commute with the actual total integral; the translation convention
is the published `rightTranslate a φ x = φ(x a)`.

The theorem `exists_characterOrbitIntegral_eq` assumes additionally the literal
compact-open basis condition used by the published
`Langlands.Induction.compactLocalSectionSpanning`: every open neighborhood of
`1` contains a compact open subgroup. For every

```text
f : Induction.CompactFunctions H (characterRepresentation χ)
```

it produces a single `φ : SchwartzBruhat G` with `Aφ(g) = f(g)` at every `g`.
The compact functions here are the actual smooth covariant functions with
compact projected nonzero support, with the right-translation action already
defined in compact induction. The theorem uses these definitions, without
identifying compact-modulo-`H` support with compact support on `G`.

The private local-section lemma supplies an explicit lift. For a compact open
subgroup `K`, let `S = {h : H | h ∈ K}` and
`c = ((μH S).toReal : ℂ)`. Closedness of `H` makes `S` compact; openness of `K`
makes it a nonempty open subset of `H`. Its Haar mass is therefore positive and
finite, so `c ≠ 0`. If `v` is fixed by `H ∩ K` in the scalar character
representation, the test

```text
φ = (v / c) • Hecke.TestFunction.subgroupIndicator K hK
```

lifts the identity-centered compact double-coset section with value `v`.
At the identity its integrand is the indicator of `S` times `v / c`: the
fixed-vector condition cancels the inverse character. Thus its integral is
`c * (v / c) = v`. Right `K`-invariance and the proved left character
covariance give the asserted values on `H K`. Off `H K`, the test integral
vanishes pointwise and the published section-support theorem forces the
section to vanish. This argument also covers `v = 0` and does not assume
that `χ` is trivial on the whole subgroup.

The private submodule `liftableFunctions` consists of compact induced functions
having such a test lift. The integral's linearity makes this a submodule.
Every translated identity-centered local section belongs to it, by the
local lift and the actual test-function translation identity. The published
compact-local-section spanning theorem makes their span the full compact
induction, proving synthesis.

All constructions are derived internally from the published actual-function,
Haar-integration, compact-section, and spanning definitions and theorems. No
external literature assertion is used as an unproved premise. The group
universe is arbitrary. No new axiom or proof hole is introduced.
