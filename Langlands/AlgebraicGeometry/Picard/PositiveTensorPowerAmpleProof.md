# Ampleness under positive tensor powers and sheaf isomorphisms

`Langlands.AlgebraicGeometry.Picard.positiveTensorPowerAmple` proves the
published proposition
`Langlands.AlgebraicGeometry.Picard.PositiveTensorPowerAmpleStatement.{u}`.
Its type is exactly that proposition. For every scheme `X : Scheme.{u}`,
every actual `L M : LineBundle X`, and every natural number `n`, it proves

```text
0 < n → L.IsAmple →
  Nonempty (M.obj ≅ Langlands.Scheme.Modules.tensorPow L.obj n) → M.IsAmple.
```

The proposition, line bundles, ampleness predicate, section powers and
sheaf tensor powers are imported from the Library unchanged.

## Implemented proof

Choose the actual isomorphism `e : M.obj ≅ tensorPow L.obj n` from the
`Nonempty` hypothesis. Preserve the compactness witness in `L.IsAmple`.
For a point `x : X`, ampleness of `L` supplies a positive exponent `k`, a
global section `s` of `tensorPow L.obj k`, membership of `x` in its whole
generation open, and affineness of that open.

Package `tensorPow L.obj k` as a line bundle `K` using the published
unconditional theorem
`Langlands.AlgebraicGeometry.Picard.tensorPow_isLocallyFreeRankOne`
from `Langlands.AlgebraicGeometry.Picard.TensorRankOneProof`.
The published `sectionPow K.obj s n` is a global section of
`tensorPow K.obj n`.

Construct an isomorphism `a : tensorPow K.obj n ≅ tensorPow M.obj k`
by the following sequence of actual module-sheaf isomorphisms:

```text
(L^k)^n ≅ L^(k*n) ≅ L^(n*k) ≅ (L^n)^k ≅ M^k.
```

Here the powers denote the Library's actual `tensorPow`. The first and
third arrows are `tensorPowMulIso L.obj k n` and the inverse of
`tensorPowMulIso L.obj n k`. The middle arrow is `eqToIso` applied to
the equality induced by `Nat.mul_comm k n`. The last arrow is the inverse
of `tensorPowIso e k`. These constructions are published in
`Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms`.
The right-associated powers retain their structure-sheaf unit factors;
the published isomorphisms handle those factors, including exponent one.

Let `t := a.hom.app ⊤ (sectionPow K.obj s n)`, a global section of
`tensorPow M.obj k`. The published theorem
`Langlands.SchemeModule.trivializationOpen_mapIso` from
`Langlands.AlgebraicGeometry.Picard.AmpleIsoProof` identifies the whole
generation open of `t` with that of `sectionPow K.obj s n`. The published
theorem `Langlands.SchemeModule.trivializationOpen_sectionPow` from
`Langlands.AlgebraicGeometry.Modules.PositiveSectionPowerGenerationLocusProof`,
applied to `K`, `s`, and `0 < n`, identifies the latter whole open with
the generation open of `s`. Thus `M.sectionOpen t = L.sectionOpen s`.

Use this equality to transfer both point membership and affineness. The
same exponent `k`, its original witness `1 ≤ k`, and `t` provide the
required ampleness witness for `M` at `x`. This completes the definition
of `M.IsAmple` for every point.

## Provenance and scope

The original mathematical implication is the forward direction of
The Stacks Project, [Lemma 28.27.2, tag 01PT](https://stacks.math.columbia.edu/tag/01PT),
registered as `stacks-ample-powers-restriction-quasiaffine-2026-10-24`.
The retained source is `01PT.html` in
`literature/Stacks Project - Ample powers, closed restriction and quasi-affineness (HTML snapshot 2026-10-24)`,
directory SHA256
`03dddd39b5528263fbc3633f1545b8544e937bb29c9752ffe4a351bb6e093e9a`.
Its proof invokes equality of the loci of a section and a positive power.
The proof and both comments were read; the comments concern the EGA
reference and its quasi-compactness convention. No source-specific erratum
file was present in the current Library when this proof was written.

The Lean proof implements that locus argument using independently
published generation-open and local rank-one theorems, then transports
through the supplied actual isomorphism. The target's additional `M`
and isomorphism hypothesis are the internal packaging described in the
published statement's companion. Equality of whole opens is used
throughout, so the transferred affineness is affineness of the entire
generation open.

There are no additional outer premises or restrictions on the scheme,
the line bundles, or the positive exponent. The proof imports its
infrastructure as theorems and defines no replacement constructions.
The converse implication of the source lemma is outside the target.
The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
