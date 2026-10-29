# Proof of the Haar modulus of the actual mirabolic radical

Authors: Worker 984 and Worker 357. Worker 357 wrote the unreviewed
radical-coordinate transport experiment shared as revision 1 of the draft for
task `f947a735-872d-44db-a9ea-954d17dec4bd`; its positive-character helpers
are adapted here. Worker 984 adapted them to the published proposition, added
the closing theorem and wrote this file.

## Result

The theorem `Langlands.mirabolicRadicalHaarModulus.{uF}` in the module
`Langlands.Group.GL.MirabolicModulusProof` has the complete type

```lean
theorem Langlands.mirabolicRadicalHaarModulus {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    Langlands.MirabolicRadicalHaarModulusStatement.{uF} F T
```

It proves the published proposition in
[MirabolicModulusStatement](MirabolicModulusStatement.md) without change. The
statement covers every prime `p`, every field `F`, its supplied realization `T`
and every rank `n : ℕ`, including `n = 0`. For each `n` it proves both
equalities of the conjunction:

1. the actual radical character `HaarModulus.closedRestrictCharacter` for
   `radical n F.Carrier` and `leviSubgroup n F.Carrier`, composed with
   `leviEquiv`, equals `T.determinantNorm n`;
2. the actual radical character for `radical (n + 1) F.Carrier` and
   `successorSubgroup n F.Carrier`, composed with `successorEquiv`, equals
   `(T.determinantNorm (n + 1)).comp (GeneralLinear.mirabolic n F.Carrier).subtype`.

The theorem has no hypothesis beyond the statement's outer parameters. It
introduces no comparison, analytic, countability or Haar-normalization premise.
The actual Haar character is not replaced by a determinant character by
definition; both sides are computed and compared.

## Topology and instances

All topologies come from the supplied `T`. The field has `T.topology`, and
matrix groups, mirabolic groups and the radical carry the induced matrix unit
and subspace topologies. The closing theorem installs `T.topology` and
`T.fieldT2`, as the statement does. The two character helpers install, for
their own ranks, `T.generalLinearTopologicalGroup`,
`T.generalLinearLocallyCompactSpace` and
`GeneralLinear.Mirabolic.locallyCompactSpace`, the same instances the
statement installs. The instance arguments of the helpers and of the statement
agree up to proof irrelevance of these `Prop`-valued classes. No topology is
changed and the canonical topology of `F` is not used.

Inside the proofs, `T.valuativeRel`, `T.localField` and
`T.secondCountableTopology` give the field's topological ring structure and
second countability for the same topology `T.topology`. The radical carries the
Borel measurable structure, which is the structure used by
`HaarModulus.closedRestrictCharacter`. The field `F.Carrier` carries its Borel
structure, and the coordinate space `Fin n → F.Carrier` carries the native
product measurable structure `MeasurableSpace.pi` of those Borel structures,
which is Borel by second countability.

## Implemented proof

**Multiplicative type synonym.** Mathlib has no measurable structure on
`Multiplicative A`. Two local instances give `Multiplicative A` the measurable
structure and Borel certificate of `A` itself. The private theorem
`multiplicativeHaar_isAddHaar` shows that a Haar measure on `Multiplicative A`
is an additive Haar measure on `A`. Compact finiteness and open positivity
carry over unchanged, and multiplicative left invariance under `ofAdd g` is
additive left invariance under `g`.

**Levi conjugation in coordinates.** `radicalCoordinates_leviConj` proves that
`HaarModulus.normalizerConj` for the actual element `leviEquiv g` sends the
radical element with last-column coordinates `v` to the one with coordinates
`g.val.mulVec v`. It rewrites the published identity
`levi_conjugate_radicalElement` using `radicalElement_coordinates` and
`radicalCoordinates_element`. It holds over every topological commutative
ring.

**Coordinate Haar measure.** `radicalCoordinates_isAddHaar` pushes a Haar
measure `μ` on the radical through the published topological group equivalence
`radicalContinuousEquiv : radical n F ≃ₜ* Multiplicative (Fin n → F)`. Mathlib's
`ContinuousMulEquiv.isHaarMeasure_map` makes the image Haar, and the helper
above makes it an additive Haar measure. The image is
`μ.map radicalCoordinates`. This holds for every Borel measurable structure on
the coordinate space.

**Pushforward scaling.** `radicalHaar_map_leviConj` proves, for every Haar
measure `μ` on the radical and every `g : GL_n(F)`,

`μ.map (normalizerConj (radical n F) (leviEquiv g)) = (|det g|_F)⁻¹ • μ`,

where `|det g|_F` is `T.determinantNorm n g` in `ℝ≥0`. Let `e` be the
homeomorphism built from `radicalCoordinates` and `radicalElement`. Pushing
forward by `e` and using the coordinate formula turns the left side into the
image of the coordinate Haar measure `μ.map e` under `Matrix.toLin' g.val`.
The published `HarmonicAnalysis.padicScalarHaarScaling` gives
`addHaar.map (x ↦ a * x) = (T.normalizedAbsHom a)⁻¹ • addHaar` for every
nonzero `a`. With it, the published
`HarmonicAnalysis.haarMeasure_map_matrix` scales any additive Haar measure on
`Fin n → F` under `toLin' g.val` by `(T.normalizedAbsHom (det g))⁻¹`, which is
the inverse determinant norm. Pushforward commutes with scalar multiplication,
and the equality is pulled back to the radical by injectivity of pushforward
along the measurable embedding `e`.

**Sign.** The Library character value `c` at `m` satisfies
`c • μ.map σ_m = μ` (`HaarModulus.normalizerCharacter_smul_map`). The
pushforward scales by `|det g|_F⁻¹`, so the character is `|det g|_F`, not its
inverse.

**Levi character.** `leviRadical_haarCharacter` proves the first equality.
After `MonoidHom.ext` and `Units.ext`, the value of the left side at `g` is
`mulEquivHaarChar` of the conjugation. Take `μ = haar` on the radical, which is
regular. Mathlib's `mulEquivHaarChar_eq` rewrites the value as
`haarScalarFactor μ (μ.map σ)`. By the pushforward scaling, this is
`haarScalarFactor μ (d⁻¹ • μ)` with `d = |det g|_F`. A dependent rewrite (`rw!`)
is needed because the Haar instance depends on the measure.
`mul_haarScalarFactor_smul` and `haarScalarFactor_self` give
`d⁻¹ * haarScalarFactor μ (d⁻¹ • μ) = 1`. Hence the factor is `d`, solved
in `ℝ≥0ˣ` with `Units.eq_inv_of_mul_eq_one_left`.

**Successor character.** `successorRadical_haarCharacter` proves the second
equality. It applies the Levi equality at rank `n + 1` to the underlying
general-linear element `g.val` of `g : P_n`. The published `successor` is
`levi.comp (mirabolic n F).subtype`, so `successorEquiv g` and
`leviEquiv g.val` have the same underlying mirabolic element. The two
normalizer elements, conjugations and Haar characters therefore coincide by
definition. The value is `|det g.val|_F` with the determinant taken in
`GL_(n+1)(F)`, as the statement requires. This also covers `n = 0`.

**Rank shifts.** The first equality concerns the radical of `P_n ≤ GL_(n+1)`
and the action of `GL_n`. The second concerns the radical of
`P_(n+1) ≤ GL_(n+2)` and the action of `P_n ≤ GL_(n+1)`. It uses the first
equality at rank `n + 1`. Rank zero needs no separate case: the radical is
trivial, and the scaling lemmas allow empty index types.

**Closing theorem.** `mirabolicRadicalHaarModulus` installs `T.topology` and
`T.fieldT2`, introduces `n` and pairs the two helper equalities.

## Provenance of the internal helpers

All helpers are internal derivations from published Library and Mathlib
results. They are `multiplicativeHaar_isAddHaar` (private) and the instances
`multiplicativeMeasurableSpace` and `multiplicativeBorelSpace` (local), and,
in the namespace `Langlands.GeneralLinear.Mirabolic`, the theorems
`radicalCoordinates_leviConj`, `radicalCoordinates_isAddHaar`,
`radicalHaar_map_leviConj`, `leviRadical_haarCharacter` and
`successorRadical_haarCharacter`. They come from Worker 357's shared draft,
renamed without the `_draft` suffix. The statements of the two character
helpers now install the statement's `generalLinearTopologicalGroup` instance
instead of the local-field instance. The source convention for `mod_V` is
documented in the statement's Markdown. The determinant formula is an internal
computation, not a quotation of a source.

## Imports and independence

The module imports only `Langlands.Group.GL.MirabolicModulusStatement` and
`Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof`. Beyond the
statement's own closure, this adds three project modules:
`HarmonicAnalysis.PadicHaarScalingStatement`,
`HarmonicAnalysis.PadicScalarHaarScalingProof` and
`HarmonicAnalysis.PadicRectangularHaarScalingProof`. They import only
`Group.GL.NormalizedCharacter`, `LocalField.Topology` and Mathlib. The complete
transitive project closure has 28 modules. They cover general-linear and
mirabolic groups, local-field normalization and topology, compact-open
subgroups, the Haar-modulus wrapper with its twist and positive-character
helpers, and the scalar and matrix Haar scaling proofs. It contains no
segment, multisegment, irreducibility, square-integrable, tempered or
classification development, and no minus-functor construction.

## Not claimed

This module proves only the positive-character identification above. It does
not state the inverse-half or `rpow` corollaries, and it does not identify the
modular function of the full mirabolic group. It makes no claim about
derivative or minus functors, their exactness or iteration, plus functors,
adjunctions, duality, filtrations, irreducibility or classification.
