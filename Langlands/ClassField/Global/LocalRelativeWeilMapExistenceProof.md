# Existence of local-to-relative Weil maps at finite places

Author: Worker 5073, for task `241e7251-de0b-431f-83a9-5584e974e22b`. The reduction theorem
reuses, unchanged, a draft by Worker 248 of a previous instance.

This module proves the published proposition
`Langlands.ClassField.Global.LocalRelativeWeilMapExistenceStatement.{u}`
(module `Langlands.ClassField.Global.LocalRelativeWeilMapStatement`) as the theorem
`Langlands.ClassField.Global.localRelativeWeilMapExistence`, with no hypotheses.

The statement says the following. Let `I` be a local family of invariant families
satisfying `RelativeClassFormation` and `ArithmeticNormalization` at every prime. Let `c`
be a global class family with `Generates`, `Restriction`, `Inflation` and
`LocalCompatibility I c`. Let `E/F` be a Galois extension of number fields, `v` a finite
place of `F`, `w` a finite place of `E` over `v`, and `e` a reciprocity candidate for `E_w`
satisfying the geometric Weil reciprocity relation. Then there is a continuous
homomorphism `ι : W_{F_v} →ₜ* W_{E/F}` (the relative Weil group `RelativeWeilGroup c F E`)
with `RelativeWeilGroup.IsLocalRelativeWeilMap v w e ι`. That is, through
`E → E_w → \bar{F_v}` the Galois image of `ι g` acts as that of `g`, and on `W_{E_w}` the map
`ι` is the inverse of `e` followed by `E_wˣ → C_E`.

The proof has two steps.

1. `localRelativeWeilMapExistence_of_localWeilClassMapExistence` derives the statement
   from the published proposition
   `Langlands.ClassField.Global.LocalWeilClassMapExistenceStatement.{u}`
   (module `Langlands.ClassField.Global.LocalWeilClassMapStatement`), the local
   Weil–Shafarevich step at completions.
2. `localRelativeWeilMapExistence` applies this to the published theorem
   `Langlands.ClassField.Global.localWeilClassMapExistence`
   (module `Langlands.ClassField.Global.LocalWeilClassMapProof`), which proves that
   proposition unconditionally.

## Imports

- `Langlands.ClassField.Global.LocalRelativeWeilMapStatement`, the target statement.
- `Langlands.ClassField.Global.LocalRelativeWeilMapReduction`, which provides
  `RelativeWeilGroup.localWeilToRelative` and
  `RelativeWeilGroup.isLocalRelativeWeilMap_localWeilToRelative`.
- `Langlands.ClassField.Global.LocalWeilClassMapStatement`, the hypothesis of the
  reduction.
- `Langlands.ClassField.Global.LocalWeilClassMapProof`, which provides
  `localWeilClassMapExistence`.
- `Langlands.ClassFieldTheory.Local.FundamentalConsequencesProof`, which provides
  `InvariantFamily.fundamentalClasses_of_relativeImages`.

## `Langlands.ClassField.Global.localRelativeWeilMapExistence_of_localWeilClassMapExistence`

`LocalWeilClassMapExistenceStatement.{u} → LocalRelativeWeilMapExistenceStatement.{u}`.

Proof. Introduce `I`, its laws `hI`, the class family `c` with
`hc : Generates c ∧ Restriction c ∧ Inflation c ∧ LocalCompatibility I c`, the number
fields `F E` with `[IsGalois F E]`, the places `v`, `w` with `w` over `v`, and the
candidate `e` with its geometric normalization `he`.

1. The published `isGalois_adicCompletion v w` gives
   `IsGalois (padicField v).Carrier (w.adicCompletion E)`. The published
   `FiniteExtension.local_finite` gives the corresponding `FiniteDimensional` instance.
2. `(hI (residuePrime v)).1.2.1` is the `RelativeImages` field of
   `RelativeClassFormation` for `I (residuePrime v)`. The published
   `InvariantFamily.fundamentalClasses_of_relativeImages` turns it into
   `FundamentalClasses`. Its first component, at `padicField v` and `w.adicCompletion E`,
   gives a class `a : CompletionH2 v w` and a proof `ha` that `a` is a fundamental class for
   the relative invariant `(I (residuePrime v)).relative (padicField v) (w.adicCompletion E)`.
3. The hypothesis, applied as `hK F E v w (I (residuePrime v)) (hI _).1 (hI _).2 e he a ha`,
   gives `κ : Weil.Local.localWeilGroup (padicField v) →ₜ* CompletionClassExtension v w a`
   with its clauses `hP` (Galois projection) and `hR` (the inverse of `e` on `W_{E_w}`).
4. Topology transfer. In `LocalWeilClassMapExistenceStatement`, the topology on
   `CompletionClassExtension v w a` is induced from the product `Gal(E_w/F_v) × E_wˣ`, with
   Mathlib's Krull topology on `Gal(E_w/F_v)`. The helper `localWeilToRelative` expects the
   same extension with the discrete topology `completionGaloisTopology v w` (defined as `⊥`)
   on `Gal(E_w/F_v)`. The Galois group is finite, so its Krull topology is discrete (Mathlib
   instance `krullTopology_discreteTopology_of_finiteDimensional`), and
   `DiscreteTopology.eq_bot` shows that the two topologies are equal. The proof takes the
   underlying monoid homomorphism `f` of `κ`, with `∀ g, f g = κ g` and `Continuous f`,
   rewrites the continuity proof along this equality, and builds `κ'` with underlying
   homomorphism `f` and the discrete topology. Here `f` is introduced as an opaque variable
   so that the rewrite does not touch the type of `κ`. Then `κ' g = κ g` for every `g`.
5. The witness is `RelativeWeilGroup.localWeilToRelative c v w I hc.2.2.2 a ha κ'`, which
   composes `κ'` with the published map `localToRelative` from the completed local class
   extension into `W_{E/F}` (it uses `LocalCompatibility I c`, the last component of `hc`).
   `RelativeWeilGroup.isLocalRelativeWeilMap_localWeilToRelative`, applied to `e`, `he`
   and to `hP` and `hR` rewritten along `κ' g = κ g`, proves
   `IsLocalRelativeWeilMap v w e` for it.

## `Langlands.ClassField.Global.localRelativeWeilMapExistence`

`LocalRelativeWeilMapExistenceStatement.{u}`.

Proof. Apply `localRelativeWeilMapExistence_of_localWeilClassMapExistence` to
`localWeilClassMapExistence`.

## Checks

`lean_check` of this module against Library `6bff2655fd831aefb39f6688f904aa7410cb0f73`,
with declaration `Langlands.ClassField.Global.localRelativeWeilMapExistence`: 0 errors and
0 warnings. The theorem has the universe parameter `u` and uses only `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The map is Tate's `θ_v : W_{F_v} → W_F` of (1.6.1), at the level of a finite Galois
extension `E/F`: the local Weil group maps into the completed local class extension (the
local Weil–Shafarevich theorem), followed by the published local-to-relative map of
extensions. See the Markdown of `LocalRelativeWeilMapReduction` and
`LocalWeilClassMapStatement`. The proof itself is internal: it assembles the published
results named above.

- J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979),
  source `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`: (1.6.1) and the
  sentence after it, printed pp.8–9 (PDF pp.17–18).
