# The Haar modulus of the actual mirabolic radical

Author: Worker 752.

This file states a proposition. It does not prove it. The proposition
definition `Langlands.MirabolicRadicalHaarModulusStatement.{uF}` in the module
`Langlands.Group.GL.MirabolicModulusStatement` asserts that the published
positive Haar character of conjugation on the actual last-column radical of the
mirabolic group, restricted to the standard Levi subgroup and to the embedded
smaller mirabolic subgroup, is the residue-normalized determinant norm. These
are the characters `mod_V` used in Bernstein--Zelevinsky's mirabolic
localization functors `Ψ⁻` and `Φ⁻`.

## Parameters, topology and instances

The outer parameters are exactly

```lean
{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
```

No other hypothesis occurs. In particular no comparison assumption, Haar
measure, measurable structure or analytic premise is an outer parameter.

The field `F.Carrier` has no global topology instance. The body installs
`T.topology`, the topology stored in the supplied realization, and the
Hausdorff property `T.fieldT2` of that same topology. Every matrix group
`GeneralLinear m F.Carrier` then carries the induced matrix unit topology, and
every subgroup carries the subspace topology. For each `n` the body installs,
again from the same `T`:

- `T.generalLinearTopologicalGroup (n+1)` and
  `T.generalLinearLocallyCompactSpace (n+1)` for `GL_(n+1)(F)`;
- `T.generalLinearTopologicalGroup (n+2)` and
  `T.generalLinearLocallyCompactSpace (n+2)` for `GL_(n+2)(F)` (written
  `n + 1 + 1` in Lean);
- `GeneralLinear.Mirabolic.locallyCompactSpace` for the mirabolic groups
  `GeneralLinear.mirabolic n F.Carrier` and
  `GeneralLinear.mirabolic (n+1) F.Carrier`, which are closed in these matrix
  groups.

These are facts about the supplied topology, proved in the Library; they are
not assumptions. The canonical topology of `F` is not used.

## Groups

Write `P_n = GeneralLinear.mirabolic n F.Carrier`. It is the actual subgroup of
`GL_(n+1)(F)` of invertible matrices with last row `(0, …, 0, 1)`, the group
`P_(n+1)` of Bernstein--Zelevinsky. Write
`U_n = GeneralLinear.Mirabolic.radical n F.Carrier`, the actual subgroup of
`P_n` whose first `n` columns are the corresponding identity columns. It is the
last-column radical `V` of BZ77 §3.1, isomorphic to `F^n`. These names are only
abbreviations in this text; the Lean statement uses the Library groups
directly and introduces no substitute groups.

The two acting subgroups are the Library's actual ranges:

- `GeneralLinear.Mirabolic.leviSubgroup n F.Carrier ≤ P_n`, the range of
  `g ↦ diag(g, 1)` on `GL_n(F)`, with
  `GeneralLinear.Mirabolic.leviEquiv : GL_n(F) ≃* leviSubgroup n F.Carrier`;
- `GeneralLinear.Mirabolic.successorSubgroup n F.Carrier ≤ P_(n+1)`, the range
  of `g ↦ diag(g, 1)` on `P_n`, with
  `GeneralLinear.Mirabolic.successorEquiv : P_n ≃* successorSubgroup n F.Carrier`.

## The actual Haar character

For a subgroup `U` of a locally compact topological group `G`, a proof
`hU : IsClosed (U : Set G)` and a subgroup `M` with
`hMU : M ≤ Subgroup.normalizer U`, the published character

```lean
HaarModulus.closedRestrictCharacter U hU M hMU : M →* ℝ≥0ˣ
```

sends `m` to `MeasureTheory.mulEquivHaarChar` of the continuous conjugation
automorphism `u ↦ m * u * m⁻¹` of `U` (`HaarModulus.normalizerConj`), computed
for the Borel measurable structure on `U`. Local compactness of `U` is derived
inside the wrapper from `hU`. By `HaarModulus.normalizerCharacter_smul_map`,
its value `c` at `m` satisfies `c • μ.map (u ↦ m*u*m⁻¹) = μ` for every regular
Haar measure `μ` on `U`.

The statement uses this character with:

- **First character.** `U = U_n` in `G = P_n`, closedness
  `GeneralLinear.Mirabolic.radical_isClosed`, `M = leviSubgroup n F.Carrier`
  and normalization `GeneralLinear.Mirabolic.leviSubgroup_le_normalizer`.
- **Second character.** `U = U_(n+1)` in `G = P_(n+1) ≤ GL_(n+2)(F)`,
  closedness `GeneralLinear.Mirabolic.radical_isClosed`,
  `M = successorSubgroup n F.Carrier` and normalization
  `GeneralLinear.Mirabolic.successorSubgroup_le_normalizer`.

No wrapper or renamed character is introduced; both are direct applications of
`HaarModulus.closedRestrictCharacter`.

## Statement

For every `n : ℕ`, including `n = 0`, the proposition asserts the conjunction
of two equalities of monoid homomorphisms into `ℝ≥0ˣ`:

1. `(closedRestrictCharacter U_n radical_isClosed (leviSubgroup n F.Carrier)
   leviSubgroup_le_normalizer).comp leviEquiv.toMonoidHom = T.determinantNorm n`,
   as homomorphisms `GL_n(F) →* ℝ≥0ˣ`;
2. `(closedRestrictCharacter U_(n+1) radical_isClosed
   (successorSubgroup n F.Carrier) successorSubgroup_le_normalizer).comp
   successorEquiv.toMonoidHom =
   (T.determinantNorm (n+1)).comp (GeneralLinear.mirabolic n F.Carrier).subtype`,
   as homomorphisms `P_n →* ℝ≥0ˣ`.

Here `.comp` is composition of monoid homomorphisms: the equivalence is applied
first. In values, the first equality says that for every `g ∈ GL_n(F)` the Haar
modulus of conjugation by `diag(g, 1)` on `U_n` is `|det g|_F`. The second says
that for every `g ∈ P_n` the Haar modulus of conjugation by `diag(g, 1)` on
`U_(n+1)` is `|det g|_F`, the determinant of `g` as an element of
`GL_(n+1)(F)`.

`T.determinantNorm m : GL_m(F) →* ℝ≥0ˣ` is the published character
`g ↦ |det g|_F` of `Group/GL/NormalizedCharacter`, where `|·|_F` is the
residue-normalized absolute value supplied by `T`
(`|x|_F = q^(-ord x)` with `q` the residue cardinality).

**Rank shifts.** The first equality is the interface for `Ψ⁻ : Alg P_(n+1) →
Alg G_n`; it includes `n = 0`, where it compares characters of `GL_0(F)` for the
trivial radical of `P_1`. The second is the interface for
`Φ⁻ : Alg P_(n+2) → Alg P_(n+1)`; its radical lies in `P_(n+2)` and its output
group is `P_(n+1)`, which is `P_n` in the Lean indexing. The quantifier is a
single `∀ n`, with both equalities under it.

## Convention and provenance

Bernstein--Zelevinsky (1977), §1.7, printed page 444, defines the module of an
automorphism `σ` of an l-group `U` by

> ∫_U f(σ⁻¹(u)) dμ(u) = mod_U σ · ∫_U f(u) dμ(u),

and for `g` normalizing a closed subgroup `U` writes `mod_U(g)` for the module
of `u ↦ g u g⁻¹`. The Library character has the same orientation: its defining
identity `c • μ.map σ = μ` is equivalent to `(σ⁻¹)_* μ = c • μ`, which is the
displayed formula (see `Group/HaarModulus.md`). §1.8(b) of the same page
normalizes the localization `r_{U,θ}` by `mod_U^(-1/2)`; the minus sign was
checked visually in the printed page because text extraction loses it.
§1.7 begins on printed page 443 with the transport functor of an isomorphism.
§3.1, printed page 450, defines `P_n`,
the standard embedding of `G_(n-1)` and `P_(n-1)` into `P_n`, and the radical
`V`; §3.2, printed page 451, defines `Ψ⁻ = r_{V,1}` and `Φ⁻ = r_{V,θ}`. These
localizations therefore twist by `mod_V^(-1/2)` with `mod_V` the two characters
of this statement. Registered source: `bernstein-zelevinsky-1977-induced-i`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
In this PDF printed page 443 is page 4 counted from one (zero-based index 3),
printed page 444 is page 5 (index 4), printed page 450 is page 11 (index 10),
and printed page 451 is page 12 (index 11). No erratum to these passages was
found.

The determinant formula is an internally derived comparison; BZ77 uses `mod_V`
without writing it as a determinant in these sections. The following
informal check is not part of the formal content. By
`levi_conjugate_radicalElement`, conjugation by `diag(g, 1)` sends the radical
element with last-column coordinates `v ∈ F^n` to the one with coordinates
`g v`. For an additive Haar measure `μ` on `F^n`, the image of `μ` under
`v ↦ g v` is `|det g|_F⁻¹ μ`. Hence `c • μ.map σ = μ` gives
`c = |det g|_F`, so the comparison is with `T.determinantNorm`, not its inverse.
The second equality is the same computation in rank `n + 1` for `g ∈ P_n`.

## Imports and independence

The module imports only `Langlands.Group.HaarModulus`,
`Langlands.Group.GL.MirabolicRadical` and
`Langlands.Group.GL.NormalizedCharacter`. It uses neither the block Haar-scaling
statement or proof, nor the rectangular determinant-scaling results, nor any
minus-functor construction, nor any classification or irreducibility
development.

## Not claimed

This file only states the comparison. It proves no Haar scaling, computes no
Haar measure and supplies no proof of either equality. It constructs no new
functor and no new character, and it supplies no proof of any irreducibility
theorem. It does not state the inverse-half or `rpow` corollaries, and says
nothing about exactness, iteration, plus functors, adjunctions, pairings, smooth
duality, filtrations or classification. It does not identify the modular
function of the full mirabolic group; BZ77's separate identification
`Δ_P = ν⁻¹` is outside this statement. Only the field universe `uF` occurs.
