# Unipotent Haar measure under character-change conjugation

Author: Worker 234.

This module states a proposition. It does not prove it. The proposition
`Langlands.RankinSelberg.UnipotentCharacterChangeModulusStatement` says how
the actual integral-normalized Haar measure on the upper-unipotent subgroup
`N = N_(n+1)(F)` changes under conjugation by the character-change diagonal.
It is the subgroup Jacobian that the quotient law
`CharacterChangeCompatibleMeasureStatement` needs as input. The module also
proves two small helper theorems, described below, about the map itself.

## Provenance

This is an internal statement built from existing Library constructions. It
is not a transcription of a literature theorem, and it cites no new source.
Every ingredient is used under its published name:

- `Representation/Whittaker/CharacterChange` defines the diagonal
  `characterChangeElement a n = d_a = diag(a^n, a^(n-1), ..., a, 1)` in
  `GL_(n+1)(F)` and the conjugation monoid homomorphism
  `Whittaker.characterChangeConj a n : N →* N`, `u ↦ d_a u d_a⁻¹`. Its
  theorem `characterChangeElement_conj_apply` computes the entries of the
  conjugate.
- `Representation/RankinSelberg/CharacterChange` defines
  `characterChangeRootExponent n` and
  `characterChangeModulus abv a n = abv(a)^(characterChangeRootExponent n)`,
  a value in `ℝ≥0`, and proves that this modulus is nonzero.
- `Representation/RankinSelberg/AnalyticStatement` defines
  `normalizedAbsoluteValue T`, the absolute value whose values are those of
  `T.normalizedAbs`. Thus `|x| = q^(-ord x)` for `x ≠ 0`, where `q` is
  `T.residueCardinality`, so a uniformizer has absolute value `q⁻¹`
  (`LocalField/Normalization/Proof`, `normalizedAbs_uniformizer`).
- `Representation/RankinSelberg/Measures` defines
  `unipotentHaar F n`. It is Mathlib's `Measure.haarMeasure` on `N`, with
  the compact open subgroup `unipotentIntegralOpen F n` of mass one. That
  subgroup is the inverse image in `N` of the level-zero subgroup
  `GL_(n+1)(O_F)`, so it consists of the elements of `N` that lie in
  `GL_(n+1)(O_F)`. This is a left Haar measure. Its right invariance is proved
  separately in `RankinSelberg/UnipotentUnimodularity` and is not used
  here.

The task that requested this statement records it as the missing subgroup
prerequisite for the published quotient target
`CharacterChangeCompatibleMeasureStatement`
(`RankinSelberg/CharacterChangeMeasureStatement`). That statement's
Markdown already names the identity `(C_a)_* ν_N = c⁻¹ ν_N` as a separate
proof obligation. This module states that obligation as its own target.

## Exact scope

`UnipotentCharacterChangeModulusStatement.{uF}` is a closed proposition
definition. Its only universe parameter is the field-carrier universe `uF`.
It quantifies over:

- every prime natural number `p`, with its `Fact p.Prime` instance;
- every `F : PadicField p`, whose carrier lies in the arbitrary universe
  `uF`;
- every actual `T : F.TopologicalData`;
- every natural number `n`. The matrix rank is `n + 1`, so rank one
  (`n = 0`) is included;
- every unit `a : F.Carrierˣ`.

Inside the statement, `T.topology`, `T.valuativeRel` and `T.localField` are
installed as instances. The subgroup `upperUnipotent (n + 1) F.Carrier`
carries the subspace topology of `GL_(n+1)(F)`, which has the units
topology of the matrix space over this field topology. The statement
installs the Borel σ-algebra of that topology on the subgroup, together
with the `BorelSpace` instance that records the equality. No other
measurable structure is used, and no topology, normalization or measure is
supplied as a hypothesis. The general linear group and the quotient
`N \ GL_(n+1)(F)` receive no measurable structure, since neither occurs.

There are no other hypotheses. In particular, no Jacobian, coordinate
identification of `N` with a product of copies of `F`, product form of the
Haar measure, uniqueness theorem or integral identity is assumed.

The conclusion is

```text
Measure.map (characterChangeConj a n) (unipotentHaar F.Carrier n)
  = ((characterChangeModulus (normalizedAbsoluteValue T) a n : ℝ≥0∞)⁻¹)
      • unipotentHaar F.Carrier n.
```

Write `c = characterChangeModulus (normalizedAbsoluteValue T) a n`. Then
`c = |a|^E` with

```text
E = characterChangeRootExponent n = sum over 0 ≤ i < j ≤ n of (j - i).
```

The modulus `c` is a positive real number. Its coercion to `ℝ≥0∞` is
therefore neither zero nor infinity, so `c⁻¹` is the ordinary positive
real inverse. As a check, `E` is `0`, `1` and `4` for `n = 0, 1, 2`. In
rank one, the diagonal is the identity, `N` is trivial and `c = 1`.

## Why the subgroup factor is `c⁻¹`

By `characterChangeElement_conj_apply`, the `(i,j)` entry of
`d_a u d_a⁻¹` is `a^(n-i) u_ij a^(-(n-j)) = a^(j-i) u_ij`. In the
coordinates `(u_ij)_(i<j)`, conjugation is therefore the linear dilation
`D` that multiplies the `(i,j)` coordinate by `a^(j-i)`. For an additive
Haar measure `λ` on a single coordinate, `λ(bS) = |b| λ(S)` with the
normalized absolute value. Hence `D` multiplies volumes by
`prod_(i<j) |a|^(j-i) = c`.

A pushforward evaluates the measure on preimages:
`(D_* ν)(S) = ν(D⁻¹(S))`. The preimage `D⁻¹(S)` is the image of `S` under
`D⁻¹`, which multiplies volumes by `c⁻¹`. So the pushforward of a
coordinate Haar measure along a dilation with volume factor `c` is `c⁻¹`
times that measure. For example, when `n = 1`, the map is `x ↦ a x` on
`F`, and `(x ↦ a x)_* dx = |a|⁻¹ dx`.

This coordinate computation explains the proposed factor only. The Lean
statement makes no reference to coordinates on `N` or to product measures.
`Measures` explicitly leaves compatibility of `unipotentHaar` with product
coordinates separate. Establishing the identity for the actual normalized
measure is the content of a future proof. The identity is linear in the
measure, so the mass-one normalization does not affect it. Its statement for
the actual measure is still the target here.

## Why the quotient factor is `c`

The published quotient target `CharacterChangeCompatibleMeasureStatement`
asserts the opposite factor:

```text
Measure.map (characterChangeQuotient a n) μ = c • μ
```

for every quotient measure `μ` on `N \ GL_(n+1)(F)` compatible with the
actual Haar measures `ν_G` and `ν_N`. The two directions are consistent.
Write `A f(N g) = ∫_N f(u g) dν_N(u)` for the orbital average, and
`C_a = characterChangeConj a n`. If `(C_a)_* ν_N = c⁻¹ ν_N`, then

```text
A(f ∘ L_(d_a))(N g) = ∫_N f(d_a u g) dν_N(u)
                    = ∫_N f(C_a(u) d_a g) dν_N(u)
                    = c⁻¹ A f(N d_a g).
```

Left invariance of `ν_G` and the compatibility identity then give
`c⁻¹ ∫ A f(T_a q) dμ(q) = ∫ A f(q) dμ(q)`, where
`T_a = characterChangeQuotient a n`. The quotient pushforward therefore
has factor `c`, not `c⁻¹`. The Markdown of
`RankinSelberg/CharacterChangeMeasureStatement` gives the same calculation.

## What this module does not claim

- It proves neither this proposition nor the quotient law. It assumes
  neither of them, and it proves no implication between them.
- It is not the quotient statement. The quotient statement concerns
  `characterChangeQuotient` and compatible quotient measures. This one
  concerns `characterChangeConj` and the subgroup measure `unipotentHaar`.
  Deriving the quotient law from this subgroup law also needs the lifting
  and uniqueness arguments described in that module's Markdown.
- It is not `Langlands.GLBlockModulusHaarStatement`
  (`Group/GL/BlockModulusHaarStatement`). That proposition concerns Levi
  conjugation on the block unipotent radical `B.unipotentRadical`, a
  subgroup of the block parabolic, with the explicit `T.leviModulus B`. It
  is itself an unproved statement. This module neither uses nor assumes it.
  A future proof that specializes it to the shape of `n + 1` blocks of
  size one would still have to identify the subgroup, the map, the measure
  and the modulus with the ones used here.
- It changes no published topology, normalization, Haar measure, quotient
  or compatibility definition.

## Helper theorems

Two proved helpers concern the map only.

- `continuous_characterChangeConj a n` holds for any field `F` with a
  topological ring structure. It says that `characterChangeConj a n` is
  continuous for the subspace topology on `N`. Conjugation by a fixed
  element is continuous on `GL_(n+1)(F)`, and its values lie in `N`.
- `measurable_characterChangeConj a n` holds for any measurable structure
  on `N` that is the Borel σ-algebra of that topology. It says that
  `characterChangeConj a n` is measurable.

Mathlib's `Measure.map f μ` is the pushforward of `μ` only when `f` is
almost everywhere measurable for `μ`. Otherwise it takes a conventional
value: the zero measure if `μ = 0`, and an arbitrary Dirac measure if
`μ ≠ 0` (`Measure.map_of_not_aemeasurable_of_ne_zero` in the pinned
Mathlib). Under the installed Borel structure, the second helper shows that
`C_a = characterChangeConj a n` is measurable, so this fallback never
applies here. With `ν = unipotentHaar F.Carrier n`, Mathlib's
`Measure.map_apply` then gives `(Measure.map C_a ν)(S) = ν(C_a⁻¹(S))` for
every measurable set `S`. Neither helper is a hypothesis of the
proposition.
