# Unramified characters under geometric reciprocity and character-sum parameters

This is an internal helper module. It contains small constructions and
deductions from the existing Library interfaces for local reciprocity
candidates, Weil–Deligne pairs and Frobenius-semisimple parameter classes. It
makes no new literature claim. It proves neither
`FullCorrespondenceUnramifiedStatement` nor any automorphic statement.

## Linear algebra and pair equivalences (`Langlands.WeilDeligneRepresentation`)

- `lmap_add`, `aeval_lmap`: on a direct sum `⨁ i, V i`, componentwise maps
  `DirectSum.lmap` respect addition, and a polynomial evaluated at
  `DirectSum.lmap f` is the componentwise map of the polynomial evaluated at
  each `f i`. The proof is by polynomial induction, using the existing
  `lmap_mul`.
- `isSemisimple_lmap_algebraMap`: over a field, for a finite index type, the
  componentwise scalar map `x_i ↦ c_i x_i` is a semisimple endomorphism. The
  proof uses `Module.End.isSemisimple_of_squarefree_aeval_eq_zero` with the
  separable polynomial `∏ (X - a)`, where `a` runs over the distinct values
  of `c`.
- `directSumCongr`: componentwise pair equivalences `A i ≃ B i` give an
  equivalence of direct sums `directSum A ≃ directSum B`. The two families may
  have different carrier universes. The existing `directSumEquiv` needs a
  single universe. The linear equivalence is `DFinsupp.mapRange.linearEquiv`.
- `zeroMonodromyCongr`: an equivalence of finite representations is an
  equivalence of their zero-monodromy pairs, again across carrier universes.
- `monodromy_eq_zero_of_equiv`: a pair equivalent to a pair with zero
  monodromy has zero monodromy.
- `zeroMonodromyEquivOfMonodromyEqZero`: a pair with zero monodromy is
  equivalent, by the identity map, to the zero-monodromy pair on its own
  underlying representation.

## Representations (`Langlands.FiniteRepresentation`)

- `hasOpenInertiaKernel_of_isUnramified`: if a subgroup `I` acts trivially,
  the inertia kernel is the whole group, so it is open.
- `isUnramified_of_equiv`: trivial action of `I` transfers along an
  equivalence of finite complex representations, across carrier universes.
- `characterLine_representation_eq_algebraMap`: the character line of `χ`
  (in any carrier universe) acts by the scalar `χ g`.

## Reciprocity side (`Langlands.Correspondence`)

`IsGeometricReciprocity F e` contains the order relation: the normalized
order of `e` applied to a Weil element is its geometric degree. The theorems
below use that relation together with the published description
`eq_unramifiedCharacter` of an unramified quasi-character as
`a ↦ χ(ϖ)^(ord a)`, where `ϖ` is the chosen uniformizer.

- `ord_reciprocityHom`: under a geometric candidate,
  `ord (reciprocityHom F e w) = localDegreeInt F w`. The proof follows the
  existing argument `LocalFactor.RankOne.reciprocityUnits_order`.
- `weilCharacter_apply_of_isUnramified`: for unramified `χ`,
  `weilCharacter F e χ w = χ(ϖ) ^ localDegreeInt F w`.
- `weilCharacter_eq_localUnramifiedCharacter`: the same identity, stated as
  equality with the published unramified Weil character
  `Weil.Local.localUnramifiedCharacter F (χ ϖ)`.
- `weilCharacter_eq_of_isUnramified`: for unramified `χ`, the pullback is the
  same for any two geometric candidates.
- `weilCharacter_eq_one_of_mem_localInertia`: for unramified `χ`, the
  pullback is trivial on `localInertia F`, which is the kernel of the degree.
- `isCharacterSumParameter_iff_of_isGeometricReciprocity`: for a family of
  unramified quasi-characters, `IsCharacterSumParameter F e χ D` does not
  depend on the geometric candidate `e`.

## Character-sum parameters (`Langlands.Correspondence`)

- `characterSumPair F ψ`: for a finite family `ψ : ι → W_F →* ℂˣ` with
  `ι : Type`, the direct sum of the zero-monodromy character lines
  `characterLine.{uF, uP} (ψ i)`. It is a local Weil–Deligne pair with
  carrier in universe `uP`. The index lives in `Type`, so the carrier stays
  in `uP`.
- `characterSumPair_monodromy`, `characterSumPair_representation`,
  `characterSumPair_rank`: the monodromy is zero, `g` acts by the scalar
  `ψ_i(g)` on the `i`-th line, and the rank is `Fintype.card ι`.
- `characterSumPair_isFrobeniusSemisimple`: every Weil element acts
  semisimply, by `isSemisimple_lmap_algebraMap`.
- `characterSumPair_isUnramified`,
  `characterSumPair_isLocalFrobeniusSemisimpleParameter`: if every `ψ_i` is
  trivial on inertia, inertia acts trivially. The pair is then a local
  Frobenius-semisimple parameter, since its inertia kernel is everything and
  so is open.
- `characterSumClass ψ hψ`: for `r + 1` characters trivial on inertia, the
  class of `characterSumPair` as a `WeilDeligneClass.{uF, uP} F r.succPNat`.
  The rank certificate is `characterSumPair_rank`.
  `parameterForget_characterSumClass` records its underlying pair class.
- `isCharacterSumParameter_characterSumClass`: if the pullbacks
  `weilCharacter F e (χ i)` are trivial on inertia, then
  `characterSumClass` of these pullbacks satisfies
  `IsCharacterSumParameter F e χ`. The witness pair is `characterSumPair`
  itself. The required equivalence is `directSumCongr` of the inverse
  `characterLineEquiv` equivalences, which pass from the carriers of
  `FiniteRepresentation.of (characterRepresentation _)` to the universe-`uP`
  character lines.
- `exists_isCharacterSumParameter`: for a geometric candidate and unramified
  quasi-characters, a character-sum parameter class exists in every carrier
  universe `uP`.
- `parameterForget_injective`: on Frobenius-semisimple parameter classes of
  fixed rank, the underlying pair class determines the parameter class.
- `isCharacterSumParameter_unique`: for any candidate `e`, at most one class
  `D` satisfies `IsCharacterSumParameter F e χ D`.
- `isUnramifiedParameterClass_of_isCharacterSumParameter`: if the pullbacks
  are trivial on inertia, every character-sum parameter `D` satisfies
  `IsUnramifiedParameterClass F D`. The proof transports zero monodromy and
  trivial inertia action from `characterSumPair` to the witness `A` of
  `IsCharacterSumParameter`, then identifies `A` with the zero-monodromy
  pair on its underlying representation.
- `isUnramifiedParameterClass_of_isCharacterSumParameter_of_isGeometricReciprocity`:
  the same conclusion for a geometric candidate and unramified
  quasi-characters.

No continuity hypothesis is added. Frobenius-semisimplicity of the character
sum is proved, not assumed.

The parameter-forget injectivity result is shared with
`Correspondence/ZeroMonodromyExtension`; its field argument is implicit.
