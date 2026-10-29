# Character-twisted and normalized Jacquet quotients under a trivial-radical twist

This pair restates the common-character equivalence
`Langlands.Jacquet.twistActionTwistEquiv` of
`Langlands.Representation.Jacquet.CharacterTwistEquiv` for the two named
twisted Jacquet actions of the Library. The hypotheses are those of that
module: `ρ : Representation R G V`, subgroups `N M` with
`hMN : M ≤ Subgroup.normalizer N` (no normality of `N` in `G`), and an ambient
character `χ` with `hN : N ≤ χ.ker`. Representation carriers `V`, `W` have
independent universes.

## Character-twisted Jacquet action

For a commutative ring `R` and `ψ : M →* Rˣ`, the Library action
`characterTwistedAction ρ N M hMN ψ` is by definition
`twist ψ (action ρ N M hMN)`. `characterTwistedActionTwistEquiv ρ N M hMN χ hN ψ`
is the equivalence

```lean
(characterTwistedAction (twist χ ρ) N M hMN ψ).Equiv
  (twist (χ.comp M.subtype) (characterTwistedAction ρ N M hMN ψ))
```

defined as `twistActionTwistEquiv ρ N M hMN χ hN ψ`. The same `ψ` occurs on
both sides. `characterTwistedActionTwistEquiv_mk` and
`characterTwistedActionTwistEquiv_symm_mk` state that the class of `v` goes to
the class of the same `v`, in both directions. For an ambient intertwiner
`f : ρ.IntertwiningMap σ`, `characterTwistedActionTwistEquiv_naturality`,
`characterTwistedActionTwistEquiv_map_apply` and
`characterTwistedActionTwistEquiv_symm_naturality` are the commuting squares
with the Library maps `characterTwistedMap N M hMN ψ (twistIntertwining χ f)`
and `twistIntertwining (χ.comp M.subtype) (characterTwistedMap N M hMN ψ f)`,
for the equivalence and for its inverse. They are the corresponding
statements of the generic module, since `characterTwistedMap N M hMN ψ f` is by
definition `twistIntertwining ψ (map N M hMN f)`.

## Normalized Jacquet action of a supplied modulus

For complex representations and a positive character `δ : M →* ℝ≥0ˣ`, the
Library action `normalizedActionOfModulus ρ N M hMN δ` is by definition
`characterTwistedAction ρ N M hMN (inverseHalfCharacter δ)`, the descended
action scaled by the inverse positive square root of `δ`.
`normalizedActionOfModulusTwistEquiv ρ N M hMN χ hN δ`, for `χ : G →* ℂˣ`, is
the equivalence

```lean
(normalizedActionOfModulus (twist χ ρ) N M hMN δ).Equiv
  (twist (χ.comp M.subtype) (normalizedActionOfModulus ρ N M hMN δ))
```

The same literal modulus `δ` normalizes both sides; nothing identifies `δ`
with a modulus of `twist χ ρ` or of `ρ`, and no relation between `δ` and `χ` is
assumed. The definition is the common-character equivalence with
`ψ = inverseHalfCharacter δ`; `normalizedActionOfModulusTwistEquiv_eq` records
this specialization as an equation (it holds by definition). The
representative formulas are `normalizedActionOfModulusTwistEquiv_mk` and
`normalizedActionOfModulusTwistEquiv_symm_mk`. Naturality with the Library
maps `normalizedMapOfModulus N M hMN δ (twistIntertwining χ f)` and
`twistIntertwining (χ.comp M.subtype) (normalizedMapOfModulus N M hMN δ f)` is
`normalizedActionOfModulusTwistEquiv_naturality`, with the pointwise form
`normalizedActionOfModulusTwistEquiv_map_apply` and the inverse square
`normalizedActionOfModulusTwistEquiv_symm_naturality`.

All proofs are definitional or apply the corresponding generic result with
`ψ` replaced by the supplied character, because the named actions and maps
unfold to the twisted generic ones.

## Provenance and scope

This is internal algebraic infrastructure. It specializes the internal
construction of `Langlands.Representation.Jacquet.CharacterTwistEquiv` to the
Library definitions `characterTwistedAction` and `characterTwistedMap`
(`Langlands.Representation.Jacquet.SmoothTwist`) and
`normalizedActionOfModulus`, `normalizedMapOfModulus` and
`inverseHalfCharacter` (`Langlands.Representation.Jacquet.Normalized` and
`Langlands.Representation.Jacquet.PositiveCharacter`). Those definitions carry
their own literature citations; this pair imports no additional literature
result.

The pair makes no smoothness claim, does not identify the supplied `δ` with
any geometric modulus, and asserts no Weyl-branch selection, analytic continuation,
generic occurrence or equality of Jordan–Hölder multiplicities.
