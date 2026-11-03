# A normalizing point lies in `P_J(k)` exactly when its class lies in `W_J`

This module proves the published target
`Langlands.GroupScheme.NormalizerStandardParabolicStatement.{u}` from
`Langlands.GroupScheme.Rational.TitsStandardParabolicStatement`, as the theorem

```lean
theorem normalizerStandardParabolicStatement : NormalizerStandardParabolicStatement.{u}
```

It keeps the target's full scope: any universe `u`, any field `k`, a connected reductive
`G` over `Spec k`, a maximal split torus `i : T ⟶ G`, a generic cocharacter `ν`, a set
`J ⊆ simpleRelativeRoots i ν` and a normalizing point `n : normalizerPoints i`. For these,
`(n : G(k)) ∈ standardParabolicPoints i ν J` holds if and only if
`QuotientGroup.mk n ∈ standardRelativeWeylGroup i ν J`.

## Proof

After introducing the data, the proof installs the two instances the statement's `haveI`s
supply: `IsAffineHom G.X.hom` from `hG.isAffineHom` and `Mono i` from
`hi.isSplitSubtorus.mono`. The two directions are already-proved lemmas.

- `→`: `IsSplitSubtorus.mk_mem_standardRelativeWeylGroup` (module
  `Langlands.GroupScheme.Rational.NormalizerParabolicPoints`), applied to
  `hi.isSplitSubtorus`. It needs only that `i` is a split subtorus. `P_J(k)` is cut out by
  the dynamic parabolics `P_G(ζ)` of a family of cocharacters `ζ` of `T`, and `L_J(k)` by
  their centralizers. A normalizing point in `P_G(ζ)` centralizes `ζ`
  (`IsSplitSubtorus.mem_centralizer_of_mem_parabolic`), because the power map `t ↦ t ^ m` of
  `𝔾_m` extends to `𝔸¹` only for `m = 0`. So the point lies in `L_J(k)`, and by
  `mem_standardRelativeWeylGroup_iff` its class lies in `W_J`.
- `←`: `coe_mem_standardParabolicPoints_of_mk_mem` (module
  `Langlands.GroupScheme.Rational.TitsStandardParabolic`). A class in `W_J` has its
  representative in `L_J(k) ⊆ P_J(k)`.

Neither direction uses the generic-cocharacter hypothesis or `J ⊆ simpleRelativeRoots i ν`.
They hold for every cocharacter `ν` and every set `J` of characters.

## Source

Borel–Tits (1965) 5.15 (printed p.100: the cells `P_k w P_k` are disjoint) and 5.17 (printed
p.101: `P_Θ,k = P_k W_Θ P_k`) give the source statement for `J = Θ`. The Lean proof does not
follow that route through the Bruhat decomposition. It argues directly through the
centralizer of the cocharacter, as above, so it assumes no Bruhat or Tits-system result.
