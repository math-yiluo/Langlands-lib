# Centralizers of cocharacters orthogonal to one root

Authors: Worker 4896.

This internal supporting module is used by the proof of
`Langlands.GroupScheme.RankOneLeviFactorExistenceStatement`
(module `Langlands.GroupScheme.SimplyConnected.RankOneLeviFactorExistenceProof`).
It works over every field `k : Type u`, in arbitrary universe `u`. It adds no
hypothesis and no proposition-valued parameter beyond those stated below.

Throughout, `S` is a commutative group scheme over `Spec k`, `G` a group
scheme, `i : S.toGrp ⟶ G` a homomorphism, and `⟨χ, ζ⟩` denotes
`latticePairing S χ ζ`.

## The orthogonal cocharacter

`IsSplitTorus.exists_rootOrthogonalCocharacter` assumes that `S` is a split
torus and that `G` is affine and locally of finite type. For every character
`α` and cocharacter `ν` of `S` it gives a cocharacter `ζ₀` with

- `⟨α, ζ₀⟩ = 0`, and
- `⟨α, ν⟩ • β = ⟨β, ν⟩ • α` for every relative root `β ∈ relativeRoots i`
  with `⟨β, ζ₀⟩ = 0`.

When `⟨α, ν⟩ ≠ 0`, the second clause says that every relative root
vanishing on `ζ₀` is a rational multiple of `α`.

Proof. For each relative root `β` put
`dev β = ⟨α, ν⟩ • β - ⟨β, ν⟩ • α`. The set of nonzero values of `dev` on the
finite set `relativeRoots i` (`IsSplitTorus.finite_relativeRoots`) is finite,
so `IsSplitTorus.exists_pairings_ne_zero` gives a cocharacter `μ` pairing
nontrivially with all of them. Take `ζ₀ = ⟨α, ν⟩ • μ - ⟨α, μ⟩ • ν`. Then
`⟨α, ζ₀⟩ = 0` by bilinearity, and `⟨β, ζ₀⟩ = ⟨dev β, μ⟩` for every `β`. So if
`⟨β, ζ₀⟩ = 0` then `dev β` is not one of the characters avoided by `μ`, that
is `dev β = 0`.

`latticePairing_eq_zero_of_smul_eq`: if `⟨α, ν⟩ ≠ 0`,
`⟨α, ν⟩ • β = ⟨β, ν⟩ • α` and `⟨α, ζ⟩ = 0`, then `⟨β, ζ⟩ = 0`. Pair the
identity with `ζ` and cancel the nonzero integer `⟨α, ν⟩`.

## Centralizer comparison

`dynamicCentralizer_le_of_rootOrthogonal` assumes that `G` is smooth, affine
and connected and that `S` is split. Given `⟨α, ν⟩ ≠ 0`, a cocharacter `ζ₀`
with the second property above, and a cocharacter `ζ` with `⟨α, ζ⟩ = 0`, it
proves

```
Dynamic.centralizer (CommGroupScheme.groupHom ζ₀ ≫ i) ≤
  Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)
```

on every test scheme. It applies the published
`dynamicCentralizer_le_of_root_zero_imp`, with its connectedness input supplied
by the published theorem `dynamicConnected`. That theorem needs every relative
root vanishing on `ζ₀` to vanish on `ζ`, which is
`latticePairing_eq_zero_of_smul_eq`.

## Roots of the centralizer

Now let `G` be affine and locally of finite type, let `l : L ⟶ G` represent
`Dynamic.centralizer (CommGroupScheme.groupHom ζ₀ ≫ i)` with `L` affine, and let
`iL : S.toGrp ⟶ L` satisfy `iL ≫ l = i`. These results adapt the
selected-root argument of the published module
`Rational.StandardLeviLieWeights` from a standard Levi subgroup to the
centralizer of the single cocharacter `ζ₀`.

- `weightSpace_le_range_of_pairing_eq_zero`: if `⟨β, ζ₀⟩ = 0`, the weight
  space `weightSpace i β` lies in the image of the differential of `l`. A
  vector of weight `β` for `S` has weight `ζ₀ ≫ β = 0` for the cocharacter
  (`weightSpace_le_comp`). The centralizer clause of the published
  `dynamicLie` puts its dual-number point in the centralizer of `ζ₀`, and
  `SubgroupFunctor.IsRepresentedBy.mem_range_lieKernelHomLinear` lifts it
  through `l`.
- `map_weightSpace_of_pairing_eq_zero`: under the same hypothesis the
  differential of `l` maps `weightSpace iL β` onto `weightSpace i β`. One
  inclusion is `lieKernelHomLinear_mem_weightSpace`, the other the previous
  lemma together with `lieKernelHomLinear_mem_weightSpace_iff`.
- `mem_relativeRoots_of_pairing_eq_zero`: every `β ∈ relativeRoots i` with
  `⟨β, ζ₀⟩ = 0` lies in `relativeRoots iL`. A zero weight space in `L` would
  map to a zero weight space in `G`.

## Provenance

The module is an internal derived construction from the published Library
interfaces named above; it invokes no new source assertion. The linear
algebra is the standard choice of a cocharacter that is generic in the
hyperplane orthogonal to a root.
