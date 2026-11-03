# Associated opposite transport from negation stability of relative roots

This internal module reduces the published target
`StandardAssociatedOppositeTransportStatement.{u}` to exactly one premise,
the published `RelativeRootNegationStatement.{u}`: every actual relative root
`α ∈ relativeRoots i` of a connected reductive `G` over a field, for a maximal
split torus `i`, has `-α ∈ relativeRoots i`. No other theorem-valued premise
is used. The final reduction theorem has type

```
RelativeRootNegationStatement.{u} → StandardAssociatedOppositeTransportStatement.{u}
```

so a published proof of negation stability gives the target by one
application. The module does not prove negation stability and does not prove
the target unconditionally.

Throughout, `zeta ≫ i` abbreviates `CommGroupScheme.groupHom zeta ≫ i`,
`P(·)` and `U(·)` are `Dynamic.parabolic` and `Dynamic.unipotent` as subgroup
functors on every test scheme, `Int(n)` is `G.innerIso n`, and `⟨α, η⟩` is
`latticePairing T α η`.

## The associated opposite cocharacter

For `n : normalizerPoints i` and `zeta : cocharacterLattice T`,
`associatedOppositeCocharacter i n zeta` is the cocharacter
`(cocharacterAut (normalizingAut i n)).symm (-zeta)`, that is, the unique
`ξ` whose image under the cocharacter automorphism induced by `n` is `-zeta`.
It is an auxiliary construction made from the published
`cocharacterAut` and `normalizingAut`; it has no separate literature source.

- `groupHom_cocharacterAut_associatedOppositeCocharacter`: the image of `ξ`
  under `cocharacterAut (normalizingAut i n)`, composed with `i`, is
  `Dynamic.oppositeCocharacter (zeta ≫ i)`. The proof cancels the inverse
  equivalence and applies the published
  `groupHom_neg_comp_eq_oppositeCocharacter`, which identifies `(-zeta) ≫ i`
  with the opposite of `zeta ≫ i`.
- `parabolic_oppositeCocharacter_comap_innerIso` and
  `unipotent_oppositeCocharacter_comap_innerIso`: on every test scheme,
  ```
  comap(Int(n), P(oppositeCocharacter(zeta ≫ i))) = P(ξ ≫ i)
  comap(Int(n), U(oppositeCocharacter(zeta ≫ i))) = U(ξ ≫ i).
  ```
  The proofs rewrite the opposite cocharacter with the previous lemma, use the
  published `groupHom_cocharacterAut_comp` to write the transported cocharacter
  as `ξ ≫ i` followed by `Int(n)`, and apply the published
  `Dynamic.parabolic_eq_comap_of_iso` and `Dynamic.unipotent_eq_comap_of_iso`.
- `latticePairing_associatedOppositeCocharacter`: for every character `α`,
  `⟨α, ξ⟩ = -⟨weylAction i n α, zeta⟩`. The proof is the published invariance
  `latticePairing_characterAut_cocharacterAut` of the pairing under a torus
  automorphism, together with linearity in the cocharacter; `weylAction i n`
  is by definition `characterAut (normalizingAut i n)`.

## Standardness of the associated opposite cocharacter

`isStandardCocharacter_associatedOppositeCocharacter` assumes a generic `ν`,
negation stability `∀ α ∈ relativeRoots i, -α ∈ relativeRoots i` as an
explicit hypothesis, and `IsRelativeWeylCoxeterRealization i ν cs`. Let `J` be
a finite simple-root subset, `K = associatedSubset cs J`, `n` a lift of
`longestRep cs J`, and `zeta` standard for `rootSet i ν J`. It proves that `ξ`
is standard for `rootSet i ν K`, by checking the three clauses of
`IsStandardCocharacter`.

1. `rootSet i ν K` consists of simple relative roots (`rootSet_subset`).
2. For a simple root `α` in `rootSet i ν K`, the published
   `weylAction_image_associatedStandardFamily` (with the empty subfamily)
   says that `weylAction i n` maps `rootSet i ν K` onto `rootSet i ν J`. So
   `weylAction i n α ∈ rootSet i ν J`, where `zeta` pairs to zero, and hence
   `⟨α, ξ⟩ = -0 = 0`.
3. Let `α` be a simple root `a` with `α ∉ rootSet i ν K`, so `a ∉ K`. Write
   `β = weylAction i n α`. Then:
   - `β` is a relative root, by `weylAction_mapsTo_relativeRoots`.
   - `β` is not positive. Otherwise the length clause `h.2.2.1` of the
     realization, applied to the class `longestRep cs J` of `n` (via
     `schemeWeylCharacterAction_mk`), would put `a` in
     `positiveSimpleSet cs (longestRep cs J)`. The published
     `positiveSimpleSet_longestRep` identifies that set with `K`, which is a
     contradiction.
   - Since `ν` is generic, `⟨β, ν⟩ ≠ 0`. Since `β` is not positive,
     `⟨β, ν⟩ < 0`.
   - By negation stability, `-β` is a relative root with `⟨-β, ν⟩ > 0`, so it
     is a positive relative root.
   - `-β` is not in the additive closure of `rootSet i ν J`. Every element `x`
     of that closure has `⟨(weylAction i n)⁻¹ x, ν⟩ ≥ 0`, by closure induction:
     the generators come from simple roots in `K`, whose `ν`-pairings are
     positive. But `(weylAction i n)⁻¹ (-β) = -α`, and `⟨-α, ν⟩ < 0` because
     `α` is simple.
   - The published `IsStandardCocharacter.pairing_pos_iff_not_mem_closure`
     for `zeta` then gives `⟨-β, zeta⟩ > 0`, that is,
     `⟨α, ξ⟩ = -⟨β, zeta⟩ > 0`.

## Transport for one realization

`isStandardAssociatedOppositeTransport_of_rootSigns` proves
`IsStandardAssociatedOppositeTransport i ν cs`. It assumes a generic `ν`,
negation stability, a realization `h`, and two root-sign comparisons for all
cocharacters `zeta, eta` of `T`:

- `hparabolic`: if every relative root with `⟨α, zeta⟩ ≥ 0` has
  `⟨α, eta⟩ ≥ 0`, then `P(zeta ≫ i) ≤ P(eta ≫ i)`.
- `hunipotent`: if every relative root with `⟨α, zeta⟩ > 0` has
  `⟨α, eta⟩ > 0`, then `U(zeta ≫ i) ≤ U(eta ≫ i)`.

Given `J`, `n` and a standard `zeta` for `J`, the two comap lemmas rewrite the
goal to `P_K = P(ξ ≫ i)` and `U_K = U(ξ ≫ i)`, where `P_K` and `U_K` are
`standardParabolic` and `standardUnipotent` at `rootSet i ν K`, and `ξ` is
standard for `rootSet i ν K` by the previous section.

- The parabolic equality is the published
  `dynamicParabolic_eq_standardParabolic_of_isStandardCocharacter`, applied to
  `ξ` with genericity, negation stability and `hparabolic`.
- For the radical, `U_K ≤ U(ξ ≫ i)` is the published
  `standardUnipotent_le_dynamicUnipotent`. For the reverse inclusion, by
  `mem_standardUnipotent` it suffices to show `U(ξ ≫ i) ≤ U(eta ≫ i)` for
  every `eta` standard for `rootSet i ν K`. This follows from `hunipotent`.
  Its root-sign premise is the third conclusion of the published
  `IsStandardCocharacter.root_pairing_implications_of_subset`, applied to
  `eta` and `ξ` with the same set `rootSet i ν K` (reflexive inclusion): every
  relative root positive on `ξ` is positive on `eta`.

## The reduction at full scope

`standardAssociatedOppositeTransport_of_relativeRootNegation` introduces the
field `k`, the group scheme `G` with `hG : IsConnectedReductive G`, the torus
`T`, the maximal split torus `i`, `ν`, genericity, the finite enumerations,
the Coxeter matrix, `cs`, and the realization. It installs the affine and
monomorphism instances from `hG.isAffineHom` and
`hi.isSplitSubtorus.mono`, exactly as the target statement does. The
root-sign comparisons are obtained unconditionally:
`relativeRootSignInclusions_of_connectedness dynamicConnected` gives, for
every `zeta, eta`, the parabolic equivalence (its reverse direction is used
as `hparabolic`) and the radical implication `hunipotent`. Here
`dynamicConnected` is the published proof of `DynamicConnectedStatement`.
Negation stability is the premise applied to `k, G, hG, T, i, hi`. The
previous section then concludes.

## Scope and why the premise is kept

The target statement's scope is unchanged: arbitrary fields at universe `u`,
any characteristic, connected reductive `G`, maximal split `i`, generic `ν`,
every finite Coxeter realization, every lift `n` and every standard `zeta`.
Nonreduced relative roots and the empty root set are allowed. The only added
input is the negation-stability premise.

Explanatory remark (not formalized): the realization axioms of
`IsRelativeWeylCoxeterRealization` do not by themselves force negation
stability or the transport. Take the abstract configuration on `ℤ²` with
`a = (1, 0)`, `b = (0, 1)`, roots `{a, -a, b}`, Weyl group `{1, s}` with
`s(x, y) = (-x, y)`, and `ν = (1, -1)`, so `a` is the only positive and simple
root. It satisfies the four root-theoretic realization clauses. It also
satisfies the fifth, which is defined through the group's standard Levi
points, if the standard Weyl subgroups are read as `{1}` for `∅` and
`{1, s}` for `{a}`. At `J = ∅`, `zeta = (1, -1)`
is standard, and `ξ = (1, 1)`. The roots pairing nonnegatively with every
standard cocharacter for `∅` are `{a}`, but those pairing nonnegatively with
`ξ` are `{a, b}`. So the root-level form of the parabolic equality fails.
That is why the module keeps negation stability as an explicit premise
rather than trying to derive it from the realization.
