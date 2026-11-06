# Associated standard groups and ambient opposite groups: proof

Worker 1068.

`Langlands.GroupScheme.standardAssociatedOppositeTransport.{u}` proves exactly
the unchanged `StandardAssociatedOppositeTransportStatement.{u}`. Let `k : Type u`
be a field of any characteristic, `G` a connected reductive group scheme over
`Spec k`, `i : T.toGrp ⟶ G` a maximal split torus, and `ν` a generic cocharacter.
Take any finite enumerations of the actual simple relative roots and of the
actual relative Weyl group, and any Coxeter system `cs` with
`IsRelativeWeylCoxeterRealization i ν cs`. Then
`IsStandardAssociatedOppositeTransport i ν cs` holds. Explicitly, take a finite
simple-root subset `J` and put `K = associatedSubset cs J`. Let
`n : normalizerPoints i` be a lift of `longestRep cs J`, and let `zeta` be a
cocharacter standard for `rootSet i ν J`. Then, as subgroup functors on every
test scheme,

```
standardParabolic (rootSet i ν K) = comap(Int(n), Dynamic.parabolic(oppositeCocharacter(zeta ≫ i)))
standardUnipotent (rootSet i ν K) = comap(Int(n), Dynamic.unipotent(oppositeCocharacter(zeta ≫ i))).
```

Here `zeta ≫ i` means `CommGroupScheme.groupHom zeta ≫ i`, and `Int(n)` is
`G.innerIso n`. The proof adds no hypothesis. In particular it does not assume
splitness or quasi-splitness of `G`, reduced relative roots, a nonempty root
set, or reduced test schemes.

## Implemented proof

The theorem applies one published result to another:

- `standardAssociatedOppositeTransport_of_relativeRootNegation`, from
  `Langlands.GroupScheme.Rational.StandardAssociatedOppositeTransportReduction`.
  It has type
  `RelativeRootNegationStatement.{u} → StandardAssociatedOppositeTransportStatement.{u}`.
- `relativeRootNegation : RelativeRootNegationStatement.{u}`, from
  `Langlands.GroupScheme.Rational.RelativeRootNegationProof`. It says that for
  every such `k`, `G` and `i`, each `α ∈ relativeRoots i` has
  `-α ∈ relativeRoots i`.

The reduction module explains its proof in its own Markdown. In outline:

1. Define the associated opposite cocharacter
   `ξ = associatedOppositeCocharacter i n zeta`, which is
   `(cocharacterAut (normalizingAut i n)).symm (-zeta)`. Pulling back the
   dynamic parabolic and radical of `oppositeCocharacter (zeta ≫ i)` along
   `Int(n)` gives `Dynamic.parabolic (ξ ≫ i)` and `Dynamic.unipotent (ξ ≫ i)`,
   on every test scheme.
2. `ξ` is standard for `rootSet i ν K`. This uses the length clause of the
   realization, the published `weylAction_image_associatedStandardFamily` and
   `positiveSimpleSet_longestRep`, genericity of `ν`, and negation stability. Negation stability is used for a simple root `α` not in
   `rootSet i ν K` with image `β = weylAction i n α`: it makes `-β` a positive
   relative root, which then pairs positively with `zeta`.
3. The parabolic and radical root-sign comparisons come from the published
   `relativeRootSignInclusions_of_connectedness`, applied to the published
   `dynamicConnected`. With them, the parabolic equality follows from the
   published `dynamicParabolic_eq_standardParabolic_of_isStandardCocharacter`.
   The radical equality follows from `standardUnipotent_le_dynamicUnipotent`
   and `mem_standardUnipotent`.

Its only premise, negation stability, is discharged here by
`relativeRootNegation`. As its Markdown explains, that proof first treats a
split maximal torus. For a root `α` it passes to the connected reductive
centralizer of a generic cocharacter in the kernel of `α` and applies rank-one
negation there (`RootReducedness.neg_mem_roots_of_rankOne`). For a general
maximal split torus it then extends to a maximal torus, splits it over a field
extension, and descends the opposite root along splitting-field restriction.

## Sources and provenance

The target statement is internal; its Markdown explains its role in the
associated-Levi contragredient comparison. This module makes no new
original-literature claim. Worker 1068 wrote the reduction module and this
assembly. The negation proof is by Worker 1310 and its credited coauthors. Both
are imported from the Library by Lean name, and no statement pair is changed.
The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
