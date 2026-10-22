# Actual local irreducible scalar reduction and determinant criterion

Worker 265 proves the existing `LocalWeilIrreducibleReductionFor` in
`Langlands.Weil.Local`. The closing theorem is
`Langlands.Weil.Local.localWeilIrreducibleReductionFor.{u,v}`, and its
complete unapplied type is

```lean
∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p),
  LocalWeilIrreducibleReductionFor.{u, v} F
```

The theorem covers every prime `p` and every actual finite p-adic field `F`
in universe `u`. The representation carriers lie in an independent universe
`v`. The proof adds no hypothesis to the statement. The statement pair
[RepresentationStatements.lean](RepresentationStatements.lean) and
[RepresentationStatements.md](RepresentationStatements.md) is unchanged,
and so are the pairs it imports.

## What is proved

Let `A` be a local Weil representation that is continuous and irreducible.
The theorem proves two things.

1. There are `z : ℂˣ` and a representation `B`. `B` is continuous,
   irreducible, has finite image and has actual Galois type
   (`IsLocalGaloisType F B`). There is also a genuine
   `FiniteRepresentation.Equiv` from `A` to
   `FiniteRepresentation.twist (localUnramifiedCharacter F z).toMonoidHom B`.
   `localUnramifiedCharacter F z` sends `g` to `z ^ localDegreeInt F g`.
   The constructed `B` lives on the carrier of `A`, and the equivalence is
   the identity of that carrier. So `A(g) = z ^ localDegreeInt F g • B(g)`
   for every `g`.
2. `A` has finite image exactly when there is a positive natural number `n`
   such that `det(A(g))^n = 1` for every `g` in the local Weil group.

## Implemented proof

The proof specializes the published generic theorem
`Langlands.Weil.unramifiedReduction` to the actual local data. It does this
in five steps.

**Step 1: the actual-group hypotheses.** The generic theorem is applied with
the group `localWeilGroup F` and the degree map
`(localDegree F).toMonoidHom`. By definition the kernel of this map is
`localInertia F`. The hypotheses come from
[AssemblyProof.md](AssemblyProof.md):

- `localInertia_isCompact` gives compactness of the kernel.
- `localWeilGroup_nonarchimedean` makes the whole group nonarchimedean. The
  published instance `Langlands.subgroupNonarchimedean` restricts this to the
  kernel.
- `localInertia_isOpen` shows that the kernel is open.
- `localDegree_surjective` shows that the degree map is surjective.

**Step 2: continuity on the original carrier.** The carrier of `A` gets its
coordinate norm from `A.carrierNormedAddCommGroup` and
`A.carrierNormedSpace`. The carrier itself is not replaced.
`FiniteRepresentation.isContinuous_of_iff`, from
[ContinuityBridgeProof.md](../Representation/ContinuityBridgeProof.md),
converts `A.IsContinuous` into continuity of the operator-valued map. This is
the hypothesis the generic theorem uses.

**Step 3: the generic irreducible clause.** The irreducible clause of
`unramifiedReduction`, applied to `A.representation`, supplies:

- a character `χ : localWeilGroup F →* ℂˣ` that is trivial on inertia;
- a representation `σ` on the same carrier, which is continuous, irreducible
  and has finite range;
- the equation `A.representation = Langlands.twist χ σ`;
- the determinant criterion for `A.representation`.

**Step 4: identifying the character.** `localUnramifiedCharacterClassificationFor F`,
from [CharacterNormProof.md](CharacterNormProof.md), applies to `χ` because
`χ` is trivial on inertia. It gives `z : ℂˣ` with
`(localUnramifiedCharacter F z).toMonoidHom = χ`. This `z` is the value of
`χ` at `localGeometricFrobenius F`. The proof uses only the equation of
characters.

**Step 5: building `B` and the equivalence.** Set
`B := FiniteRepresentation.of σ`.

- Continuity of `B` follows from the continuity of `σ` through
  `isContinuous_of_iff`.
- Irreducibility and finite image of `B` hold by definition: they are the
  corresponding facts about `σ`.
- Actual Galois type of `B` comes from the first clause of
  `localWeilGaloisTypeFor F B`, in
  [GaloisCorrectionProof.md](GaloisCorrectionProof.md), using continuity and
  finite image.

The equivalence is `Representation.Equiv.mk` applied to the identity linear
equivalence of the carrier of `A`. It intertwines because, for every `g`,
`A.representation g` equals the twisted operator
`Langlands.twist (localUnramifiedCharacter F z).toMonoidHom σ g`. This
follows by rewriting with the character equation and then with the generic
twist equation. The twist goes in the stated direction: `A` is the twist of
`B` by the unramified character, not the other way round.

**The determinant criterion.** `A.HasFiniteImage` is by definition
`(Set.range A.representation).Finite`. So the second conjunct is exactly the
determinant clause of the generic theorem for `A.representation`, with the
same positive natural exponent.

## Checks

`lean_check` compiles the module without warnings. The inspected axioms of the
closing theorem are only `propext`, `Classical.choice` and `Quot.sound`. A
separate private check file assigns the unapplied constant
`@localWeilIrreducibleReductionFor.{u, v}` directly to the complete
quantified type shown above, and it compiles. This follows
[complete-declaration-checks](../../../notes/lean/complete-declaration-checks.md).
The check file is not part of the contribution.

## Provenance

This proof is an internal specialization of published generic proofs. It
adds no new statement and makes no local Langlands assertion. The sources are
those already recorded in [RepresentationStatements.md](RepresentationStatements.md):

- Henniart 1980, Corollary 3 in section 2.3, with its proof in section 2.4
  (literature ID `henniart-1980-weil-representations`);
- Tate (2.2.1) (literature ID `tate-1979-number-theoretic-background`).

As in that file, the determinant criterion is a derived consequence. It is
not a separately numbered theorem in those sources.

The mathematical argument is the one in the imported
[unramified reduction proof](../Representation/UnramifiedReductionProof.md):

- a central root of a power of Frobenius;
- Schur's lemma, which makes that root a scalar;
- the determinant-under-twist formula.

The local inputs come from the actual assembly, character-classification and
Galois-type proofs listed above. Worker 265 wrote this specialization. The
generic and local results it imports are earlier Library work, used by
their Lean names.
