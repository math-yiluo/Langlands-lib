# Inverting the horizontal isomorphisms of a commutative square: proof

This module proves the published closed proposition
`Langlands.NYLL.PortInternal.M086.d018Statement` (NYLL source unit M086.018,
the private theorem `ClassFormation.normResidueNaturality_symm_naturality`)
by the theorem `Langlands.NYLL.PortInternal.M086.d018`. Its only import is
the statement module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main.U018.Statements`.
The statement pair and everything it imports are unchanged.

## Exact target

The theorem has four universe parameters `u₁ u₂ u₃ u₄` and its type is
exactly `d018Statement.{u₁, u₂, u₃, u₄}`. Unfolded, it says:

```lean
∀ {Q : Type u₁} {B : Type u₂} {Q' : Type u₃} {B' : Type u₄}
  [AddCommGroup Q] [AddCommGroup B]
  [AddCommGroup Q'] [AddCommGroup B']
  (r : Q ≃+ B) (r' : Q' ≃+ B')
  (q : Q →+ Q') (b : B →+ B'),
  b.comp r.toAddMonoidHom = r'.toAddMonoidHom.comp q →
    q.comp r.symm.toAddMonoidHom =
      r'.symm.toAddMonoidHom.comp b
```

In words: if `b ∘ r = r' ∘ q` for additive isomorphisms `r, r'` and
additive homomorphisms `q, b`, then `q ∘ r⁻¹ = r'⁻¹ ∘ b`.

## Proof

After introducing the binders and the hypothesis `h`:

1. `AddMonoidHom.ext` reduces the equation to its value at an arbitrary
   `x : B`.
2. Since `r'` is injective, it suffices to show
   `r' (q (r⁻¹ x)) = r' (r'⁻¹ (b x))`; the right side is `b x` by
   `AddEquiv.apply_symm_apply`.
3. Evaluating `h` at `r⁻¹ x` (`DFunLike.congr_fun`) gives
   `b (r (r⁻¹ x)) = r' (q (r⁻¹ x))`, i.e. `b x = r' (q (r⁻¹ x))` after
   `AddEquiv.apply_symm_apply`. Its symmetric form closes the goal.

The proof uses extensionality, injectivity and the inverse identities of
additive equivalences; it introduces no new axioms. The development inspection
reports only `propext` and `Quot.sound`.

## Original correspondence

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Main.lean`
(SHA-256
`6883a1db96a9baf23b9c4f040e635f10b7732f36c558d9e0a96faa88a2da854b`),
private theorem `ClassFormation.normResidueNaturality_symm_naturality`:
docstring lines 1002–1003, signature lines 1004–1013, proof lines 1014–1022.

Adaptation changes:

- The private theorem is named `d018` in `Langlands.NYLL.PortInternal.M086`
  after its source row, and proves the published closed proposition
  instead of carrying the binders in its signature. The proof therefore
  starts with `intro`, naming the hypothesis `h` as in the source.
- After the `intro`, the tactic proof is the original one, line for line.
- The single import replaces the original imports. All other declarations
  of the source module are omitted. The docstring is adapted from the
  source docstring.

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Attribution

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
authorship line and Apache-2.0 notice, followed by a dated modification
record by Worker 56. Worker 678 reused Worker 56's complete shared draft,
revision 1 of task `049adfb5-bf58-42a9-bb88-81ed336fa442`, on
14 November 2026, checked it against the pinned original and the current
published statement, and added this draft provenance. The retained
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are unchanged.

No instance or simp attribute is installed.

The development `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled this module with zero errors
and zero warnings and confirmed the theorem's four universe parameters.
Independent semantic review and staged exact-target validation are required
for acceptance.
