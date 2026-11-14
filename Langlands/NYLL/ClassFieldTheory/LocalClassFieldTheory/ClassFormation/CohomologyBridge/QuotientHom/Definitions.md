# Additive equivalence followed by a submodule quotient map

Compose e.toAddMonoidHom with the actual submodule quotient homomorphism N.mkQ.toAddMonoidHom. This is an additive homomorphism A →+ M ⧸ N, where N is a ℤ-submodule of M.

## Pinned source and attribution

Naganori Yamaguchi (assisted by OpenAI Codex), `n-yamaguchi-0729/ClassFieldTheory`, commit `fbd320cd8b1b06487c58227e92eb135794267709`, `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/CohomologyBridge.lean`. Registered original `external-lean-reuse-snapshots-2026-10-21`, content fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The retained original file SHA-256 is `97f7d1f21d8bf5cb2fa787caba600d6820c4be4d91e00d1ebe4f89b89f29830b`. The readable snapshot is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

The original copyright/Apache-2.0/author header is retained in the Lean file. The unchanged original license and notices are `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. Worker 194 made the extraction and adaptations recorded below on 14 November 2026.

## Exact source correspondence

| Source unit and lines | Original declaration | Published declaration |
| --- | --- | --- |
| M114.003, 80–83 | `LocalClassFieldTheory.additiveEquivToQuotientHom` | `Langlands.NYLL.PortInternal.M114.d003` |

Line ranges include each complete original declaration and any original proof; only its signature and proposition are retained for a statement target. The definition names above denote the constructions themselves. The statement names above denote propositions, without proofs of those propositions.

## Telescope, construction and modifications

Both implicit parameters A and M are Type, hence Type 0; the source is not universe-polymorphic here. Preserve the following AddCommGroup A and AddCommGroup M instances and explicit e and N binders, in that order. The ambient K/L field variables, CategoryTheory opens and concrete Galois representations do not occur in this source command. The source-private command is made available under the required implementation name Langlands.NYLL.PortInternal.M114.d003; this is not the original mangled private kernel name. The body is unchanged.

The source namespace is adapted to the namespace displayed in the name table. Original whole-module imports are replaced by these focused imports:

- `Mathlib.LinearAlgebra.Quotient.Basic`

Each theorem is changed to a `def` returning `Prop`: the full ordered telescope is retained, and the source conclusion becomes its body. Source theorem proofs and theorem attributes are omitted. Construction bodies and any proof terms inside them are unchanged apart from resolving source names to their published adaptations. Documentation comments are replaced with focused unit labels; unrelated source declarations and unused opens are omitted. No new global or local instance is declared. These support units assert no host class-formation, cup, transfer, Tate or reciprocity comparison.

## Lean declarations

The following is the exact authored declaration content, in its declared namespace and context.

```lean
noncomputable section

/-- Source M114.003: original construction. -/
def d003
    {A M : Type} [AddCommGroup A] [AddCommGroup M]
    (e : A ≃+ M) (N : Submodule ℤ M) : A →+ M ⧸ N :=
  N.mkQ.toAddMonoidHom.comp e.toAddMonoidHom
```
