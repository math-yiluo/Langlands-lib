# Renard A.VI.3: the numerical length of a finite-length object

This module defines the length of a finite-length object from David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, Appendix A.VI.3, printed page 263 / PDF page 269.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The full source page was read. After the Jordan–Hölder assertion, the source
calls an object of finite length when it admits a composition series and
defines its length to be the length of one of those series.

The existing constructions and their source comparison are in
[CompositionChains.md](CompositionChains.md); the published Jordan–Hölder
proof and its implemented route are in [JordanHolder.md](JordanHolder.md).
The chain convention uses the `n` successive factors `B_{i+1}/B_i`, repairing
the printed factor-index range as explained in `CompositionChains.md`.
The current Appendix A discrepancy note
`notes/renard/appendix-a-corrections.md` has no additional correction to this
length definition. The older 2010-edition errata, PDF pages 18–19, were checked
in the source audit recorded in `CompositionChains.md`; they do not alter this
definition and do not replace the governing 2026 edition.

All declarations are in `Langlands.Renard`. The ambient assumptions are
`C : Type u`, `[Category.{v} C]` and `[Abelian C]`, with independent object and
morphism universes. They are the assumptions at the start of A.VI.3. The
Grothendieck and local-finite-type assumptions introduced later on the same
page are not needed here.

`compositionLength (X : C) (hX : IsFiniteLength X) : ℕ` chooses the natural
number witness in the published predicate
`IsFiniteLength X = ∃ n, HasCompositionChainOfLength X n`.
It is noncomputable. Its domain explicitly requires finite length; it assigns
no natural-number value to an object without a composition chain.
`hasCompositionChainOfLength_compositionLength` is the specification of this
choice and supplies a chain of the chosen length.

The short intrinsic laws establish the intended meaning of the construction:

- `compositionLength_eq_of_chain hX c` says that its value equals `n` for
  every actual `c : CompositionChain X n`. The proof obtains a chain of the
  chosen length and applies the equal-length component of the imported theorem
  `jordanHolder C` to that chain and `c`.
- `compositionLength_eq_iff hX n` says that the value is `n` exactly when
  `HasCompositionChainOfLength X n`. The forward implication uses the chosen
  chain; the reverse implication uses the preceding equality.
- `compositionLength_proof_irrel X hX hX'` says that changing the supplied
  finite-length proof does not change the value. It follows by Lean's proof
  irrelevance (`rfl`). Independence of the actual chain is the separate
  Jordan–Hölder argument above.
- `compositionLength_eq_zero_iff hX` says that the value is zero exactly when
  `IsZero X`. It combines the characterization by chain length with the
  published `hasCompositionChainOfLength_zero_iff`. Thus the zero object has
  length zero, using its length-zero chain, and a nonzero finite-length object
  has nonzero length.

These laws are intrinsic specifications and consequences of the definition,
grouped with it under the parent task's construction boundary. The module
imports the existing Jordan–Hölder proof; it does not reprove that source
theorem. It does not construct a multiset of composition factors or establish
length additivity, invariance under isomorphism, or representation-specific
comparisons. It makes no claim of completing A.VI.3, Appendix A or the book.
