# Proof of fixed-vector generation of actual Jacquet coinvariants

Worker 189. The theorem `Langlands.Jacquet.fixedVectorsGeneration` proves
`Langlands.Jacquet.FixedVectorsGenerationStatement.{uR,uG,uV}` with independent
coefficient, group, and carrier universes. Every hypothesis of that proposition
is introduced explicitly. There is no topology or finite-dimensionality premise.

The implementation uses the actual quotient `Jacquet.Coinvariants ρ N`,
the surjective quotient map `Jacquet.mk ρ N`, and the descended action
`Jacquet.action ρ N M hMN`.

First, `apply_mem_fixedVectors_of_mem_normalizer` shows that `ρ(k)` preserves
`K`-fixed vectors when `k` normalizes `K`. For `a ∈ K`, normality puts
`k⁻¹ a k` in `K`. Hence
`ρ(a) ρ(k) v = ρ(k) ρ(k⁻¹ a k) v = ρ(k) v`.

Next, let `S` be a Jacquet subrepresentation containing all its fixed vectors
under `K.comap M.subtype`. For `v` fixed by `K`, factor `g = m n k` using the
given algebraic hypothesis. The preceding observation makes `ρ(k)v` fixed
by `K`. The published `fixedJacquetMap` puts its class in the fixed-vector
space contained in `S`. The quotient kills the `N`-action and intertwines the
`M`-action, giving

```text
q(ρ(g)v) = Jacquet.action(m)(q(ρ(k)v)) ∈ S.
```

This is `mk_translate_mem_of_fixedVectors_le`.

For the main deduction, form the subrepresentation `C` of the ambient
representation with underlying scalar submodule

```text
⋂ g ∈ G, (q ∘ ρ(g))⁻¹(S).
```

It is invariant because `q(ρ(a)(ρ(g)v)) = q(ρ(a g)v)`. The previous step
shows that `C` contains all `K`-fixed vectors. The ambient generation
hypothesis therefore gives `C = ⊤`. Every Jacquet vector has a lift `v`
by surjectivity of `q`. The condition defining `C` at `g = 1` puts `q(v)`
in `S`, so `S = ⊤`. The proof includes the zero representation.

The mathematical source is the lemma in Renard VI.6.3, printed page 178 /
PDF184, in the French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The actual structural hypotheses are supplied explicitly here, as explained
in the statement Markdown. This proves its algebraic core; the module does
not construct the source's special compact subgroup or Iwasawa factorization.

The intersection-subrepresentation implementation is adapted from Worker 187's
published `JacquetFiniteGeneration.finite_of_compactQuotient` in
`Langlands.Representation.Aubert.General.JacquetFiniteGeneration`. Its paired
Markdown credits the route to Workers 319 and 238; this implementation retains
that attribution. That published result has a different conclusion and is not
used as a finite-generation or finite-length hypothesis.

The proof makes no claim about normalized Jacquet fixed vectors,
supercuspidal subquotients, subquotient generation, or Howe's theorem itself.
In particular, it does not discharge the actual rational-point structural or
representation-theoretic inputs of the final Howe target.
