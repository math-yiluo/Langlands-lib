# Jacquet's lemma for compact open subgroups with an Iwahori decomposition: proof

Module: `Langlands.Representation.Exponents.RepresentedJacquetLemmaProof`.

This module proves the proposition
`Langlands.Aubert.General.RepresentedParabolic.RepresentedJacquetLemmaStatement.{u, v}`
(module `Langlands.Representation.Exponents.RepresentedIwahoriDecompositionStatements`) as

```text
Langlands.Aubert.General.RepresentedParabolic.representedJacquetLemma :
  RepresentedJacquetLemmaStatement.{u, v}
```

The statement is Renard 2026, VI.6.1 Théorème (printed p.176 / PDF p.182), for an arbitrary
actual rational parabolic `P = MN` with an opposite `P̄ = M N̄` and a compact open subgroup
`K` with the ordered decomposition `K = (K ∩ N̄(F)) (K ∩ M(F)) (K ∩ N(F))`. For every
admissible complex representation `ρ` of `G(F)` on `V`, the Jacquet quotient map
`Jacquet.fixedJacquetMap ρ N(F) M(F) _ K` from `V^K` to the `K ∩ M(F)`-fixed vectors of
`V_N` is surjective. The proof adds no hypothesis and keeps all data of the statement.
Only the axioms `propext`, `Classical.choice` and `Quot.sound` are used.

It imports the companion module
`Langlands.Representation.Exponents.RepresentedIwahoriContractionProof`, which proves
`RepresentedIwahoriContractionStatement` as `representedIwahoriContraction`.

## Proof

After introducing the data, the proof installs `IsAffineHom G.X.hom` (from `hG`) and the
point topology on `G(F)`, as in the statement.

1. **A split component of `M`.** `M` is connected reductive (the field
   `isConnectedReductive` of `IsRationalLeviSubgroup m`). The first clause of the published
   `splitComponentStatement` (module `Langlands.GroupScheme.Rational.SplitComponentProof`)
   gives a commutative group scheme `A` and a split component `a : A.toGrp ⟶ M`.
2. **A compatible root presentation.** The published
   `parabolicRootPresentationExistence` (module
   `Langlands.GroupScheme.Rational.ParabolicRootPresentationProof`), applied to `G`, `hG`,
   `p`, `m`, `a` and the facts that `p` is parabolic, `m` is a rational Levi subgroup and `a`
   is a split component, gives some `pres : ParabolicRootPresentation p m a`.
3. **A contracting element.** `representedIwahoriContraction`, applied to all data of the
   statement and to `A`, `a`, `pres`, gives a point `t₀ ∈ A(F)` in `A^{++}` (part (i)). Part
   (ii) at this `t₀` gives `r₀` such that, for every `r ≥ r₀`, the image of `t₀ ^ r` in
   `G(F)` satisfies `Jacquet.IsIwahoriContraction K N(F) M(F) N̄(F)`. The proof uses
   `r = r₀`.
4. **Weak Jacquet lemma.** The published
   `Jacquet.fixedJacquetMap_surjective_of_iwahoriContraction` (module
   `Langlands.Representation.Jacquet.IwahoriContractionAdmissibility`) proves surjectivity of
   `fixedJacquetMap ρ N M hMN K` for a smooth `ρ`, a compact open subgroup `K`, an element
   satisfying `IsIwahoriContraction K N M N̄`, a proof `hMN` that `M` normalizes `N`, and
   finite dimensionality of `V^K`. The inputs are:
   - smoothness of `ρ`: the first component of `Langlands.IsAdmissible ρ`;
   - compactness of `K`: the hypothesis of the statement;
   - the contraction: step 3;
   - `hMN = pointImage_le_normalizer p m n hn`, the same proof term as in the statement, so
     the map is literally the one of the statement;
   - finite dimensionality of `V^K`: the second component of `Langlands.IsAdmissible ρ`
     at the open subgroup `K` (`Module.Finite ℂ`, which is `FiniteDimensional ℂ`).

## Relation to the literature

Renard's proof of VI.6.1 has two parts. First it chooses `t ∈ C_A^{++}` and uses the
contraction properties of V.5.2 for `K`. Then it argues with `K`-averages: `π_N(t)` maps
`j(V^K)` into itself (formula VI.6.1.1), and onto it because `j(V^K)` is finite dimensional
and `π_N(t)` is invertible. Given `v̄ ∈ (V_N)^{K_M}`, take a `K ∩ M`-fixed lift `v` of `v̄`
and `m ∈ ℕ` such that `v` is fixed by `t^{-m} (K ∩ N̄) t^m`. Then `π(t^m) v` is fixed by
`K ∩ N̄`, and its `K`-average maps to `π_N(t^m) v̄`, so `v̄ ∈ π_N(t^{-m}) j(V^K) = j(V^K)`.

This proof follows the same division. The choice of `t` and its contraction properties are
`representedIwahoriContraction` (steps 1–3). The representation-theoretic part is the
published abstract lemma `Jacquet.fixedJacquetMap_surjective_of_iwahoriContraction`
(step 4). That lemma is stated for any topological group and any element satisfying
`Jacquet.IsIwahoriContraction`, and needs only finite dimensionality of `V^K`. Its own proof
goes through the compressed action of the contracting element, rather than repeating
Renard's computation verbatim; this module does not depend on that route.
