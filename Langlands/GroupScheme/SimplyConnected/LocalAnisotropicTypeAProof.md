# Anisotropic absolutely almost-simple groups over local fields have type `A_n`

Authors: Worker 158, Worker 5662 (Task 5972).

`LocalAnisotropicTypeAProof.lean` proves the published statement
`Langlands.GroupScheme.LocalAnisotropicTypeAStatement` (module
`Langlands.GroupScheme.SimplyConnected.LocalAnisotropicInnerTypeAStatement`). This is
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Theorem 10.3.1 (printed
pp. 391–392 / PDF pp. 422–423; source `kaletha-prasad-2023-bruhat-tits-new-approach`):

```lean
theorem Langlands.GroupScheme.localAnisotropicTypeA :
    LocalAnisotropicTypeAStatement.{u}
```

## The proved statement

Let `K : Type u` be a nonarchimedean local field, with
`[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`. Let `G`
be a group scheme over `Spec K` with `[IsAffineHom G.X.hom]` and
`[LocallyOfFiniteType G.X.hom]`, and let `d : TitsIndexData G` be any actual index datum
of `G`. If `G` is absolutely almost simple and anisotropic, then there are `n : ℕ` with
`0 < n` and a bijection `e : d.Vertex ≃ Fin n` such that
`d.cartan a b = CartanMatrix.A n (e a) (e b)` for all simple vertices `a b`. In other
words, the Cartan matrix of the index is the type `A_n` Cartan matrix.

The theorem proves the statement exactly as published, at every universe `u`. It adds
no premise and puts no condition on the characteristic of `K` or of its residue field.
The statement module and its Markdown are imported unchanged.

## Proof

The proof is one term. It composes two published results:

1. `Langlands.GroupScheme.localAnisotropicTypeA_of_affineDiagram` (module
   `Langlands.GroupScheme.SimplyConnected.LocalAnisotropicTypeAReduction`) has type
   `LocalAnisotropicAffineDiagramStatement.{u} → LocalAnisotropicTypeAStatement.{u}`.
   For given `K`, `G`, `d` and hypotheses, the input supplies an integer matrix `B` on
   `Option d.Vertex`. Its block on the simple vertices is `d.cartan`, its diagonal
   entries are `2`, its off-diagonal entries are nonpositive and its zero pattern is
   symmetric. It also has a left kernel vector `m` with positive entries
   (`m ᵥ* B = 0`), and its symmetries act transitively on `Option d.Vertex`. The
   reduction passes these data to the proved combinatorial theorem
   `TitsIndexData.exists_equiv_cartanA_of_transitive_extension` (module
   `Langlands.GroupScheme.SimplyConnected.AffineCartanTransitive`), whose conclusion is
   the conclusion of the target. That theorem does not use the classification of affine
   root systems. See `LocalAnisotropicTypeAReduction.md` and `AffineCartanTransitive.md`.
2. `Langlands.GroupScheme.localAnisotropicAffineDiagram` (module
   `Langlands.GroupScheme.SimplyConnected.LocalAnisotropicAffineDiagramProof`, Task
   6205) proves `LocalAnisotropicAffineDiagramStatement.{u}` with no premise. It is the
   building part of the source proof: the `Gal(K'/K)`-stable chamber over the maximal
   unramified extension `K'`, the Cartan matrix of its simple affine roots with their
   positive marks, the transitive Galois action given by anisotropy, and the splitting
   over `K'`. See `LocalAnisotropicAffineDiagramProof.md`.

The Lean term is

```lean
localAnisotropicTypeA_of_affineDiagram localAnisotropicAffineDiagram
```

`lean_check` reports that the theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`. Its only universe parameter is `u`.

The route follows the source up to one step. Kaletha–Prasad get type `A_n` from the
transitive action on the affine Dynkin diagram by the classification of affine root
systems (Proposition 6.4.8 and Table 6.4.1). Here the combinatorial theorem in
`AffineCartanTransitive` replaces that classification step.

## Excluded inputs

The task forbids `LocalAnisotropicSimplyConnectedClassificationStatement`,
`LocalRankOneClassificationStatement`, `LocalRankOneTitsIndexStatement`, any local
Kneser–Tits statement, and any result whose planned proof consumes one of these. The
theorem has no hypotheses and uses only the three standard axioms, so it depends only on
proved Library theorems. None of the first three statements occurs in the modules the
proof imports, directly or transitively. The only Kneser–Tits statement there is
`SimplyConnectedKneserTitsCentralizerStatement`. It occurs only as a hypothesis of
conditional reductions and has no proof in the Library, so the proof cannot depend on
it. The proved local Kneser–Tits theorems `localSpinKneserTits` and
`localSymplecticKneserTits` are not imported.
