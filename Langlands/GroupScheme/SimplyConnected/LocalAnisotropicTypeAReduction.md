# Type `A_n` for anisotropic local groups from the affine-diagram input

Authors: Worker 158, Worker 5662.

This module proves one theorem,
`Langlands.GroupScheme.localAnisotropicTypeA_of_affineDiagram`:

```
theorem localAnisotropicTypeA_of_affineDiagram
    (h : LocalAnisotropicAffineDiagramStatement.{u}) :
    LocalAnisotropicTypeAStatement.{u}
```

It is a conditional result. The unproved building input
`LocalAnisotropicAffineDiagramStatement` (module
`Langlands.GroupScheme.SimplyConnected.LocalAnisotropicAffineDiagramStatement`) is an
explicit hypothesis. The conclusion is the published proposition
`LocalAnisotropicTypeAStatement` (module
`Langlands.GroupScheme.SimplyConnected.LocalAnisotropicInnerTypeAStatement`), unchanged,
at the same universe `u`. It uses only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`.

## Proof

Fix `K`, `G`, `d` and the hypotheses `IsAbsolutelyAlmostSimple G` and
`IsAnisotropic G`. The input gives a matrix `B` on `Option d.Vertex` with
`B (some a) (some b) = d.cartan a b`, diagonal entries `2`, nonpositive off-diagonal
entries, `B i j = 0 ↔ B j i = 0`, a vector `m` with positive entries and `m ᵥ* B = 0`, and
transitive symmetries. The proof passes these data to
`TitsIndexData.exists_equiv_cartanA_of_transitive_extension` from
`Langlands.GroupScheme.SimplyConnected.AffineCartanTransitive`. That theorem needs only
the diagonal entry at `none` and the forward implication of the symmetric zero pattern.
Its conclusion,
`∃ n, 0 < n ∧ ∃ e : d.Vertex ≃ Fin n, ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b)`,
is the conclusion of `LocalAnisotropicTypeAStatement`.

## Provenance

The reduction is internal. It follows the proof of Kaletha–Prasad, *Bruhat–Tits Theory:
A New Approach* (2023), Theorem 10.3.1 (printed pp. 391–392 / PDF pp. 422–423; source
`kaletha-prasad-2023-bruhat-tits-new-approach`). The source gets type `A_n` from the
transitive action of `Gal(K'/K)` on the affine Dynkin diagram by the classification of
affine root systems (Proposition 6.4.8). Here that step is replaced by the proved
combinatorial theorem in `AffineCartanTransitive`, which does not use the
classification. See `LocalAnisotropicAffineDiagramStatement.md` for exactly what the
remaining input contains, including the splitting over the maximal unramified extension.
