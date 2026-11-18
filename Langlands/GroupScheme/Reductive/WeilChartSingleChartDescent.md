# Descent of Weil-restriction presentations along one étale cover

This module completes the proof of `AffineWeilPairSingleChartDescentStatement` (one étale,
surjective cover) and of `AffineWeilPairEtaleDescentStatement` (an arbitrary covering family of
étale charts). Both are proved from two inputs, taken as hypotheses:

- `hR : WeilFactorIdempotentRigidityStatement`, factor rigidity of Weil restrictions;
- `hK : Langlands.AlgebraicGeometry.FiniteEtaleChartDescentStatement`, faithfully flat descent of
  a finite étale algebra from functorial chart isomorphisms.

## Auxiliary definitions (namespace `Langlands.GroupScheme.WeilChart`)

For `e : A' ⊗[A] B ≃ₐ[A'] C`:

- `coverAlgebra e` is the `B`-algebra structure on `C` given by `b ↦ e (1 ⊗ b)`.
  `coverAlgEquiv e` is `e`, viewed as an isomorphism of `B`-algebras from `A' ⊗[A] B` (with `B`
  acting on the right factor).
- `coverAlgebra_etale`: if `A'` is étale over `A`, then `C` is étale over `B`. It is a base change
  of `A → A'` (`etale_tensor_right`, from the module
  `Langlands.GroupScheme.Reductive.AffineWeilPairEtaleDescentReduction`).
- `coverAlgebra_faithfullyFlat`: if `A'` is faithfully flat over `A`, then `C` is faithfully flat
  over `B`. This is base change, transported along `B ⊗[A] A' ≅ A' ⊗[A] B ≅ C`.

## The theorems (namespace `Langlands.GroupScheme`)

- `affineWeilPairSingleChartDescent hR hK : AffineWeilPairSingleChartDescentStatement`. Let
  `A → A'` be étale with `Spec A' → Spec A` surjective, and let
  `P : G_{A'} ≅ R_{C/A'}(H)` be given. The proof proceeds as follows.
  1. `A'` is flat over `A`, so with the surjectivity it is faithfully flat
     (`flat_and_surjective_SpecMap_iff`).
  2. `exists_chartDescent` (module `WeilChartNaturality`) applies `hK` to the canonical
     coefficient isomorphisms. It gives a finite, projective, étale `A`-algebra `B`, an
     isomorphism `e : A' ⊗[A] B ≃ₐ[A'] C`, and the invariance of the elements `1 ⊗ e (1 ⊗ b)`.
  3. With the `B`-algebra structure `coverAlgebra e`, `Spec C → Spec B` is étale and surjective.
  4. The descended factor group `G' = factorGroup e P hR hred hsimple hinv` (module
     `WeilChartFactorGroup`) is affine and locally of finite type. It is reductive with almost
     simple geometric fibres (`factorGroup_isReductive`, `factorGroup_isAlmostSimple`, module
     `WeilChartFactorCover`). `weilIso` (module `WeilChartWeilIso`) gives
     `G ≅ AffineWeil.groupScheme A B G'`.
- `affineWeilPairEtaleDescent hR hK : AffineWeilPairEtaleDescentStatement`. This combines the
  previous theorem with the reduction `affineWeilPairEtaleDescent_of_singleChart` (module
  `AffineWeilPairEtaleDescentReduction`, integrated together with this module). It is the
  étale-descent input of the adjoint Weil-restriction assembly.

## Provenance

This follows the proof of Proposition 6.4.4 in Conrad, *Reductive group schemes* (2014): étale
descent of the coefficient algebra and of the group, together with uniqueness of Weil-restriction
presentations. The organisation is internal. The canonical isomorphisms come from factor rigidity
(modules `WeilChartTransfer`, `WeilChartAlgebra`). The coefficient algebra descends through `hK`.
The group `G'` is constructed as a closed fixed subgroup of `G_B` (modules `WeilChartDiagonal`,
`WeilChartFactorDescent`, `WeilChartFactorGroup`, `WeilChartFactorChart`). The comparison
`G ≅ R_{B/A}(G')` and the properties of `G'` are proved by faithfully flat descent of points
(modules `AffinePointFaithfullyFlatDescent`, `WeilChartWeilIso`, `WeilChartFactorCover`).
