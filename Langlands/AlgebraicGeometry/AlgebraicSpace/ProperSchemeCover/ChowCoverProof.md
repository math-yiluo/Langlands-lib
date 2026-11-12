# Proof of the weak Chow cover statement

This module proves `chowCover : ChowCoverStatement.{u}` (module `ChowCoverStatement`).
For every separated algebraic space `X` over an affine scheme `S` with a quasi-compact,
locally finitely presented étale atlas, it gives a scheme `U` over `S` and a surjective
`φ : h_U → X`. Every base change of `φ` to a scheme is proper, and `U → S` is locally of
finite type and quasi-compact. (`U → S` is also separated, an instance of
`Construction`, but the statement does not record this.) This is a weak form of Chow's
lemma (Stacks 089I), proved by the construction of the modules `Construction`,
`Closedness` and `RelativeProper`.

## Quasi-compactness of the cover

- `ChowData.isCompact_opens`: each open `opens i = (ζ ≫ p i)⁻¹(O)` of `Z` is quasi-compact.
  The composite of `ζ ≫ p i : Z ⟶ Y` with `Y → S` is the proper `Z → S`. Since `Y → S` is
  separated, `ζ ≫ p i` is quasi-compact (`QuasiCompact.of_comp`), and the preimage of the
  quasi-compact open `O` is quasi-compact.
- `U = ⋃ i, opens i` is a finite union, so `U` is a compact space. Over an affine
  (quasi-separated) base, `U → S` is then quasi-compact (Mathlib's
  `quasiCompact_of_compactSpace`).

## Construction of the data (`chowCover`)

1. `FinitePresentationEtaleAtlas.exists_affine_atlas` gives an étale surjective chart
   `π : h_W → X` with `W` affine and `W → S` locally of finite presentation. `W → S` is
   quasi-compact because `W` is affine and `S` is affine.
2. `X` is quasi-separated (`isQuasiSeparated_of_isSeparated`). `exists_completeLocus`
   (module `CompleteTuples`) gives `n` such that every point of `W` is the first
   coordinate of a complete point of the fibre power `P = ChartFibrePower.fin π n` with
   `n + 1` factors.
3. Let `C = Γ(S, ⊤)` and `e : S ≅ Spec C` (`Scheme.isoSpec`). The map
   `W → S ≅ Spec C` is of finite type, so `exists_closedImmersion_stdAway`
   (module `AffineEmbedding`) gives a closed immersion `ι₀ : W ⟶ Spec C[X₀,…,X_N]_(X₀)`
   compatible with the structure maps.
4. The data are:
   - `Y = ℙᴺ_C`, over `S` through `e⁻¹`. It is proper, hence separated.
   - `O` is the standard open `D₊(X₀)`, which is affine and so quasi-compact, and `o` is
     its open immersion `stdAwayι`.
   - `ι = ι₀`, a closed immersion.
   - `M = ℙᴺ ×_C ⋯ ×_C ℙᴺ` with `n + 1` factors (`ProjSpace.prodOver`), proper over `S`.
     The `p k` are its projections (`ProjSpace.prodPr`).
   - `ε : P ⟶ M` is the morphism with components `pr k ≫ ι₀ ≫ stdAwayι`
     (`ProjSpace.prodLift`). The identity `ε ≫ p k = pr k ≫ ι ≫ o` is
     `ProjSpace.prodLift_comp_prodPr`.

   All compatibilities with the structure maps to `S` reduce to
   `ProjSpace.prodPr_comp_π`, `ProjSpace.prodLift_comp_prodOverπ`, and the compatibility
   of `ι₀` with `W → Spec C`.
5. For these data `D`, the cover is `D.U` with `D.φ`. Surjectivity is
   `ChowData.isSurjective_φ`, represented properness is `ChowData.relative_isProper_φ`,
   and finite type and quasi-compactness of `U → S` are instances.
