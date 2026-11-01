# Coherent Künneth over a field for external tensor products of line bundles: proof

Authors: Worker 1137 and Worker 1147.

Lean module: `Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethProof`.

## Theorem

```lean
theorem coherentFieldExternalTensorKunneth :
    CoherentFieldExternalTensorKunnethStatement.{u}
```

This proves the published proposition, imported unchanged from
`Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethStatement`, in an
arbitrary universe `u`, with no additional hypothesis. The setting is as follows:

- `K : Type u` is a field and `X Y : Over (Spec (CommRingCat.of K))` are smooth and proper.
- `P = X ⨯ Y` is the product in `Over (Spec K)`, with projections `p₁` and `p₂`.
- `L : LineBundle X.left` and `M : LineBundle Y.left` are line bundles, and `n : ℕ`.

The theorem gives a `K`-linear isomorphism

    (relativeCohomology P.hom n).obj (tensorObj (p₁^* L.obj) (p₂^* M.obj))
      ≅ ModuleCat.of K (⨁_{ab : {ab : ℕ × ℕ // ab.1 + ab.2 = n}}
          (relativeCohomology X.hom ab.1.1).obj L.obj ⊗[K] (relativeCohomology Y.hom ab.1.2).obj M.obj)

Here `relativeCohomology` is the right derived functor of `K`-module global sections, and
`tensorObj` and `pullback` are the actual module-sheaf constructions.

## Implemented route

1. A proper morphism is separated and quasi-compact. The underlying spaces of `X.left`
   and `Y.left` are therefore compact (`QuasiCompact.compactSpace_of_compactSpace`), and
   `X.hom`, `Y.hom` are separated.
2. Geometric input (Worker 1147, `BiCech.Kunneth`):
   `BiCech.exists_nonempty_relativeCohomology_overProd_iso X Y L M n` provides finite
   ordered affine covers `𝒰` of `X.left` and `𝒱` of `Y.left` with
   `Hⁿ(P, p₁^* L ⊗ p₂^* M) ≅ Hⁿ(Tot(Č(𝒰, L) ⊗_K Č(𝒱, M)))`. Here `Č` is the Library's
   `cechCochainComplex`, and the total complex is
   `HomologicalComplex.mapBifunctor … (curriedTensor _) (ComplexShape.up ℕ)`.
3. Algebraic Künneth over a field (Worker 1137, `FieldKunneth.kunnethIso`):
   `Hⁿ(Tot(C ⊗_K D)) ≅ ⨁_{a+b=n} Hᵃ(C) ⊗_K Hᵇ(D)` for `ℕ`-indexed complexes of
   `K`-modules.
4. The factors: `nonempty_relativeCohomology_iso_cechCochainComplex_homology` (Worker 1137,
   `CechResolution.CechCohomologyIso`) identifies `Hᵃ(X, L)` with `Hᵃ(Č(𝒰, L))`, and
   likewise for `M`. It uses the separatedness of `X.hom`, `Y.hom` and the
   quasi-coherence of line bundles (`LineBundle.isQuasicoherent`).
5. `directSumTensorIso` transports componentwise isomorphisms through the direct sum of
   tensor products (`DFinsupp.mapRange.linearEquiv` and `TensorProduct.congr`). Composing
   the isomorphisms of steps 2 to 5 gives the statement.

## Supporting modules

The candidate also contains the helper modules:

- `Langlands.Cohomology.ModuleComplex.TensorSignsUpNat`: the tensor signs on
  `ComplexShape.up ℕ`.
- `Langlands.Cohomology.ModuleComplex.FieldKunneth`: algebraic Künneth over a field.
- `Langlands.AlgebraicGeometry.Modules.CechResolution.CechCohomologyIso`: derived
  isomorphisms give isomorphisms of cohomology modules.
- `Langlands.AlgebraicGeometry.Modules.BiCech.*`: the bi-Čech resolution and the section
  computation. The modules are `OneDirection`, `Sections`, `Complex`, `Comparison`,
  `TensorFrame`, `Cup`, `CupBijective`, `GlobalSections`, `ProductSections`,
  `SectionsIso` and `Kunneth`.

Each module has its own Markdown file.

## Provenance

The general formula is Stacks Project tag 0BED (`lemma-kunneth`), in the source
registered as `stacks-flasque-affine-vanishing-kunneth-a04446e5`: commit `a04446e5`,
`varieties.tex` lines 5441-5456 for the statement and lines 5459-5630 for the proof. See
the target statement's Markdown for the full citation.

The implemented route differs from the source's argument. The source compares the Čech
complex of the product cover with the tensor product of the Čech complexes of the factors
through a cup-product map, and then uses a two-out-of-three argument. Here, instead:

- the cohomology of `p₁^* L ⊗ p₂^* M` is computed by the bi-Čech total complex, an
  acyclic resolution on `P` indexed by pairs of tuples of the two covers;
- its global sections are identified, as a complex, with the tensor total complex of the
  factor Čech complexes.

No isomorphism of complexes with the Čech complex of the product cover is claimed. The
comparison with `Hⁿ(P, ·)` is proved on cohomology only, through the derived acyclic
resolution comparison.
