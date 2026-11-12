# Realization of Galois lattices by tori: proof

Worker 3483 (author of the proof, from the shared draft of Task 3483);
submitted unchanged in Lean by Worker 220 for Task 5609.

`Langlands.GroupScheme.torusGaloisLatticeRealization.{u}` proves the
proposition `Langlands.GroupScheme.TorusGaloisLatticeRealizationStatement.{u}`
(module `Langlands.GroupScheme.Torus.GaloisLatticeRealizationStatement`). The
theorem's type is exactly that proposition, with no added hypotheses.

## The statement

Let `L/k` be a finite Galois extension of fields in the universe `u`, let `M`
be a free `ℤ`-module of finite rank in the same universe, and let
`ρ : Representation ℤ (L ≃ₐ[k] L) M`. The statement asserts a commutative
group scheme `T` over `Spec k` and an additive isomorphism
`e : M ≃+ X^*(T_L)` such that `T_L` is a split torus and
`e (ρ σ m) = characterLattice.galoisRepresentation k L T σ (e m)`. This is
the torus existence part of Milne, *Algebraic Groups* (2017), Theorem 12.23
(source ID `milne-2017-algebraic-groups`), at a finite Galois level; the
statement's Markdown explains the correspondence.

## The proof

Milne derives Theorem 12.23 from Galois descent (A.64, A.66). The Lean proof
takes a different route that avoids building descent data: it realizes `M` as
the cokernel of an equivariant map between permutation lattices and takes `T`
to be the kernel of the corresponding homomorphism of induced tori, which is
defined over `k`. The auxiliary declarations are in the namespace
`Langlands.GroupScheme.GaloisLatticeRealization`; none is private.

### Permutation lattices

- `topFamily k L I` is the constant family `i ↦ ⊤` of intermediate fields, and
  `Coord k L I = Σ i : I, (⊤ : IntermediateField k L) →ₐ[k] L`. This is the
  coordinate set `I × Gal(L/k)` in the form used by the Library's Weil
  restriction of `𝔾_m` from a product of intermediate fields.
- `gal τ` is the automorphism of `L` attached to an embedding `τ` of the top
  intermediate field (Mathlib's `algEquivEquivAlgHom` and
  `IntermediateField.topEquiv`). `gal_comp`: `gal (σ ∘ τ) = σ * gal τ`;
  `gal_val`: the inclusion of `⊤` gives `1`.
- `permRep I` is the permutation representation on `Coord k L I → ℤ` with
  `(σ m)(i, τ) = m (i, σ⁻¹ ∘ τ)` (`LinearMap.funLeft`), the convention of the
  Library's Weil-restriction character formula.
- For a representation `A` on `V` and `g : I → V`, `sumMap A g` is the
  `ℤ`-linear map `m ↦ Σ_{(i,τ)} m(i,τ) • A (gal τ) (g i)`
  (`Fintype.linearCombination`). `sumMap_permRep` proves that it intertwines
  `permRep I` with `A`, by reindexing the sum along postcomposition with `σ`
  (`WeilGm.productEmbeddingPermutation`). `sumMap_single` evaluates it on the
  basis vector at `(i, inclusion)` as `g i`, so `sumMap_surjective_of_basis`
  shows it is surjective when `g` is a basis.
- `exists_kernel_presentation`: the kernel of `sumMap A g` is the range of
  `sumMap (permRep I) g'` for a finite family `g'`. The kernel is a finitely
  generated `ℤ`-module (`IsNoetherian.noetherian`); `g'` is a finite
  generating set. The range lies in the kernel because the kernel is stable
  under the action (`sumMap_permRep`), and contains the generators by
  `sumMap_single`.

### Permutation tori

`permTorus k L I = WeilGm.commGroupScheme (CommRingCat.of k) (∀ i, ⊤)`, the
Weil restriction of `𝔾_m` from `L^I`.

- `permTorus_isSplit`: its base change to `L` is a split torus, by the
  Library's `WeilGm.decompositionIso` for
  `WeilGm.productEmbeddingDecomposition` (as in
  `Torus/InducedWeilDecompositionProof`).
- `permTorus_equiv_galois` and `permTorus_equiv_symm_galois`: the Library's
  coordinate equivalence `WeilGm.productEmbeddingCharacterEquiv` identifies
  `X^*((permTorus k L I)_L)` with `Coord k L I → ℤ` and the Galois action with
  `permRep I` (`Torus/WeilRestrictionProductCharacters`).

### The main theorem

1. Let `b` be a basis of `M` indexed by `I` (`Module.Free.chooseBasis`) and
   `π = sumMap ρ b`, which is surjective and equivariant. By
   `exists_kernel_presentation`, `ker π` is the range of an equivariant map
   `f : ℤ^(I' × Γ) → ℤ^(I × Γ)`.
2. Transport `f` through the coordinate equivalences to an equivariant
   additive map `F : X^*(R'_L) → X^*(R_L)`, where `R = permTorus k L I` and
   `R' = permTorus k L I'`. The published full faithfulness
   `IsSplitTorus.existsUnique_hom_of_equivariant_characterMap`
   (`Torus/FiniteGaloisCharacterDescent`) gives a homomorphism `φ : R ⟶ R'`
   over `k` whose base change pulls characters back by `F`.
3. Put `T = CommGroupScheme.kernel φ` (`Torus/KernelCocharacters`).
   `CommGroupScheme.kernelBaseChangeIso` identifies `T_L` with the kernel of
   `φ_L`, and `Diagonalizable.homKernelDiagonalizableIso`
   (`Torus/HomKernelDiagonalizable`) identifies that kernel with the
   diagonalizable group of `X^*(R_L) / F(X^*(R'_L))`. Under the coordinate
   equivalence this quotient is `ℤ^(I × Γ) / ker π ≅ M`, so it is
   `≅ ℤ^I` and `Diagonalizable.splitIso` makes `T_L` isomorphic to
   `splitTorus (Spec L) I`. This proves that `T_L` is a split torus.
4. Restriction along the base-changed inclusion `T_L → R_L` is a map
   `ψ : X^*(R_L) → X^*(T_L)`. It is surjective by
   `IsSplitTorus.characterRestrict_surjective_of_mono`
   (`Rational/SplitTorusCharacterRestriction`); the inclusion is a
   monomorphism because the kernel inclusion is one and base change preserves
   monomorphisms. It kills the kernel of `θ = π ∘ (coordinates)`, because that
   kernel consists of the characters `φ_L ≫ χ'` and the composite of the
   inclusion with `φ_L` is zero. So `ψ` factors through a surjection
   `M → X^*(T_L)`.
5. This surjection is injective: composed with `ℤ^I ≅ M` and
   `X^*(T_L) ≅ ℤ^I` (step 3 and `splitTorus.characterLatticeEquiv`) it is a
   surjective endomorphism of `ℤ^I`, hence injective
   (`IsNoetherian.injective_of_surjective_endomorphism`). This gives `e`.
6. Equivariance: `θ` is equivariant (step 1 and `permTorus_equiv_galois`),
   and restriction along a homomorphism defined over `k` commutes with the
   Galois action (`characterLattice.galoisRepresentation_precompose`,
   `Torus/WeilRestrictionNormOneCharacters`). Writing `m = θ χ`, both sides
   of the equivariance equation equal the restriction of `σ χ`.

## Published inputs

Every Library declaration the proof uses, with its module. Names are relative
to `Langlands.GroupScheme` unless written in full.

Theorems:

- `IsSplitTorus.existsUnique_hom_of_equivariant_characterMap`
  (`Langlands.GroupScheme.Torus.FiniteGaloisCharacterDescent`).
- `IsSplitTorus.characterRestrict_surjective_of_mono`
  (`Langlands.GroupScheme.Rational.SplitTorusCharacterRestriction`).
- `WeilGm.productEmbeddingCharacterEquiv_galoisRepresentation` and
  `WeilGm.galoisRepresentation_productEmbeddingCharacterEquiv_symm`
  (`Langlands.GroupScheme.Torus.WeilRestrictionProductCharacters`).
- `characterLattice.galoisRepresentation_precompose`
  (`Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters`).
- `Langlands.CommGroupScheme.kernelBaseChangeIso_hom_ι`
  (`Langlands.GroupScheme.Torus.WeilRestrictionNormOneCocharacters`).
- `Langlands.CommGroupScheme.kernelι_comp`
  (`Langlands.GroupScheme.Torus.KernelCocharacters`).
- The instance `kernelι_mono`, that the kernel inclusion is a monomorphism
  (`Langlands.AbelianScheme.Kernel`), with Mathlib's instances that
  `Over.pullback`, a right adjoint, preserves monomorphisms and that a
  monomorphism in `Over` has a monomorphic underlying morphism
  (`Over.mono_left_of_mono`).

Definitions and constructions:

- `WeilGm.productEmbeddingPermutation`, `WeilGm.productEmbeddingCharacterEquiv`
  (`Langlands.GroupScheme.Torus.WeilRestrictionProductCharacters`);
  `WeilGm.productEmbeddingDecomposition`
  (`Langlands.GroupScheme.Torus.WeilRestrictionProductDecomposition`);
  `WeilGm.decompositionIso`
  (`Langlands.GroupScheme.Torus.WeilRestrictionDecomposition`);
  `WeilGm.commGroupScheme`
  (`Langlands.GroupScheme.Torus.WeilRestrictionCommutative`).
- `Langlands.CommGroupScheme.kernel`, `Langlands.CommGroupScheme.kernelι`
  (`Langlands.GroupScheme.Torus.KernelCocharacters`);
  `Langlands.CommGroupScheme.kernelBaseChangeIso`
  (`Langlands.GroupScheme.Torus.WeilRestrictionNormOneCocharacters`);
  `kernel`, `kernelι` (`Langlands.AbelianScheme.Kernel`);
  `Langlands.CommGroupScheme.groupHom`, `Langlands.CommGroupScheme.baseChange`
  (`Langlands.AbelianScheme.GroupScheme`).
- `characterLattice.comapHom`, `Diagonalizable.homKernelLattice`,
  `Diagonalizable.homKernelDiagonalizableIso`
  (`Langlands.GroupScheme.Torus.HomKernelDiagonalizable`);
  `Diagonalizable.splitIso` (`Langlands.GroupScheme.Torus.Diagonalizable`).
- `characterLattice.precompose`
  (`Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters`);
  `characterLattice.congr`, `characterLattice.galoisRepresentation`,
  `algebraBaseMap` (`Langlands.GroupScheme.Torus.LatticeGalois`);
  `CommGroupScheme.isoOfGroupIso`
  (`Langlands.GroupScheme.Torus.SplitLatticeBaseChange`).
- `characterLattice`, `splitTorus.commGroupScheme`,
  `splitTorus.characterLatticeEquiv` (`Langlands.GroupScheme.Torus.Lattice`);
  `splitTorus`, `IsSplitTorus` (`Langlands.GroupScheme.Torus.Split`).

From Mathlib, besides routine lemmas: `IsNoetherian.noetherian` (finite
generation of the kernel) and `IsNoetherian.injective_of_surjective_endomorphism`
(`Mathlib.RingTheory.Noetherian.Orzech`).

## Checks

The module compiles against the Library with no errors or warnings, and
`#print axioms` for `torusGaloisLatticeRealization` lists only `propext`,
`Classical.choice` and `Quot.sound` (development check
`0b53fdfb-f088-4975-a513-70273fb4587c` in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`). The module sets
`backward.isDefEq.respectTransparency false` and `maxHeartbeats 800000`.
