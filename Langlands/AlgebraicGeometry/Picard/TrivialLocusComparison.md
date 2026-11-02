# Comparing base changes of line bundles and their global sections

Author: Worker 766.

This module is `Langlands.AlgebraicGeometry.Picard.TrivialLocusComparison`. It
imports the Library modules
`Langlands.AlgebraicGeometry.Picard.ClassEqualizerReduction` (and through it
`ClassEqualizerLocus`, with `isoLocus` and `isoLocus_trivial_iff`, and
`RelativeGeometry`, with `relativeSpace`),
`Langlands.AlgebraicGeometry.Picard.FrameCombinationTrivialization`
(`FrameCombination.pullbackGlobalSection` and its lemmas) and
`Langlands.AlgebraicGeometry.Modules.SchemeIsoCohomology`
(`Modules.pushforwardEquivalence`).

## Purpose and provenance

This is an internal helper for the proof of the Library statement
`FieldPicardClassEqualizerImmersionStatement`, which is part of the diagonal
branch of `FieldPicardSheafAlgebraicSpaceStatement`. The triviality locus of a
line bundle is phrased with the chosen fibre products
`(relativeSpace f).obj T'`. The FLT port's cohomology and base change theorem
and its polynomial-trick consumer use other fibre products, of the form
`pullback g (specMap R A)`. This module provides the comparisons between the two.
No literature theorem is claimed. All results are formal consequences of the
universal property of fibre products, of the pullback functor on sheaves of
modules, and of the definition `moduleSectionsOfHom` of the module structure
on global sections over a base ring.

## Conventions

- For a scheme `P` with a morphism `p : P ⟶ Spec A`, the global sections
  `Γ(M, ⊤)` of a module `M` on `P` are an `A`-module through
  `Scheme.TwoAffineOpenCover.moduleSectionsOfHom p M ⊤`. Here `r : A` acts as
  the image of `r` in `Γ(P, ⊤)` under `p`.
- `SheafOfModules.unit P.ringCatSheaf` is the structure sheaf as a module.

## Triviality along morphisms over a test morphism

These declarations are in the namespace `RelativePicard`.

- `relativeSpace_isPullback`: for `φ : V ⟶ T` in `Over S`, the square formed
  by `(relativeSpace f).map φ`, the projections `pullback.fst V.hom f` and
  `pullback.fst T.hom f`, and `φ.left` is a pullback square. The proof applies
  Mathlib's `IsPullback.of_right` to the two pullback squares over `X`.
- `nonempty_pullback_iso_trivial_of_mem`: let `g : T' ⟶ T.left` lie in
  `isoLocus f T N (LineBundle.trivial _)`, so that `N` becomes trivial along
  `g`. Let `q : P ⟶ (relativeSpace f).obj T` and `p : P ⟶ T'` satisfy
  `q ≫ pullback.fst T.hom f = p ≫ g`. Then the pullback of `N` along `q` is
  isomorphic to the trivial line bundle. The morphism `q` factors through
  `(relativeSpace f).map (Over.homMk g)` by the universal property of the
  fibre product, and pullback preserves the trivial bundle.

## Global sections over a base ring

These declarations are in the namespace `SectionsComparison`.

- `sectionsMap p φ`: a morphism `φ : M ⟶ M'` of modules on `P` gives an
  `A`-linear map `Γ(M, ⊤) →ₗ[A] Γ(M', ⊤)`, namely `φ.app ⊤`.
- `sectionsEquivOfIso p e`: an isomorphism `e : M ≅ M'` gives an `A`-linear
  equivalence of global sections.
- `pullbackSectionsMap p₁ p₂ c hc M`: for `c : P₁ ⟶ P₂` with `c ≫ p₂ = p₁`,
  pulling back global sections along `c`
  (`FrameCombination.pullbackGlobalSection c`) is `A`-linear from
  `Γ(M, ⊤)` to `Γ(c^* M, ⊤)`. Linearity uses
  `FrameCombination.pullbackGlobalSection_smul` and the identity
  `p₂.appTop ≫ c.appTop = p₁.appTop` on global sections.
- `pullbackSectionsEquiv`: if moreover `c` is an isomorphism, this map is an
  `A`-linear equivalence. Pushforward along an isomorphism is an equivalence
  (`Modules.pushforwardEquivalence`), so the pullback functor is an equivalence
  and the unit of the pullback–pushforward adjunction is an isomorphism. Its
  component at `M`, evaluated on the whole scheme, is the pullback of global
  sections.
- `unitSectionsEquiv`: for an isomorphism `c : P₁ ⟶ P₂` over `Spec A`, the
  global sections of the structure sheaves of `P₁` and `P₂` are `A`-linearly
  equivalent. It combines `pullbackSectionsEquiv` with
  `Langlands.Scheme.Modules.pullbackUnitIso`.
- `sectionsEquivOfIsPullback h₁ h₂ M`: let `h₁ : IsPullback q₁ p₁ u v` and
  `h₂ : IsPullback q₂ p₂ u v` be two pullback squares of the same cospan
  `u : Y ⟶ S₀`, `v : Spec A ⟶ S₀`, and let `M` be a module on `Y`. Then
  `Γ(q₁^* M, ⊤) ≃ₗ[A] Γ(q₂^* M, ⊤)`, with `A` acting through `p₁` and `p₂`.
  The isomorphism between the two pullbacks is Mathlib's
  `IsPullback.isoIsPullback`. It commutes with the projections, so the result
  follows from `pullbackSectionsEquiv`, `Scheme.Modules.pullbackComp` and
  `Scheme.Modules.pullbackCongr`.
- `unitSectionsEquivOfIsPullback`: the same comparison for the structure
  sheaves of `P₁` and `P₂`.
