# Pulled-back section bases, generation, and closed immersions after base change

This module collects general tools for passing from a field to an extension field in
questions about complete linear systems. It is internal infrastructure for Task 7747,
which proves `Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFieldEmbeddingStatement`
over an arbitrary field by base change to an algebraic closure and descent. Every
declaration below is proved in Lean. The module adds no axiom and assumes no statement
target.

## Definitions

### `Langlands.AlgebraicGeometry.ProjectiveBundle.specGlobalSectionsBasis`

For a commutative ring `R` and an actual module sheaf `N` on `Spec R`, the published
functor `moduleSpecΓFunctor` gives the global sections of `N` as an `R`-module. It does
this by restricting scalars along the inverse of `Scheme.ΓSpecIso R`. The definition
turns an `R`-basis of `moduleSpecΓFunctor.obj N` into a `Γ(Spec R, ⊤)`-basis of
`GlobalSections N`, using Mathlib's `Module.Basis.mapCoeffs` along that ring isomorphism.
The compatibility of the two scalar actions is the published `moduleSpecΓFunctor_smul`.
The lemma `specGlobalSectionsBasis_apply` says the basis vectors are unchanged.

### `Langlands.AlgebraicGeometry.ProjectiveBundle.baseChangeSectionBasis`

Data: a morphism `p : X ⟶ Spec R`, a line bundle `L` on `X`, a commutative square
`w : q ≫ p = p' ≫ β` with `β : Spec R' ⟶ Spec R` and `p' : X' ⟶ Spec R'`, and two
instance hypotheses:

- the direct image `p_* L` is quasi-coherent;
- the published canonical comparison
  `baseChangeEvaluation p L (𝟙 _) β p' q w : β^* p_* L ⟶ p'_* q^* L` is an isomorphism.

Given an `R`-basis `b` of `(relativeGlobalSections p).obj L.obj`, i.e. of `Γ(X, L)`, the
definition produces an `R'`-basis of `(relativeGlobalSections p').obj (q^* L).obj`, i.e.
of `Γ(X', q^* L)`. The construction:

1. read `b` as a `Γ(Spec R, ⊤)`-basis (`specGlobalSectionsBasis`);
2. base-change it to `Γ(Spec R', ⊤)` and transport it through the published bijection
   `pullbackTensorMap β (p_* L) le_top : Γ(Spec R', ⊤) ⊗ Γ(p_* L, ⊤) ⟶ Γ(β^* p_* L, ⊤)`
   (`pullbackTensorMap_bijective`; both opens are the whole affine schemes);
3. transport it along the comparison isomorphism on global sections;
4. read the result back as an `R'`-basis.

`baseChangeSectionBasis_apply` identifies its members: the `i`-th vector is the actual
pullback `pullbackSection q L.obj (b i)`. The proof uses `pullbackTensorMap_one_tmul`,
the published `baseChangeEvaluation_sectionPullbackLE` and
`pullbackSection_eq_sectionPullbackLE`.

Mathematically this is the familiar statement that, when `Γ(X', q^* L) = R' ⊗_R Γ(X, L)`
by the comparison map (for instance by flat base change, Stacks Project Lemma 30.5.2,
tag 02KH, registered as `stacks-flat-base-change-projection-formula-2026-11-02`), the
pullbacks of a basis form a basis. Here the comparison isomorphism is a hypothesis; the
module does not prove flat base change.

## Lemmas about the transported basis

- `exists_eq_linComb_pullbackSection`: for `R' = CommRingCat.of K'` and a basis indexed by
  `Fin (n + 1)`, every global section of `q^* L` equals
  `LinearSystem.linComb p'' (fun i ↦ pullbackSection q L.obj (b i)) c` for some
  coefficients `c : Fin (n + 1) → K'`. That is, it is
  `∑ i, scalarsFromBase p'' (c i) • pullbackSection q L.obj (b i)`.
  The coefficients are the coordinates in `baseChangeSectionBasis`.
- `exists_eq_sum_pullbackSection`: the same for a basis with any index type, as a finite
  sum over the support of the coordinates.
- `vanishesAlong_of_forall_pullbackSection`: if all `pullbackSection q L.obj (b i)` vanish
  along a morphism `y : T ⟶ X'`, so does every global section of `q^* L`. The proof uses
  additivity and linearity of pullback of sections (`LinearSystem.pullbackSection_sum`,
  `LinearSystem.pullbackSection_smul`).

## Generation and epimorphisms

`Langlands.SchemeModule.epi_of_forall_mem_nonvanishingLocus`: let `φ : N ⟶ L.obj` be a
morphism of actual module sheaves onto a line bundle. Suppose every point `x` lies in the
nonvanishing locus of `φ.app ⊤ t` for some global section `t` of `N`. Then `φ` is an
epimorphism.

Proof: by the published `epi_of_isLocallySurjective` and Mathlib's
`locally_surjective_iff_surjective_on_stalks`, it suffices that every stalk map of `φ` is
surjective. At `x`, the section `s = φ.app ⊤ t` is a stalk frame
(`lineBundleResidueStalkCriterion`). So the stalk map of `sectionHom L.obj s` is an
isomorphism. By `sectionHom_naturality` this map is the composite of the stalk map of
`sectionHom N t` with the stalk map of `φ`. Hence the latter is surjective.

## Closed immersions over an algebraically closed field

`Langlands.AlgebraicGeometry.LinearSystem.isClosedImmersion_linearSystemMap_of_separates`:
take `K` algebraically closed, `p : X ⟶ Spec K` proper, and sections
`s : Fin (n + 1) → GlobalSections L.obj` without common zero. Assume
`SeparatesPointsAndTangents p L`, and assume every global section is `linComb p s c` for
some `c`. Then the published `linearSystemMap p hs : X ⟶ ProjectiveSpace K n` is a closed
immersion.

Proof: `linearSystemMap p hs` lies over `Spec K` (`linearSystemMap_toSpec`), so it is
proper because `p` is proper and projective space is separated. The published criterion
`properRationalImmersion_isClosedImmersion` asks for injectivity on rational points and
on rational tangent vectors.

- For rational points `x ≠ y` with the same image, separation gives a section vanishing
  along `x` but not along `y`. It is a linear combination `linComb p s c`. The forward
  half of the vanishing dictionary of `linearSystemMap` (`exists_mem_trivializationOpen`,
  `mem_trivializationOpen_of_comp_mem`, `comp_mem_coordinateOpen` and
  `vanishesAlong_linComb_iff_of_comp_eq`, as in the published proof of
  `linearSystemMorphism`) shows that it vanishes along `y` too, a contradiction.
- Tangent vectors are handled the same way, using `forall_mem_of_augmentation_comp` and
  `vanishesAlong_comp`.

## Descent along fpqc coverings

- `Langlands.AlgebraicGeometry.mono_of_isPullback_of_fpqc`: take a pullback square
  `IsPullback fst snd f g` with `f` surjective, flat and quasi-compact. If `fst` is a
  monomorphism, so is `g`. Proof: monomorphisms are the diagonal of isomorphisms
  (`MorphismProperty.diagonal_isomorphisms`). Isomorphisms satisfy fpqc descent
  (`descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`, Stacks 02L4 in
  Mathlib). Descent passes to diagonals (Mathlib's instance for `MorphismProperty.diagonal`).
  The needed stability of `@Surjective ⊓ @Flat ⊓ @QuasiCompact` under base change is
  supplied explicitly.
- `Langlands.AlgebraicGeometry.isClosedImmersion_of_isPullback_of_fpqc`: in the same
  situation, if `fst` is a closed immersion and `g` is proper, then `g` is a closed
  immersion. Proof: Mathlib's `IsClosedImmersion.iff_isProper_and_mono`
  (Stacks 04XV (1) ⇔ (2)) together with the previous lemma.

## Provenance and scope

The definitions are internal constructions: they repackage a basis along published
canonical isomorphisms. No source definition is formalized, and the hypotheses
(quasi-coherence and invertibility of the comparison map) are explicit instance
arguments. The lemmas are standard facts proved here from published Library results and
Mathlib. The Markdown claims nothing beyond the Lean statements.

Worker 5655 wrote this module for Task 7747 (`5e7c789a-8444-4b3e-a58a-fe10bd3c7b99`).
