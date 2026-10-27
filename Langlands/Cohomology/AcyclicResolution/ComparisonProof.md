# Acyclic resolutions compute right derived functors

Author: Worker 716. This module proves Worker 3's statement
`Langlands.Cohomology.AcyclicResolutionComparisonStatement` from the module
`Langlands.Cohomology.AcyclicResolution.Statement`. It imports that statement module, Worker
61's published modules `Langlands.Cohomology.RightDerivedSequence` (the long exact sequence of
right derived functors) and `Langlands.Cohomology.ExtendMap` (extension by zero commutes with
applying a functor), and Mathlib's `Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`.

Composition `f ≫ g` is `f` followed by `g`. `(single₀ C).obj A`, written `A[0]` below, is
the cochain complex with `A` in degree zero and zero elsewhere. `Hⁿ(F ·)` abbreviates the
functor `F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n`: apply `F`
termwise, then take degree-`n` cohomology. `RᵏF` is Mathlib's `F.rightDerived k`. An object
`X` is *`F`-acyclic* if `(F.rightDerived (n + 1)).obj X` is zero for every `n : ℕ`. A complex
is *acyclic* if it is exact in every degree (Mathlib's `HomologicalComplex.Acyclic`).

## Theorem

`Langlands.Cohomology.acyclicResolutionComparisonStatement :
AcyclicResolutionComparisonStatement.{u, v, u', v'}`, with all four universe parameters free
and no hypotheses beyond those of the statement. Spelled out, it says:

Let `C : Type u` be an abelian category (`Category.{v} C`) with
`[HasInjectiveResolutions C]`, let `D : Type u'` be an abelian category
(`Category.{v'} D`), and let `F : C ⥤ D` be an additive functor that preserves finite limits
(so `F` is left exact). Let `A : C`, `K : CochainComplex C ℕ`, and `ε : A[0] ⟶ K` a
quasi-isomorphism (`QuasiIso ε`), such that every term `K.X i` is `F`-acyclic. Let `I` be an
injective resolution of `A` and `φ : K ⟶ I.cocomplex` a cochain map with `ε ≫ φ = I.ι`. Then

1. `(F.mapHomologicalComplex _).map φ : F K ⟶ F I.cocomplex` is a quasi-isomorphism, and
2. for every `n : ℕ` the map
   `Hⁿ(F ·).map φ ≫ (I.isoRightDerivedObj F n).inv : Hⁿ(F K) ⟶ (F.rightDerived n).obj A`
   is an isomorphism. Here `I.isoRightDerivedObj F n` is Mathlib's identification of
   `(F.rightDerived n).obj A` with the degree-`n` cohomology of `F` applied to
   `I.cocomplex`.

So a resolution of `A` by `F`-acyclic objects computes the right derived functors of `F` at
`A`, through the map induced by a lift to an injective resolution. The statement's Markdown
locates this in Grothendieck, *Sur quelques points d'algèbre homologique* (1957), Section 2.4,
Remark 3 after Theorem 2.4.1, p.148, in the setting of Cartan–Eilenberg, *Homological
Algebra* (1956), Chapter V. The sections below describe the route of the Lean proof, through
mapping cones and the long exact sequence of right derived functors.

## Helper results

All helpers are in the namespace `Langlands.Cohomology.AcyclicComparison`. They are stated in
the setting of Worker 61's long exact sequence: `C` and `D` abelian with independent universes,
`[EnoughInjectives C]`, and, where the long exact sequence is used, derived categories chosen by
`[HasDerivedCategory.{w} C]` and `[HasDerivedCategory.{w'} D]`.

- `isZero_rightDerived_obj_of_isZero F k hX`: if `X` is a zero object, then `RᵏF X` is zero.
  Proof: the identity of `X` is the zero map, and right derived functors send zero maps to zero
  (Worker 61's `DerivedPlus.rightDerived_map_zero`; Mathlib has no `Additive` instance for
  `F.rightDerived k`).
- `isZero_rightDerived_obj_of_iso F k e hX`: if `e : X ≅ Y` and `RᵏF X` is zero, so is
  `RᵏF Y`.
- `isZero_rightDerived_obj_biprod F k X Y hX hY`: if `RᵏF X` and `RᵏF Y` are zero, so is
  `RᵏF (X ⊞ Y)`. Proof: `X ⟶ X ⊞ Y ⟶ Y` is split short exact, and Worker 61's
  `DerivedPlus.rightDerived_exact₂` makes `RᵏF X ⟶ RᵏF (X ⊞ Y) ⟶ RᵏF Y` exact.
- `cyclesSc X i j`, for `X : CochainComplex C ℤ`: the short complex
  `Zⁱ ⟶ Xⁱ ⟶ Zʲ` of objects of cycles, with first map the inclusion `X.iCycles i` and second
  map `X.toCycles i j`, the differential `Xⁱ ⟶ Xʲ` factored through `Zʲ`.
- `cyclesSc_shortExact X i j hij hX`: if `i + 1 = j` and `X` is exact in degree `j`, then
  `0 ⟶ Zⁱ ⟶ Xⁱ ⟶ Zʲ ⟶ 0` is short exact. The inclusion is a monomorphism; exactness in the
  middle holds because `Zⁱ` is the kernel of the differential `Xⁱ ⟶ Xʲ`, which differs from
  `X.toCycles i j` by the monomorphism `X.iCycles j`; and `X.toCycles i j` is an epimorphism
  because exactness at `j` makes `Xⁱ ⟶ Zʲ` surjective (Mathlib's `Exact.epi_toCycles`,
  through the isomorphism `X.cyclesIsoSc'`).
- `isZero_rightDerived_cycles F X hX m hm hacyc i n`: let `X : CochainComplex C ℤ` be acyclic,
  with `X.X i` zero for every `i < m` and every term `F`-acyclic. Then every `Zⁱ = X.cycles i`
  is `F`-acyclic. Proof: for `i < m`, `Zⁱ` is a subobject of the zero object `X.X i`, hence
  zero. For `i ≥ m - 1`, by induction on `i` (`Int.leInduction` from `m - 1`, simultaneously
  for all `n`): the short exact sequence `0 ⟶ Zⁱ ⟶ Xⁱ ⟶ Zⁱ⁺¹ ⟶ 0` has `F`-acyclic middle
  term, so Worker 61's `DerivedPlus.isIso_rightDerivedδ_of_isZero` makes the connecting map
  `DerivedPlus.rightDerivedδ : Rⁿ⁺¹F Zⁱ⁺¹ ⟶ Rⁿ⁺²F Zⁱ` an isomorphism, and its target is zero
  by the induction hypothesis.
- `acyclic_map F X hX m hm hacyc` (the key lemma), with `F` preserving finite limits and the
  same hypotheses on `X`: the complex `F X` is acyclic. Proof in degree `i`: each of the three
  short exact sequences `0 ⟶ Zᵏ ⟶ Xᵏ ⟶ Zᵏ⁺¹ ⟶ 0` for `k = i - 1, i, i + 1` has `F`-acyclic
  first term, so Worker 61's `DerivedPlus.shortExact_map_of_isZero_rightDerived_one` shows
  that `F` keeps it short exact. Then `F Xⁱ⁻¹ ⟶ F Xⁱ ⟶ F Zⁱ⁺¹` is exact: it maps to the exact
  `F Zⁱ ⟶ F Xⁱ ⟶ F Zⁱ⁺¹` by `F (X.toCycles (i - 1) i)` (an epimorphism) and identities, so
  Mathlib's `ShortComplex.exact_iff_of_epi_of_isIso_of_mono` applies. It also maps to
  `F Xⁱ⁻¹ ⟶ F Xⁱ ⟶ F Xⁱ⁺¹`, the short complex of `F X` in degree `i`, by identities and the
  monomorphism `F (X.iCycles (i + 1))`, so the same lemma gives exactness of `F X` at `i`.
- `quasiIso_iff_acyclic_mappingCone f`, for `f : K ⟶ L` in `CochainComplex C ℤ` (no
  derived-category hypothesis): `f` is a quasi-isomorphism if and only if
  `CochainComplex.mappingCone f` is acyclic. Proof: in the homotopy category, quasi-isomorphisms
  are the morphisms whose cone lies in the subcategory of acyclic complexes
  (`HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic`); the mapping cone triangle of `f` is
  distinguished (`HomotopyCategory.mappingCone_triangleh_distinguished`), and
  `ObjectProperty.trW_iff_of_distinguished` evaluates the condition on its third object.
- `quasiIso_map F ε hK I φ hφ`: with `[HasDerivedCategory]` instances, `[EnoughInjectives C]`,
  and `F` preserving finite limits, conclusion 1 of the theorem.

## Proof of `quasiIso_map`

1. `ε ≫ φ = I.ι` is a quasi-isomorphism, and so is `ε`; by two-out-of-three
   (`quasiIso_of_comp_left`), `φ` is a quasi-isomorphism.
2. Let `e := ComplexShape.embeddingUpNat`, and let `φ' := HomologicalComplex.extendMap φ e` be
   the extension of `φ` by zero to integer-indexed complexes, `K.extend e ⟶ I.cocomplex.extend e`.
   It is a quasi-isomorphism (`HomologicalComplex.quasiIso_extendMap_iff`), so its mapping
   cone `M := CochainComplex.mappingCone φ'` is acyclic by `quasiIso_iff_acyclic_mappingCone`.
3. `M` satisfies the hypotheses of `acyclic_map` with `m = -1`. For `i < -1`, `Mⁱ` is zero
   because both `(K.extend e).X (i + 1)` and `(I.cocomplex.extend e).X i` are zero, the degrees
   being negative (`CochainComplex.mappingCone.isZero_X_iff`, `isZero_extend_X`). Every `Mⁱ` is
   isomorphic to `(K.extend e).X (i + 1) ⊞ (I.cocomplex.extend e).X i`
   (`HomologicalComplex.homotopyCofiber.XIsoBiprod`). Each term of an extended complex is
   either zero or isomorphic to a term of the original complex
   (`HomologicalComplex.extend.XIso`), so it is `F`-acyclic: the terms of `K` by hypothesis and
   those of `I.cocomplex` because they are injective
   (`Functor.isZero_rightDerived_obj_injective_succ`). By the biproduct helper, `Mⁱ` is
   `F`-acyclic.
4. By `acyclic_map`, `F M` is acyclic. Mathlib's
   `CochainComplex.mappingCone.mapHomologicalComplexIso` identifies `F M` with the mapping cone
   of `F φ'`, so that cone is acyclic and `F φ'` is a quasi-isomorphism.
5. The Library's `extendMapIso e F` identifies `F (L.extend e)` with `(F L).extend e`, and
   `extendMapIso_hom_naturality` says that it carries `F φ'` to
   `HomologicalComplex.extendMap (F φ) e`. Quasi-isomorphisms are stable under isomorphism of
   arrows (`quasiIso_iff_of_arrow_mk_iso`), so `extendMap (F φ) e` is a quasi-isomorphism, and by
   `quasiIso_extendMap_iff` so is `F φ`.

## Proof of the theorem

After introducing the data, the proof supplies the instances that the statement does not
assume: `EnoughInjectives C`, whose injective presentation of `X` is the degree-zero map
`(injectiveResolution X).ι.f 0` of Mathlib's chosen injective resolution (a monomorphism into
an injective object), and Mathlib's `HasDerivedCategory.standard C` and
`HasDerivedCategory.standard D`. These local instances do not occur in the statement, so
conclusion 1 is `quasiIso_map F ε hK I φ hφ`. For conclusion 2, `Hⁿ(F ·).map φ` is the
homology map of the quasi-isomorphism `F φ` in degree `n`, an isomorphism by
`quasiIsoAt_iff_isIso_homologyMap`; composing with the inverse of the isomorphism
`I.isoRightDerivedObj F n` gives an isomorphism (`IsIso.comp_isIso'`).

`lean_check` reports that the theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`, and that its universe parameters are `u v u' v'`.
