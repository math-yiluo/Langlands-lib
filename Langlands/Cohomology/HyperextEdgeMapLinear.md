# Linearity of the cohomology functors and of the hyperext edge map

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextAbutmentFiltration` (`edgeMapAddMonoidHom`;
Worker 61), which imports `Langlands.Cohomology.HyperextDegeneration.Statement`
(`HyperextDegenerationStatement`, `HyperextDegeneration.edgeMap`; Worker 3),
and `Langlands.Representation.Category.Abelian` (the abelian category
`SmoothRep R G`), and on Mathlib's `R`-linear structures on homological
complexes, short complexes and derived categories.

Let `R` be a ring and `C` an `R`-linear abelian category. Mathlib makes the
derived category `DerivedCategory C` an `R`-linear category, and its
localization functor `DerivedCategory.Q`, shift functors and single functors
`R`-linear (`Mathlib.Algebra.Homology.DerivedCategory.Linear`). Mathlib
records `R`-linearity of the homology functor of short complexes, but not of
the homology functor of homological complexes or of the cohomology functors
`H^n = DerivedCategory.homologyFunctor C n`. This module proves these
linearity statements. It then shows that the edge map

`HyperextDegeneration.edgeMap K W n : Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)`

is `R`-linear, where `W₀` is `W` placed in degree `0`. Both groups of
morphisms are `R`-modules through the `R`-linear structures of
`DerivedCategory C` and `C`. Under Worker 3's proposition
`HyperextDegenerationStatement`, the edge map is therefore an `R`-linear
equivalence. This module does not prove `HyperextDegenerationStatement`; it
takes the proposition as an explicit hypothesis `h`.

## Linearity of homology functors

Section `Complexes` takes a ring `R : Type t`, a preadditive `R`-linear
category `C` with objects in `Type u` and morphisms in `Type v`, and a
complex shape `c` on `ι : Type uι`. All declarations are instances.

| Declaration | Statement |
| --- | --- |
| `shortComplexFunctor'_linear R C c i j k` | `HomologicalComplex.shortComplexFunctor' C c i j k`, sending `K` to the short complex `K.X i ⟶ K.X j ⟶ K.X k`, is `R`-linear. |
| `shortComplexFunctor_linear R C c i` | `HomologicalComplex.shortComplexFunctor C c i`, sending `K` to its short complex at `i`, is `R`-linear. |
| `homologicalComplexHomologyFunctor_linear R C c i` | If `C` has homology (`CategoryWithHomology C`), the homology functor `HomologicalComplex.homologyFunctor C c i` is `R`-linear. |

Section `Derived` takes a ring `R`, an abelian `R`-linear category `C` and an
instance `HasDerivedCategory.{w} C`.

| Declaration | Statement |
| --- | --- |
| `homologyFunctor_linear R C n` | The cohomology functor `DerivedCategory.homologyFunctor C n : DerivedCategory C ⥤ C` is `R`-linear (an instance). |

Proofs.

- `shortComplexFunctor'_linear`: a morphism of short complexes is
  determined by its three components (`ext`). The components of the image of
  `r • f` are `r • f.f i`, `r • f.f j` and `r • f.f k` by definition of the
  scalar actions on morphisms of homological complexes and of short
  complexes (`rfl`).
- `shortComplexFunctor_linear`: `shortComplexFunctor C c i` is by definition
  `shortComplexFunctor' C c (c.prev i) i (c.next i)`.
- `homologicalComplexHomologyFunctor_linear`: Mathlib's
  `HomologicalComplex.homologyFunctorIso` identifies the homology functor
  with the composite of `shortComplexFunctor C c i` and the homology functor
  of short complexes, which Mathlib proves `R`-linear
  (`ShortComplex.homologyFunctor_linear`). A functor isomorphic to an
  `R`-linear functor is `R`-linear (`Functor.linear_of_iso`).
- `homologyFunctor_linear`: Mathlib's `DerivedCategory.homologyFunctorFactors`
  identifies `Q ⋙ H^n` with the homology functor of cochain complexes in
  degree `n`, where `Q` is the localization functor at quasi-isomorphisms. This
  identification is supplied as a `Localization.Lifting` structure. Mathlib's
  `Localization.functor_linear_iff` says that for an `R`-linear localization
  functor, a lifted functor is `R`-linear if and only if the original functor
  is. The previous instance gives the original functor's linearity.

## The edge map

Still in section `Derived`, with `K : DerivedCategory C`, `W : C` and
`n : ℤ`. `ShiftedHom K W₀ n` is Mathlib's type of morphisms `K ⟶ W₀⟦n⟧`.

| Declaration | Statement |
| --- | --- |
| `edgeMap_smul K W n r f` | `edgeMap K W n (r • f) = r • edgeMap K W n f` for `r : R`. |
| `edgeMapLinearMap R K W n` | The edge map as an `R`-linear map `ShiftedHom K W₀ n →ₗ[R] (H^{-n} K ⟶ W)`. A `def`. |
| `edgeMapLinearMap_apply` | `edgeMapLinearMap R K W n f = edgeMap K W n f` (a `simp` lemma, by definition). |
| `edgeMapLinearMap_toAddMonoidHom` | The underlying additive map of `edgeMapLinearMap R K W n` is the Library's `edgeMapAddMonoidHom K W n` (by definition). |

With an additional instance `HasExt.{w'} C`, and with
`h : HyperextDegenerationStatement.{w, w'} C`,
`hK : ∀ i : ℤ, b < i → IsZero (H^i K)` and
`hW : ∀ (k : ℤ) (i : ℕ), 0 < i → Subsingleton (Abelian.Ext.{w'} (H^k K) W i)`:

| Declaration | Statement |
| --- | --- |
| `degenerationLinearEquiv R h K b hK W hW n` | The `R`-linear equivalence `ShiftedHom K W₀ n ≃ₗ[R] (H^{-n} K ⟶ W)` whose underlying map is the edge map: Mathlib's `LinearEquiv.ofBijective` applied to `edgeMapLinearMap R K W n` and the bijectivity `h K b hK W hW n`. A `def`. |
| `degenerationLinearEquiv_apply` | `degenerationLinearEquiv R h K b hK W hW n f = edgeMap K W n f` (a `simp` lemma, by definition). |

Section `Smooth` takes a commutative ring `R : Type u`, a group `G : Type u`
with a topology, and an instance `HasDerivedCategory.{w}` for the category
`SmoothRep.{u, u, u} R G` of smooth representations. This category is
`R`-linear by Mathlib's instances for `Rep R G` and for full subcategories
(`CategoryTheory.Linear.fullSubcategory`), and abelian by the Library's
`SmoothRep.abelian`.

| Declaration | Statement |
| --- | --- |
| `smoothEdgeMapLinearMap R G K W n` | For `K : DerivedCategory (SmoothRep R G)` and `W : SmoothRep R G`, the edge map as an `R`-linear map, i.e. `edgeMapLinearMap R K W n` in this category. A `def`. |
| `smoothEdgeMapLinearMap_apply` | Its value at `f` is `edgeMap K W n f` (a `simp` lemma, by definition). |

Proofs.

- `edgeMap_smul`: the edge map is
  `(H^0).shiftMap f (-n) 0 _ ≫ ε_W`, where `shiftMap` is
  `(H^0).shift (-n)` applied to `f`, followed by an isomorphism, and `ε_W` is
  the isomorphism `H^0(W₀) ≅ W`. The functor `(H^0).shift (-n)` is by
  definition `H^{-n}`, which is `R`-linear by `homologyFunctor_linear`; so
  `r • f` is sent to `r • H^{-n}(f)`. Composition is `R`-bilinear in an
  `R`-linear category (`Linear.smul_comp`).
- `edgeMapLinearMap`: additivity is that of `edgeMapAddMonoidHom`, and
  compatibility with scalars is `edgeMap_smul`.
- The equivalence and the smooth map are direct applications.

## Provenance and interpretation

The statements and proofs are ours, assembled from Mathlib and the Library.
Linearity of homology and cohomology functors over the ring of scalars is
standard. Worker 13, the first executor of the task, asked Worker 61 to
continue towards the specialization of the degeneration isomorphism to
Harris's (5.2). The isotypic components in (5.2) need linear structure,
which an additive isomorphism does not record.

For this module Worker 61 read the following passages of Harris 1999 in the
rendered scans of the PDF:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`),
  Proposition 4.10, printed p.311 (one-based PDF page 13): "There is a
  spectral sequence of `𝒪`-modules" (4.10.1), and "Here `Ext^i` denotes the
  `i`-th derived functor of `Hom` in the category of smooth
  `L_ℓ[GJ]`-modules."
- The same article, §5, printed p.312 (one-based PDF page 14): the
  isomorphism (5.2)
  `Hom_GJ(H_c^{2(n-1)-j}(M̆_N, 𝒪(n - 1)), 𝒜_ℓ(GJ, ρ, H)[π^v])[JL(π_v)] ≅ H^j(S̄_K(N), W̃)[π]`.

Interpretation (explanation only). Harris's spectral sequence (4.10.1) is a
spectral sequence of `𝒪`-modules, and the Ext groups are taken in the
category of smooth `L_ℓ[GJ]`-modules. In this module `R` plays the role of
the coefficient ring, and the edge map and the degeneration isomorphism are
`R`-linear. The isotypic components in (5.2) are defined using this linear
structure together with group actions; they are not formalized here.
(5.2) is stated for the selected components `𝒜_ℓ(GJ, ρ, H)[π^v]`,
`[JL(π_v)]` and `[π]`, not for the whole module `𝒜_ℓ(GJ, ρ, H)`. This
module claims no Ext vanishing for the whole module; the hypothesis `hW`
concerns the chosen `W` only.

## Scope

- `HyperextDegenerationStatement` is a hypothesis of
  `degenerationLinearEquiv`; it is not proved here.
- Only linearity over the scalar ring `R` of the category is treated. No
  group action, Hecke equivariance or isotypic component appears. For
  smooth representations only the edge map is given as a linear map; no
  linear equivalence with a hypothesis on smooth Ext groups is stated.
- `HasDerivedCategory` and `HasExt` are hypotheses; the results hold for each
  such instance. In the smooth section `R` and `G` share the universe `u`, as
  in `SmoothRep.{u, u, u} R G`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.311-312 read in the rendered scans for this module.

Dependencies: `Langlands.Cohomology.HyperextAbutmentFiltration`,
`Langlands.Representation.Category.Abelian`,
`Mathlib.Algebra.Homology.DerivedCategory.Linear`,
`Mathlib.Algebra.Homology.ShortComplex.Linear` and
`Mathlib.Algebra.Homology.Linear`, with Mathlib pinned to Lean 4.34.0 and
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
