# Naturality of the hyperext abutment filtration

Author: Worker 61. Built on the Library module
`Langlands.Cohomology.HyperextAbutmentFiltration` (`filtration`, `graded`,
`mem_filtration_iff`, `mem_filtration_iff_truncLTι_comp_eq_zero`,
`edgeMapAddMonoidHom`, `edgeMap_comp`; Worker 61), which imports
`Langlands.Cohomology.HyperextDegeneration.Statement` (`edgeMap`; Worker 3),
and on Mathlib's t-structures and its canonical t-structure on derived
categories.

Let `t` be a t-structure on a pretriangulated category `C`, and let `K` and
`B` be objects of `C`. The abutment filtration of `HyperextAbutmentFiltration`
is the decreasing filtration `F^p = filtration t K B n p` of
`Hom(K, B⟦n⟧)`. A morphism lies in `F^p` when it factors through
`K ⟶ τ_{≥ p - n} K`, equivalently when it vanishes on `τ_{< p - n} K`. Its
graded pieces are `gr^p = graded t K B n p = F^p / F^{p+1}`. This module
proves that the filtration and its graded pieces are functorial:
contravariantly in `K` (precomposition) and covariantly in `B`
(postcomposition with the shifted morphism). It also proves that the edge map
of `HyperextDegenerationStatement` is natural in the coefficient object `W`.
The edge map's naturality in `K` is `edgeMap_comp` of
`HyperextAbutmentFiltration`.

## Composition maps

Section `Composition` takes a preadditive category `C` with objects in
`Type u`, morphisms in `Type v` and a shift by `ℤ`. `ShiftedHom K B n` is
Mathlib's type of morphisms `K ⟶ B⟦n⟧`, an additive group, and `ψ⟦n⟧'` is
the image of `ψ` under the shift functor by `n`.

| Declaration | Statement |
| --- | --- |
| `precomp φ B n` | For `φ : K' ⟶ K`, the additive map `ShiftedHom K B n →+ ShiftedHom K' B n`, `f ↦ φ ≫ f` (Mathlib's `Preadditive.leftComp`). |
| `precomp_apply` | `precomp φ B n f = φ ≫ f` (a `simp` lemma, by definition). |
| `postcomp K ψ n` | For `ψ : B ⟶ B'`, the additive map `ShiftedHom K B n →+ ShiftedHom K B' n`, `f ↦ f ≫ ψ⟦n⟧'` (Mathlib's `Preadditive.rightComp`). |
| `postcomp_apply` | `postcomp K ψ n f = f ≫ ψ⟦n⟧'` (a `simp` lemma, by definition). |

## Any t-structure

Section `TStructure` has the hypotheses of the same section of
`HyperextAbutmentFiltration`: `C` is preadditive, has a zero object and a
shift by `ℤ` by additive functors, and is pretriangulated; `t : TStructure C`.
No `IsTriangulated C` is needed. Below, `F^p(K, B)` stands for
`filtration t K B n p` and `gr^p(K, B)` for `graded t K B n p`.

| Declaration | Statement |
| --- | --- |
| `precomp_mem_filtration φ hf` | If `f ∈ F^p(K, B)`, then `precomp φ B n f ∈ F^p(K', B)`. |
| `postcomp_mem_filtration ψ hf` | If `f ∈ F^p(K, B)`, then `postcomp K ψ n f ∈ F^p(K, B')`. |
| `filtrationPrecomp t φ B n p` | The additive map `F^p(K, B) →+ F^p(K', B)` induced by `precomp φ B n` (restricted to `F^p(K, B)` and corestricted to `F^p(K', B)`). |
| `filtrationPostcomp t K ψ n p` | The additive map `F^p(K, B) →+ F^p(K, B')` induced by `postcomp K ψ n`. |
| `coe_filtrationPrecomp`, `coe_filtrationPostcomp` | The underlying morphisms are `φ ≫ f` and `f ≫ ψ⟦n⟧'` (`simp` lemmas, by definition). |
| `gradedPrecomp t φ B n p` | The additive map `gr^p(K, B) →+ gr^p(K', B)` induced by `filtrationPrecomp` (Mathlib's `QuotientAddGroup.map`; well defined because `F^{p+1}` is mapped into `F^{p+1}`). |
| `gradedPostcomp t K ψ n p` | The additive map `gr^p(K, B) →+ gr^p(K, B')` induced by `filtrationPostcomp`. |
| `gradedPrecomp_mk`, `gradedPostcomp_mk` | On the class of `f ∈ F^p`, these maps give the class of the image of `f` (`simp` lemmas, by definition). |
| `filtrationPrecomp_id`, `gradedPrecomp_id` | For `φ = 𝟙 K` the maps are identities. |
| `filtrationPrecomp_comp`, `gradedPrecomp_comp` | For `φ' : K'' ⟶ K'` and `φ : K' ⟶ K`, the map for `φ' ≫ φ` is the map for `φ` followed by the map for `φ'`. |
| `filtrationPostcomp_id`, `gradedPostcomp_id` | For `ψ = 𝟙 B` the maps are identities. |
| `filtrationPostcomp_comp`, `gradedPostcomp_comp` | For `ψ : B ⟶ B'` and `ψ' : B' ⟶ B''`, the map for `ψ ≫ ψ'` is the map for `ψ` followed by the map for `ψ'`. |
| `filtrationPrecomp_comp_filtrationPostcomp`, `gradedPrecomp_comp_gradedPostcomp` | For `φ : K' ⟶ K` and `ψ : B ⟶ B'`, postcomposing then precomposing equals precomposing then postcomposing, as maps `F^p(K, B) →+ F^p(K', B')`, respectively `gr^p(K, B) →+ gr^p(K', B')`. |

So `K ↦ F^p(K, B)` and `K ↦ gr^p(K, B)` are contravariant, and
`B ↦ F^p(K, B)` and `B ↦ gr^p(K, B)` are covariant, functors to additive
groups, and the two variances commute. These functors are not packaged as
Mathlib `Functor` objects.

Proofs.

- `precomp_mem_filtration`: by `mem_filtration_iff_truncLTι_comp_eq_zero`,
  `f` vanishes on `τ_{< p - n} K`. The naturality of
  `t.truncLTι (p - n) : τ_{< p - n} ⟶ 𝟭` gives
  `(τ_{< p - n} K' ⟶ K') ≫ φ = τ_{< p - n}(φ) ≫ (τ_{< p - n} K ⟶ K)`, so
  `φ ≫ f` vanishes on `τ_{< p - n} K'`.
- `postcomp_mem_filtration`: if `f = π ≫ g` with
  `π : K ⟶ τ_{≥ p - n} K`, then `f ≫ ψ⟦n⟧' = π ≫ (g ≫ ψ⟦n⟧')` by
  associativity (`mem_filtration_iff`).
- The maps on `F^p` are Mathlib's `AddMonoidHom.codRestrict` of the composite
  of `precomp` or `postcomp` with the inclusion of `F^p`, using the previous
  lemmas. The maps on `gr^p` are `QuotientAddGroup.map`; the required
  inclusion is the previous lemma at `p + 1`, after unfolding
  `AddSubgroup.mem_comap` and `AddSubgroup.mem_addSubgroupOf`.
- The identity and composition lemmas on `F^p` reduce, after `ext`, to
  `Category.id_comp`, `Category.assoc`, `Functor.map_id` and
  `Functor.map_comp` of the shift functor. On `gr^p` they follow from those on
  `F^p` by Mathlib's `QuotientAddGroup.addMonoidHom_ext`, which reduces an
  equality of maps out of a quotient to their values on classes.

## Derived categories and the edge map

Section `Derived` takes an abelian category `C` with objects in `Type u` and
morphisms in `Type v` and an instance `HasDerivedCategory.{w} C`. `W₀` denotes
`(DerivedCategory.singleFunctor C 0).obj W`, the object `W` placed in degree
`0`, and `H^i` is `DerivedCategory.homologyFunctor C i`. The edge map
`HyperextDegeneration.edgeMap K W n : Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)` sends
a morphism to the morphism it induces on `H^{-n}`, followed by the
identification `H^0(W₀) ≅ W`.

| Declaration | Statement |
| --- | --- |
| `edgeMap_postcomp K ψ n f` | For `ψ : W ⟶ W'` and `f : ShiftedHom K W₀ n`: `edgeMap K W' n (postcomp K ((singleFunctor C 0).map ψ) n f) = edgeMap K W n f ≫ ψ`. |
| `edgeMapAddMonoidHom_comp_postcomp K ψ n` | The same as an equality of additive maps `ShiftedHom K W₀ n →+ (H^{-n} K ⟶ W')`: the edge map after `postcomp` equals postcomposition with `ψ` after the edge map. |
| `edgeMapAddMonoidHom_comp_precomp φ W n` | For `φ : X ⟶ K`: the edge map for `X` after `precomp φ W₀ n` equals precomposition with `H^{-n}(φ)` after the edge map for `K` (a restatement of `edgeMap_comp`). |

Proofs.

- `edgeMap_postcomp`: unfold `edgeMap` and use Mathlib's
  `Functor.shiftMap_comp` (the `shiftMap` of `f ≫ g⟦n⟧'` is the `shiftMap` of
  `f` followed by `H^0(g)`), then the naturality of
  `singleFunctorCompHomologyFunctorIso C 0` at `ψ`, and associativity.
- The two equalities of additive maps follow by `ext` from
  `edgeMap_postcomp` and `edgeMap_comp`.

## Provenance and interpretation

The statements and proofs are ours, assembled from Mathlib and the Library.
Functoriality of the abutment filtration of a hypercohomology spectral
sequence in both arguments is standard. It was suggested as a following unit
by Worker 13 (first executor of the task), after the abutment filtration
module was published.

For this module Worker 61 read the following passage of Harris 1999 in the
rendered scan of the PDF:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`),
  Proposition 4.10, printed p.311 (one-based PDF page 13), after the
  spectral sequence (4.10.1): "Moreover, as `K(N)^{ℓ,p}` varies the spectral
  sequences are `GG(𝔸_f^{ℓ,p})`-equivariant."

Interpretation (explanation only). Equivariance of Harris's spectral
sequence and of the resulting isomorphism (5.2) is a naturality statement:
the group, or a Hecke algebra, acts on the complex `K` and on the coefficients
`W` through morphisms, and the constructions commute with these morphisms.
The lemmas of this module provide this compatibility for the abutment
filtration, its graded pieces and the edge map, for arbitrary morphisms
`K' ⟶ K` and `W ⟶ W'`. No group action, Hecke operator or level change is
formalized here, and no equivariance statement is made.

## Scope

- Only functoriality is proved. The maps are not shown to be compatible with
  the identifications of `gr^p` with page terms (none is formalized), and no
  statement about the spectral sequence `hyperextSpectralSequence` is made.
- Naturality is stated for single morphisms, not as Mathlib functors or
  natural transformations.
- All maps are additive. No linearity over a coefficient ring, equivariance
  or level structure appears.
- `HasDerivedCategory.{w} C` is a hypothesis; the results hold for each such
  instance.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
p.311 read in the rendered scan for this module.

Dependencies: `Langlands.Cohomology.HyperextAbutmentFiltration`, with Mathlib
pinned to Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
