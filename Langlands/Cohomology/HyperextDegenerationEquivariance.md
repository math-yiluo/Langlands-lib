# Equivariance of the hyperext edge map and of the degeneration isomorphism

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextAbutmentNaturality` (`precomp`, `postcomp`,
`precomp_mem_filtration`, `postcomp_mem_filtration`, `edgeMap_postcomp`;
Worker 61) and `Langlands.Cohomology.HyperextDegenerationIso`
(`degenerationAddEquiv`, `smoothDegenerationAddEquiv`; Worker 61). These
import `Langlands.Cohomology.HyperextAbutmentFiltration` (`filtration`,
`edgeMapAddMonoidHom`, `edgeMap_comp`; Worker 61) and
`Langlands.Cohomology.HyperextDegeneration.Statement`
(`HyperextDegenerationStatement`, `HyperextDegeneration.edgeMap`; Worker 3).

Let `C` be an abelian category, `K` an object of its derived category and `W`
an object of `C`. Write `W₀` for `W` placed in degree `0` and `H^i` for the
cohomology functor in degree `i`. The edge map
`HyperextDegeneration.edgeMap K W n : Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)`
sends a morphism to the morphism it induces on `H^{-n}`. Let a group `Γ` act
on `K` and on `W` by automorphisms, through group homomorphisms
`ρ : Γ →* Aut K` and `σ : Γ →* Aut W`. This module defines the induced
actions of `Γ` on `Hom(K, W₀⟦n⟧)` and on `Hom(H^{-n} K, W)`. It proves that
the edge map intertwines them, and so do the degeneration isomorphism of
`HyperextDegenerationIso` and its inverse. The degeneration isomorphism
therefore restricts to an additive isomorphism between the subgroups of
`Γ`-fixed elements.

An action by additive automorphisms is a group homomorphism
`Γ →* AddMonoid.End A` into the monoid of additive endomorphisms of `A`.
Multiplication in `AddMonoid.End A` is composition, so such a homomorphism
is a left action of `Γ` on `A` by additive maps, each of them invertible with
inverse the image of `γ⁻¹`. In Mathlib `Aut X` is the group of
automorphisms of `X`, with `(α * β).hom = β.hom ≫ α.hom`.

This module does not prove `HyperextDegenerationStatement`. The
degeneration isomorphisms take it as an explicit hypothesis `h`, as in
`HyperextDegenerationIso`.

## Actions on groups of morphisms

Section `Hom` takes a preadditive category `C` with objects in `Type u` and
morphisms in `Type v`, and a group `Γ : Type uΓ`.

| Declaration | Statement |
| --- | --- |
| `homAddEquiv α β` | For isomorphisms `α : X ≅ X'` and `β : Y ≅ Y'`, the additive isomorphism `(X ⟶ Y) ≃+ (X' ⟶ Y')`, `f ↦ α⁻¹ ≫ f ≫ β` (Mathlib's `Iso.homCongr`). A `def`. |
| `homAddEquiv_apply` | `homAddEquiv α β f = α.inv ≫ f ≫ β.hom` (a `simp` lemma, by definition). |
| `homAction ρ σ` | For `ρ : Γ →* Aut X` and `σ : Γ →* Aut Y`, the action `Γ →* AddMonoid.End (X ⟶ Y)` sending `γ` to `homAddEquiv (ρ γ) (σ γ)`, so `γ` sends `f` to `(ρ γ)⁻¹ ≫ f ≫ σ γ`. A `def`. |
| `homAction_apply` | `homAction ρ σ γ f = (ρ γ).inv ≫ f ≫ (σ γ).hom` (by definition). |

Section `Fixed` takes a group `Γ`.

| Declaration | Statement |
| --- | --- |
| `fixedAddSubgroup a` | For an additive group `A` and `a : Γ →* AddMonoid.End A`, the additive subgroup `{x | ∀ γ, a γ x = x}` of `Γ`-fixed elements. A `def`. |
| `mem_fixedAddSubgroup_iff` | `x ∈ fixedAddSubgroup a ↔ ∀ γ, a γ x = x` (by definition). |
| `fixedAddEquiv a b e he` | For actions `a` on `A` and `b` on `B` and an additive isomorphism `e : A ≃+ B` with `he : ∀ γ x, e (a γ x) = b γ (e x)`, the additive isomorphism `fixedAddSubgroup a ≃+ fixedAddSubgroup b` given by `e` and `e.symm`. A `def`. |
| `coe_fixedAddEquiv_apply` | The underlying element of `fixedAddEquiv a b e he x` is `e x` (a `simp` lemma, by definition). |

Proofs.

- `homAction` is a group homomorphism: `ρ 1` is the identity automorphism,
  so `(ρ 1).inv = 𝟙 X`, and `(ρ (γ * δ)).inv = (ρ γ).inv ≫ (ρ δ).inv`; the
  same holds for `σ` with `hom` in the opposite order. Both identities follow
  from `map_one` and `map_mul` of `ρ` and `σ` and the definition of the group
  structure on `Aut`; the rest is associativity of composition.
- `fixedAddSubgroup` is closed under addition, zero and negation because each
  `a γ` is additive.
- `fixedAddEquiv`: `e x` is fixed by `he`. For fixed `y`, `e.symm y` is fixed
  because `e` is injective and `e (a γ (e.symm y)) = b γ y = y`.

## The abutment and the edge map

Section `Derived` takes an abelian category `C` with objects in `Type u` and
morphisms in `Type v`, an instance `HasDerivedCategory.{w} C`, and a group
`Γ`. Below, `K : DerivedCategory C`, `W : C`, `ρ : Γ →* Aut K` and
`σ : Γ →* Aut W`. `ShiftedHom K W₀ n` is Mathlib's type of morphisms
`K ⟶ W₀⟦n⟧`.

| Declaration | Statement |
| --- | --- |
| `abutmentAction ρ σ n` | The action `Γ →* AddMonoid.End (ShiftedHom K W₀ n)`: `homAction` for `ρ` and for the action on `W₀⟦n⟧` obtained from `σ` by applying the functor `singleFunctor C 0 ⋙ shiftFunctor _ n` (Mathlib's `Functor.mapAut`). A `def`. |
| `cohomologyHomAction ρ σ n` | The action `Γ →* AddMonoid.End (H^{-n} K ⟶ W)`: `homAction` for the action on `H^{-n} K` obtained from `ρ` by applying `H^{-n}`, and for `σ`. A `def`. |
| `abutmentAction_apply` | `abutmentAction ρ σ n γ f = postcomp K ((singleFunctor C 0).map (σ γ).hom) n (precomp (ρ γ).inv _ n f)`, i.e. `(ρ γ)⁻¹ ≫ f ≫ ((σ γ)₀)⟦n⟧'`. |
| `cohomologyHomAction_apply` | `cohomologyHomAction ρ σ n γ g = H^{-n}((ρ γ).inv) ≫ g ≫ (σ γ).hom` (by definition). |
| `edgeMap_abutmentAction ρ σ n γ f` | `edgeMap K W n (abutmentAction ρ σ n γ f) = cohomologyHomAction ρ σ n γ (edgeMap K W n f)`: the edge map intertwines the two actions. |
| `edgeMapAddMonoidHom_comp_abutmentAction ρ σ n γ` | The same as an equality of additive maps `ShiftedHom K W₀ n →+ (H^{-n} K ⟶ W)`. |
| `abutmentAction_mem_filtration t ρ σ γ hf` | For any t-structure `t` on `DerivedCategory C`: if `f` lies in the step `F^p = filtration t K W₀ n p` of the abutment filtration, then so does `abutmentAction ρ σ n γ f`. |

Proofs.

- `abutmentAction_apply` is associativity of composition.
- `edgeMap_abutmentAction`: rewrite with `abutmentAction_apply`, then with
  `edgeMap_postcomp` (naturality of the edge map in `W`) and `edgeMap_comp`
  (naturality in `K`), and finish with associativity.
- `abutmentAction_mem_filtration`: `precomp_mem_filtration` and then
  `postcomp_mem_filtration`.

## The degeneration isomorphism

Still in section `Derived`, with an additional instance `HasExt.{w'} C`. In
the declarations below, `h : HyperextDegenerationStatement.{w, w'} C`, `hK`
is the hypothesis `∀ i : ℤ, b < i → IsZero (H^i K)`, and `hW` is the
hypothesis
`∀ (k : ℤ) (i : ℕ), 0 < i → Subsingleton (Abelian.Ext.{w'} (H^k K) W i)`,
exactly as for `degenerationAddEquiv h K b hK W hW n`.

| Declaration | Statement |
| --- | --- |
| `degenerationAddEquiv_abutmentAction h b hK hW n ρ σ γ f` | `degenerationAddEquiv h K b hK W hW n (abutmentAction ρ σ n γ f) = cohomologyHomAction ρ σ n γ (degenerationAddEquiv h K b hK W hW n f)`. |
| `degenerationAddEquiv_symm_cohomologyHomAction h b hK hW n ρ σ γ g` | The inverse isomorphism intertwines the actions: `(degenerationAddEquiv h K b hK W hW n).symm (cohomologyHomAction ρ σ n γ g) = abutmentAction ρ σ n γ ((degenerationAddEquiv h K b hK W hW n).symm g)`. |
| `degenerationFixedAddEquiv h b hK hW n ρ σ` | The additive isomorphism `fixedAddSubgroup (abutmentAction ρ σ n) ≃+ fixedAddSubgroup (cohomologyHomAction ρ σ n)` given by `fixedAddEquiv` applied to `degenerationAddEquiv`: the `Γ`-fixed elements of `Hom(K, W₀⟦n⟧)` correspond to the `Γ`-fixed elements of `Hom(H^{-n} K, W)`. A `def`. |
| `coe_degenerationFixedAddEquiv_apply` | The underlying morphism of `degenerationFixedAddEquiv h b hK hW n ρ σ f` is `edgeMap K W n f` (a `simp` lemma, by definition). |

Section `Smooth` takes a commutative ring `R : Type u`, a topological group
`G : Type u`, instances `HasDerivedCategory.{w}` and `HasExt.{w'}` for the
category `SmoothRep.{u, u, u} R G` of smooth representations, and a group
`Γ`. Here `hW` is the smooth-Ext hypothesis of `smoothDegenerationAddEquiv`:
`(SmoothExt.ext R G (H^k K) i).obj W` is trivial for every `k : ℤ` and every
`i : ℕ` with `0 < i`.

| Declaration | Statement |
| --- | --- |
| `smoothDegenerationAddEquiv_abutmentAction R G h b hK hW n ρ σ γ f` | `smoothDegenerationAddEquiv R G h K b hK W hW n` intertwines `abutmentAction ρ σ n` and `cohomologyHomAction ρ σ n`. |
| `smoothDegenerationFixedAddEquiv R G h b hK hW n ρ σ` | The additive isomorphism between the `Γ`-fixed subgroups given by `smoothDegenerationAddEquiv`. A `def`. |

Proofs.

- The underlying map of `degenerationAddEquiv` and of
  `smoothDegenerationAddEquiv` is the edge map by definition, so the
  intertwining lemmas are `edgeMap_abutmentAction`.
- The statement for the inverse follows by injectivity of
  `degenerationAddEquiv` and `AddEquiv.apply_symm_apply`.
- The fixed-point isomorphisms are `fixedAddEquiv` applied to these
  isomorphisms and intertwining lemmas.

## Provenance and interpretation

The definitions, statements and proofs are ours, assembled from Mathlib and
the Library. Inducing actions on groups of morphisms from actions on source
and target, and restricting an equivariant isomorphism to fixed points, are
standard. Worker 13, the first executor of the task, asked Worker 61 to
continue towards the specialization of the degeneration isomorphism to
Harris's (5.2) and to identify the geometric action input it needs. This
module is the part of that specialization that is pure category theory.

For this module Worker 61 read the following passages of Harris 1999:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`),
  Proposition 4.10, printed p.311 (one-based PDF page 13), read in the
  rendered scan, after the spectral sequence (4.10.1): "Moreover, as
  `K(N)^{ℓ,p}` varies the spectral sequences are
  `GG(𝔸_f^{ℓ,p})`-equivariant."
- The same article, §5, printed p.312 (one-based PDF page 14), read in the
  rendered scan and the text layer. Harris uses Proposition 4.10 "to express
  the representation of the decomposition group `Z_v` on the
  `JL(π_f)`-isotypic component of `H^{n-1}(S̄_K(N), W̃)`", and writes, before
  (5.2): "since `π_v` is supercuspidal, the higher Ext's vanish and the
  spectral sequence (4.10.1) degenerates to an isomorphism". The isomorphism
  (5.2) is
  `Hom_GJ(H_c^{2(n-1)-j}(M̆_N, 𝒪(n - 1)), 𝒜_ℓ(GJ, ρ, H)[π^v])[JL(π_v)] ≅ H^j(S̄_K(N), W̃)[π]`.

Interpretation (explanation only). Harris's argument uses compatibility of
(4.10.1), and hence of (5.2), with actions: the action of `GG(𝔸_f^{ℓ,p})`
as the level `K(N)^{ℓ,p}` varies, stated in Proposition 4.10, and the action
of the decomposition group `Z_v`, whose representation on the isotypic
component Harris sets out to express. In this module such symmetries are
modelled by one group `Γ` acting on `K` and on the coefficient `W` by
automorphisms. The lemmas say that the edge map and the degeneration
isomorphism of `HyperextDegenerationIso` commute with the induced actions,
and that the isomorphism restricts to the subgroups of `Γ`-fixed elements.

Harris's (5.2) is stated for selected components, not for the whole module
`𝒜_ℓ(GJ, ρ, H)`. The coefficient module is restricted to its `π^v`-isotypic
part, the `Hom` group to its `JL(π_v)`-isotypic component, and the target to
its `[π]`-component. As explained in `HyperextDegenerationIso`, this module
claims no Ext vanishing for the whole module `𝒜_ℓ(GJ, ρ, H)`; the hypothesis
`hW` concerns the chosen `W` only.

The following inputs to an equivariant specialization to (5.2) are missing.
None is formalized here.

- A complex `K` in the derived category of smooth `GJ`-modules whose
  cohomology `H^{-q} K` is the compactly supported cohomology
  `H_c^{2(n-1)-q}(M̆_N, 𝒪(n - 1))` of the Drinfeld tower, with the action of
  `Z_v` (and of any other group to be compared) given by automorphisms of
  `K` in the derived category that induce the given actions on cohomology.
- The identification of the abutment `Hom(K, W₀⟦j⟧)` with the cohomology
  `H^j(S̄_K(N), W̃)` of the Shimura variety (Proposition 4.10), compatible
  with these actions and with the abutment filtration.
- The coefficient module `𝒜_ℓ(GJ, ρ, H)[π^v]` with its `GJ`- and Hecke
  actions, and a vanishing statement for positive Ext groups in the
  restricted situation of (5.2), derived from supercuspidality of `π_v`.
- Isotypic components (`[JL(π_v)]`, `[π]`) of the two sides. These require
  linear structure over the coefficient ring, which the additive maps of
  this module do not record.

## Scope

- `HyperextDegenerationStatement` is a hypothesis of every degeneration
  isomorphism; it is not proved here.
- Only one group `Γ` acting by automorphisms is treated. Actions of monoids or
  Hecke algebras by non-invertible endomorphisms, continuity or smoothness of
  the actions, and changes of level are not formalized; the fixed-point
  subgroups are taken for the whole group `Γ`.
- All maps are additive. No linearity over a coefficient ring and no
  isotypic components appear.
- The actions are given as `Γ →* AddMonoid.End _`. They are not packaged as
  Mathlib `DistribMulAction` instances or as representations.
- `HasDerivedCategory` and `HasExt` are hypotheses; the results hold for each
  such instance. In the smooth section `R` and `G` share the universe `u`, as
  in `SmoothRep.{u, u, u} R G`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
p.311 (rendered scan) and p.312 (rendered scan and text layer) read for this
module.

Dependencies: `Langlands.Cohomology.HyperextAbutmentNaturality` and
`Langlands.Cohomology.HyperextDegenerationIso`, with Mathlib pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
