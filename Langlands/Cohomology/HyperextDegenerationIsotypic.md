# Isotypic parts of the degeneration isomorphism

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextDegenerationEquivariance` (`homAction`,
`abutmentAction`, `cohomologyHomAction`, `edgeMap_abutmentAction`; Worker 61),
`Langlands.Cohomology.HyperextEdgeMapLinear` (`edgeMapLinearMap`,
`degenerationLinearEquiv`, `R`-linearity of the cohomology functors; Worker 61)
and `Langlands.Cohomology.HyperextDegeneration.Proof`
(`hyperextDegenerationStatement_proof`; Worker 894). Through these it uses
`Langlands.Cohomology.HyperextDegenerationIso` (`subsingleton_ext_of_smoothExt`;
Worker 61) and `Langlands.Cohomology.HyperextDegeneration.Statement`
(`HyperextDegenerationStatement`, `HyperextDegeneration.edgeMap`; Worker 3).

Let `R` be a commutative ring, `C` an `R`-linear abelian category, `K` an
object of its derived category and `W` an object of `C`. Write `W₀` for `W`
placed in degree `0` and `H^i` for the cohomology functor in degree `i`. The
edge map `HyperextDegeneration.edgeMap K W n : Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)`
sends a morphism to the morphism it induces on `H^{-n}`. Let a group `Γ` act on
`K` and on `W` by automorphisms, through `ρ : Γ →* Aut K` and
`σ : Γ →* Aut W`. The module `HyperextDegenerationEquivariance` defines the
induced additive actions of `Γ` on `Hom(K, W₀⟦n⟧)` and on `Hom(H^{-n} K, W)`
and proves that the edge map intertwines them.

This module makes these actions `R`-linear representations of `Γ` (Mathlib's
`Representation R Γ _`, a group homomorphism `Γ →* (_ →ₗ[R] _)`). It proves
that the degeneration isomorphism is an equivalence of representations
(Mathlib's `Representation.Equiv`), and restricts it to isotypic parts, to
multiplicity spaces `Hom_Γ(τ, -)`, to invariants, and, for commuting actions
of two groups, to the action of the second group on the isotypic parts for
the first.

The degeneration isomorphism needs no hypothesis `h` here: bijectivity of the
edge map is the Library's theorem `hyperextDegenerationStatement_proof C`, a
proof of `HyperextDegenerationStatement` for every abelian category `C` with
`HasDerivedCategory` and `HasExt` instances. The remaining hypotheses are those of
that statement: `hK : ∀ i : ℤ, b < i → IsZero (H^i K)` and
`hW : ∀ (k : ℤ) (i : ℕ), 0 < i → Subsingleton (Abelian.Ext.{w'} (H^k K) W i)`.

## Isotypic parts

Section `Isotypic` takes a commutative ring `R`, a group `Γ`, and
representations `τ`, `ρ`, `σ` of `Γ` over `R` on `R`-modules `U`, `V`, `W`.

| Declaration | Statement |
| --- | --- |
| `isotypicPart τ ρ` | The submodule `⨆ f : τ.IntertwiningMap ρ, range f` of `V`: the sum of the images of all intertwining maps `τ → ρ`. A `def`. |
| `range_le_isotypicPart τ ρ f` | The range of an intertwining map `f : τ → ρ` lies in `isotypicPart τ ρ`. |
| `apply_mem_isotypicPart f u` | `f u ∈ isotypicPart τ ρ` for every intertwining map `f : τ → ρ` and `u : U`. |
| `isotypicPart_le_iff τ ρ` | `isotypicPart τ ρ ≤ N ↔ ∀ f u, f u ∈ N` for a submodule `N` of `V`. |
| `intertwiningMap_apply_mem_isotypicPart τ φ hv` | An intertwining map `φ : ρ → σ` sends `isotypicPart τ ρ` into `isotypicPart τ σ`. |
| `map_isotypicPart_le τ φ` | The same as `(isotypicPart τ ρ).map φ ≤ isotypicPart τ σ`. |
| `apply_mem_isotypicPart_of_mem τ γ hv` | `isotypicPart τ ρ` is stable under every `ρ γ`. |
| `isotypicSubrepresentation τ ρ` | `isotypicPart τ ρ` as a Mathlib `Subrepresentation ρ`. A `def`. |
| `isotypicRepresentation τ ρ` | The representation of `Γ` on `isotypicPart τ ρ` restricted from `ρ`. A `def`; `coe_isotypicRepresentation_apply` (a `simp` lemma) says that `γ` acts through `ρ γ`. |
| `isotypicIntertwiningMap τ φ` | The restriction of an intertwining map `φ : ρ → σ` to an intertwining map `isotypicRepresentation τ ρ → isotypicRepresentation τ σ`. A `def`, equal to `φ` on underlying elements (`coe_isotypicIntertwiningMap_apply`). |
| `isotypicEquiv τ e` | The restriction of an equivalence of representations `e : ρ ≃ σ` to an equivalence `isotypicRepresentation τ ρ ≃ isotypicRepresentation τ σ`. A `def`, equal to `e` on underlying elements (`coe_isotypicEquiv_apply`). |
| `map_isotypicPart_eq τ e` | `(isotypicPart τ ρ).map e = isotypicPart τ σ` for an equivalence `e : ρ ≃ σ`. |
| `intertwiningMapEquiv τ e` | The `R`-linear equivalence `τ.IntertwiningMap ρ ≃ₗ[R] τ.IntertwiningMap σ`, `f ↦ e ∘ f`, for an equivalence `e : ρ ≃ σ`. A `def`; `intertwiningMapEquiv_apply_apply` gives its values. |
| `invariantsLinearEquiv e` | The `R`-linear equivalence `ρ.invariants ≃ₗ[R] σ.invariants` given by an equivalence `e : ρ ≃ σ` (Mathlib's `Representation.invariants`). A `def`, equal to `e` on underlying elements (`coe_invariantsLinearEquiv_apply`). |
| `invariantsIntertwiningMap ρ hv` | For `v ∈ ρ.invariants`, the intertwining map from the trivial representation of `Γ` on `R` to `ρ`, `r ↦ r • v`. A `def`. |
| `isotypicPart_trivial ρ` | `isotypicPart (Representation.trivial R Γ R) ρ = ρ.invariants`. |

Proofs.

- `isotypicPart_le_iff`: `iSup_le`, and every element of the range of `f` is
  some `f u`.
- `intertwiningMap_apply_mem_isotypicPart`: apply `isotypicPart_le_iff` to the
  preimage of `isotypicPart τ σ` under `φ`; for an intertwining map
  `f : τ → ρ`, the composite `φ ∘ f` is an intertwining map `τ → σ`.
- `apply_mem_isotypicPart_of_mem`: apply `isotypicPart_le_iff` to the
  preimage of `isotypicPart τ ρ` under `ρ γ`; `ρ γ (f u) = f (τ γ u)` because
  `f` is intertwining.
- `isotypicEquiv`, `intertwiningMapEquiv`, `invariantsLinearEquiv`: the maps
  are given by `e` and `e.symm`; they preserve the subspaces by the previous
  lemmas, or, for invariants, because `σ γ (e x) = e (ρ γ x) = e x`.
- `map_isotypicPart_eq`: `≤` is `map_isotypicPart_le`; for `y` in
  `isotypicPart τ σ`, `e.symm y` lies in `isotypicPart τ ρ` and maps to `y`.
- `isotypicPart_trivial`: if `f` is an intertwining map from the trivial
  representation, then `ρ γ (f r) = f r`, so `f r` is invariant. Conversely
  an invariant `v` is the value at `1` of `invariantsIntertwiningMap ρ hv`.

## Two commuting actions

Section `Product` takes groups `Γ` and `Δ`. A representation `ρ` of `Γ × Δ`
restricts to representations `ρ.comp (MonoidHom.inl Γ Δ)` of `Γ` and
`ρ.comp (MonoidHom.inr Γ Δ)` of `Δ`, whose actions commute.

| Declaration | Statement |
| --- | --- |
| `equivComp e φ` | For a group homomorphism `φ : Γ' →* Γ`, an equivalence `e : ρ ≃ σ` of representations of `Γ` as an equivalence of `ρ.comp φ` and `σ.comp φ`. A `def`. |
| `inrIntertwiningMap ρ δ` | For a representation `ρ` of `Γ × Δ` and `δ : Δ`, the map `ρ (1, δ)` as an intertwining map from the restriction of `ρ` to `Γ` to itself. A `def`. |
| `isotypicProdSubrepresentation τ ρ` | For a representation `τ` of `Γ` and a representation `ρ` of `Γ × Δ`, the `τ`-isotypic part of the restriction of `ρ` to `Γ`, as a subrepresentation of the restriction of `ρ` to `Δ`. A `def`. |
| `isotypicProdRepresentation τ ρ` | The representation of `Δ` on this `τ`-isotypic part. A `def`; `δ` acts through `ρ (1, δ)` (`coe_isotypicProdRepresentation_apply`, a `simp` lemma). |
| `isotypicProdEquiv τ e` | For an equivalence `e : ρ ≃ σ` of representations of `Γ × Δ`, the equivalence `isotypicProdRepresentation τ ρ ≃ isotypicProdRepresentation τ σ` of representations of `Δ`. A `def`, equal to `e` on underlying elements (`coe_isotypicProdEquiv_apply`). |

Proofs.

- `inrIntertwiningMap`: `(1, δ) * (γ, 1) = (γ, 1) * (1, δ)` in `Γ × Δ`.
- `isotypicProdSubrepresentation`: the part is stable under `ρ (1, δ)` by
  `intertwiningMap_apply_mem_isotypicPart` applied to `inrIntertwiningMap ρ δ`.
- `isotypicProdEquiv`: the underlying linear equivalence is that of
  `isotypicEquiv τ (equivComp e (MonoidHom.inl Γ Δ))`; it commutes with the
  action of `δ` because `e` commutes with `ρ (1, δ)` and `σ (1, δ)`.

## Representations on groups of morphisms and the edge map

Section `HomRepresentation` takes a commutative ring `R`, a preadditive
`R`-linear category `C` with objects in `Type u` and morphisms in `Type v`,
and a group `Γ : Type uΓ`. Section `Derived` takes an `R`-linear abelian
category `C` with an instance `HasDerivedCategory.{w} C`; the `R`-linear
structure of `DerivedCategory C` is Mathlib's.

| Declaration | Statement |
| --- | --- |
| `homRepresentation R ρ σ` | For `ρ : Γ →* Aut X` and `σ : Γ →* Aut Y`, the representation of `Γ` on `X ⟶ Y` whose underlying additive action is `homAction ρ σ`. A `def`. |
| `homRepresentation_apply` | `homRepresentation R ρ σ γ f = (ρ γ).inv ≫ f ≫ (σ γ).hom` (by definition). |
| `abutmentRepresentation R ρ σ n` | The representation of `Γ` on `ShiftedHom K W₀ n = Hom(K, W₀⟦n⟧)`: `homRepresentation` for `ρ` and for the action on `W₀⟦n⟧` obtained from `σ` through `singleFunctor C 0 ⋙ shiftFunctor _ n`. A `def`. |
| `cohomologyHomRepresentation R ρ σ n` | The representation of `Γ` on `H^{-n} K ⟶ W`: `homRepresentation` for the action on `H^{-n} K` obtained from `ρ` and for `σ`. A `def`. |
| `abutmentRepresentation_apply`, `cohomologyHomRepresentation_apply` | These representations act by `abutmentAction ρ σ n` and `cohomologyHomAction ρ σ n` of `HyperextDegenerationEquivariance` (by definition). |
| `edgeMapIntertwiningMap R ρ σ n` | The edge map as an intertwining map `abutmentRepresentation R ρ σ n → cohomologyHomRepresentation R ρ σ n`. A `def`, equal to `HyperextDegeneration.edgeMap K W n` (`edgeMapIntertwiningMap_apply`). |

Proofs.

- `homRepresentation`: each map `f ↦ (ρ γ).inv ≫ f ≫ (σ γ).hom` is
  `R`-linear by `Linear.smul_comp` and `Linear.comp_smul`; `map_one` and
  `map_mul` are those of `homAction ρ σ`, applied to each `f`.
- `abutmentRepresentation_apply` and `cohomologyHomRepresentation_apply` hold
  by definition: `abutmentAction` and `cohomologyHomAction` are `homAction` for
  the same automorphisms.
- `edgeMapIntertwiningMap`: the linear map is `edgeMapLinearMap R K W n`
  (`HyperextEdgeMapLinear`); it is intertwining by `edgeMap_abutmentAction`.

## The degeneration isomorphism

Still in section `Derived`, with an additional instance `HasExt.{w'} C`, and
`hK`, `hW` as in the introduction. In the corollaries `τ` is a representation
of `Γ` over `R` on an `R`-module `U`.

| Declaration | Statement |
| --- | --- |
| `degenerationEquiv R b hK hW n ρ σ` | The equivalence of representations `abutmentRepresentation R ρ σ n ≃ cohomologyHomRepresentation R ρ σ n` given by the edge map. A `def`; `degenerationEquiv_apply` (a `simp` lemma) says it is the edge map. |
| `edgeMap_degenerationEquiv_symm_apply` | `edgeMap K W n ((degenerationEquiv R b hK hW n ρ σ).symm g) = g`. |
| `degenerationIsotypicEquiv R b hK hW n ρ σ τ` | The equivalence `isotypicRepresentation τ (abutmentRepresentation R ρ σ n) ≃ isotypicRepresentation τ (cohomologyHomRepresentation R ρ σ n)`: the `τ`-isotypic part of `Hom(K, W₀⟦n⟧)` corresponds to the `τ`-isotypic part of `Hom(H^{-n} K, W)`. A `def`, the edge map on underlying morphisms (`coe_degenerationIsotypicEquiv_apply`). |
| `degenerationMultiplicityEquiv R b hK hW n ρ σ τ` | The `R`-linear equivalence `τ.IntertwiningMap (abutmentRepresentation R ρ σ n) ≃ₗ[R] τ.IntertwiningMap (cohomologyHomRepresentation R ρ σ n)`, composition with the edge map (`degenerationMultiplicityEquiv_apply_apply`). A `def`. |
| `degenerationInvariantsLinearEquiv R b hK hW n ρ σ` | The `R`-linear equivalence between the `Γ`-invariants of the two representations, the edge map on underlying morphisms (`coe_degenerationInvariantsLinearEquiv_apply`). A `def`. |
| `degenerationIsotypicProdEquiv R b hK hW n ρ σ τ` | For `ρ : Γ × Δ →* Aut K` and `σ : Γ × Δ →* Aut W`, the equivalence of the representations of `Δ` on the `τ`-isotypic parts for `Γ` given by `isotypicProdRepresentation`. A `def`, the edge map on underlying morphisms (`coe_degenerationIsotypicProdEquiv_apply`). |

Section `Smooth` takes a commutative ring `R : Type u`, a topological group
`G : Type u`, instances `HasDerivedCategory.{w}` and `HasExt.{w'}` for
`SmoothRep.{u, u, u} R G` with its Library `R`-linear structure, and a group
`Γ`. Here `hW` is the smooth-Ext hypothesis: `(SmoothExt.ext R G (H^k K) i).obj W`
is trivial for every `k : ℤ` and every `i : ℕ` with `0 < i`.

| Declaration | Statement |
| --- | --- |
| `smoothDegenerationEquiv R G b hK hW n ρ σ` | `degenerationEquiv` for smooth representations, with the smooth-Ext hypothesis. A `def`, the edge map (`smoothDegenerationEquiv_apply`). |
| `smoothDegenerationIsotypicEquiv`, `smoothDegenerationMultiplicityEquiv`, `smoothDegenerationInvariantsLinearEquiv`, `smoothDegenerationIsotypicProdEquiv` | The four corollaries above for smooth representations, with the smooth-Ext hypothesis. `def`s. |

Proofs.

- `degenerationEquiv`: Mathlib's `Representation.Equiv.mk` applied to the
  `R`-linear equivalence
  `degenerationLinearEquiv R (hyperextDegenerationStatement_proof C) K b hK W hW n`
  of `HyperextEdgeMapLinear`, which is intertwining by `edgeMap_abutmentAction`.
- `edgeMap_degenerationEquiv_symm_apply` is `apply_symm_apply`.
- The corollaries are `isotypicEquiv`, `intertwiningMapEquiv`,
  `invariantsLinearEquiv` and `isotypicProdEquiv` applied to
  `degenerationEquiv`.
- The smooth variants convert `hW` with `subsingleton_ext_of_smoothExt`
  (`HyperextDegenerationIso`) and apply the general declarations.

## Provenance and interpretation

The definitions, statements and proofs are ours, assembled from Mathlib and
the Library. Inducing representations on groups of morphisms, restricting an
equivalence of representations to isotypic parts, multiplicity spaces and
invariants, and letting a commuting group act on isotypic parts are standard.
The formula for `isotypicPart` is the one of the Library's
`Langlands.CompactSplitting.isotypicPart`
(`Langlands/Representation/CompactCoefficient/AdmissibleComplement.lean`),
which is stated for complex representations only; the version here allows an
arbitrary commutative ring `R`, as needed for `ℤ_ℓ`- or `𝔽_ℓ`-coefficients.
When `τ` is irreducible, every nonzero intertwining map `τ → ρ` is injective,
so `isotypicPart τ ρ` is the sum of all subrepresentations of `ρ` isomorphic to
`τ`, the usual isotypic component. This comparison is explanation only; the
module does not prove it.

Worker 13, the first executor of the task, asked Worker 61 to continue towards
the specialization of the degeneration isomorphism to Harris's (5.2). The
module `HyperextDegenerationEquivariance` listed isotypic components and
linearity over the coefficient ring as missing for that specialization; this
module supplies the parts of that input that are pure algebra.

For this module Worker 61 read the following passage of Harris 1999:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`), §5,
  printed p.312 (one-based PDF page 14), read in the rendered scan and the
  text layer. Harris uses Proposition 4.10 "to express the representation of
  the decomposition group `Z_v` on the `JL(π_f)`-isotypic component of
  `H^{n-1}(S̄_K(N), W̃)`", and writes, before (5.2): "since `π_v` is
  supercuspidal, the higher Ext's vanish and the spectral sequence (4.10.1)
  degenerates to an isomorphism". The isomorphism (5.2) is
  `Hom_GJ(H_c^{2(n-1)-j}(M̆_N, 𝒪(n - 1)), 𝒜_ℓ(GJ, ρ, H)[π^v])[JL(π_v)] ≅ H^j(S̄_K(N), W̃)[π]`.

Interpretation (explanation only). Harris's argument passes from the
degenerate spectral sequence to isotypic components, and studies the action
of the decomposition group `Z_v` on an isotypic component for another
action. `degenerationIsotypicEquiv` is the general form of the first step for
one group `Γ` acting by automorphisms on `K` and `W`. `isotypicProdRepresentation`
and `degenerationIsotypicProdEquiv` model the second: if `Γ × Δ` acts, then
`Δ` acts on each `Γ`-isotypic part, and the degeneration isomorphism respects
these actions of `Δ`.

The specialization to (5.2) needs inputs that are not formalized here.

- The groups and actions themselves. Harris's components `[π^v]`, `[JL(π_v)]`
  and `[π]` are formed for actions of adelic or local groups or of Hecke
  algebras. At a finite level `K(N)` the cohomology `H^j(S̄_K(N), W̃)` carries
  a Hecke-algebra action rather than an action of the adelic group, and an
  action of an algebra by non-invertible endomorphisms is not a group action;
  this module treats group actions only.
- The complex `K` of smooth `GJ`-modules with `H^{-q} K` the compactly
  supported cohomology of the Drinfeld tower, the actions on `K` by
  automorphisms in the derived category, and the identification of the
  abutment with the cohomology of the Shimura variety (Proposition 4.10). As
  listed in `HyperextDegenerationEquivariance`, these are geometric inputs.
- The Ext vanishing. Harris's (5.2) concerns the coefficient module
  `𝒜_ℓ(GJ, ρ, H)[π^v]`, already restricted to a component, and selected
  components on both sides. As explained in `HyperextDegenerationIso`, this
  module claims no Ext vanishing for the whole module `𝒜_ℓ(GJ, ρ, H)`; the
  hypothesis `hW` concerns the chosen `W` only.

## Scope

- Only groups acting by automorphisms are treated. Actions of monoids or of
  Hecke algebras, continuity or smoothness of the actions, and changes of
  level are not formalized.
- `isotypicPart τ ρ` is defined for any representation `τ`. No irreducibility,
  semisimplicity or decomposition of a representation into isotypic parts is
  stated or proved, and the comparison with sums of subrepresentations
  isomorphic to `τ` is not proved.
- The Ext hypothesis `hW` and the bound `hK` are hypotheses of every
  degeneration equivalence.
- `HasDerivedCategory` and `HasExt` are hypotheses; the results hold for each
  such instance. In the smooth section `R` and `G` share the universe `u`, as
  in `SmoothRep.{u, u, u} R G`.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
p.312 (rendered scan and text layer) read for this module.

Dependencies: `Langlands.Cohomology.HyperextDegenerationEquivariance`,
`Langlands.Cohomology.HyperextEdgeMapLinear`,
`Langlands.Cohomology.HyperextDegeneration.Proof` and Mathlib's
`RepresentationTheory.Intertwining`, `RepresentationTheory.Invariants` and
`RepresentationTheory.Subrepresentation`, with Mathlib pinned to Lean 4.34.0
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
