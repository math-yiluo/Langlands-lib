# Isotypic degeneration isomorphisms and extension of scalars

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextScalarEdgeMap`
(`mapDerivedCategory_homology_isZero`,
`edgeMapLinearMap_comp_abutmentBaseChangeMap`,
`edgeMap_abutmentBaseChangeMap`; Worker 61) and
`Langlands.Cohomology.HyperextIsotypicBaseChange` (`baseChangeIntertwiningMap`,
`multiplicityBaseChangeMap`, `invariantsBaseChangeMap`, `isotypicBaseChangeMap`,
`isotypicBaseChangeIntertwiningMap`, `abutmentBaseChangeIntertwiningMap`,
`cohomologyHomBaseChangeIntertwiningMap`, `abutmentIsotypicBaseChangeMap`,
`cohomologyHomIsotypicBaseChangeMap` and their smooth specializations;
Worker 61). Through these imports it also uses
`Langlands.Cohomology.HyperextScalarExtension` (`IsSemilinear`, `abutmentMap`,
`cohomologyHomMap`, `abutmentBaseChangeMap`, `cohomologyHomBaseChangeMap`,
`smoothRepExtendScalars_isSemilinear`; Worker 61),
`Langlands.Cohomology.HyperextDegenerationIsotypic` (`isotypicPart`,
`isotypicRepresentation`, `isotypicIntertwiningMap`,
`isotypicProdRepresentation`, `abutmentRepresentation`,
`cohomologyHomRepresentation`, `edgeMapIntertwiningMap`,
`degenerationIsotypicEquiv`, `degenerationMultiplicityEquiv`,
`degenerationInvariantsLinearEquiv`, `degenerationIsotypicProdEquiv`; Worker 61), `baseChangeRepresentation` of
`Langlands.Cohomology.DivisibleSystem.ScalarExtension` (Worker 61) and the edge
map `HyperextDegeneration.edgeMap` of
`Langlands.Cohomology.HyperextDegeneration.Statement` (Worker 3).

Let `R → S` be an algebra of commutative rings and `Γ` a group. For an object
`K` of the derived category of an `R`-linear abelian category `C`, an object `W`
of `C` with `W₀` the complex `W` placed in degree `0`, and actions
`ρ : Γ →* Aut K`, `σ : Γ →* Aut W`, the module `HyperextDegenerationIsotypic`
makes `Hom(K, W₀⟦n⟧)` and `Hom(H^{-n} K, W)` into representations of `Γ`
(`abutmentRepresentation R ρ σ n` and `cohomologyHomRepresentation R ρ σ n`),
makes the edge map an intertwining map between them, and, under degeneration
hypotheses, restricts the degeneration isomorphism to `τ`-isotypic parts, to
multiplicity spaces `Hom_Γ(τ, -)` and, for actions of `Γ × Δ`, to the
`τ`-isotypic parts for `Γ` as representations of `Δ`. For an exact functor
`F : C ⥤ D` that is semilinear along `R → S`, the module
`HyperextIsotypicBaseChange` defines base-change maps from `S ⊗[R]` the
`τ`-isotypic parts over `R` to the `S ⊗[R] τ`-isotypic parts of the
corresponding representations over `S` attached to `F K` and `F W`.

This module proves that these base-change maps, and the corresponding maps on
multiplicity spaces, on `Γ`-invariants and for actions of `Γ × Δ`, commute with
the edge maps and therefore with the degeneration isomorphisms over `R` and
over `S`. It derives that, under the degeneration hypotheses, the base-change
map on abutments is bijective if and only if the base-change map on
`Hom(H^{-n} K, W)` is, and packages the base-change maps on abutments as
equivalences of representations (on invariants, as linear equivalences) under
the hypothesis that the map on `Hom(H^{-n} K, W)` is bijective. No base-change
map is proved bijective, and no such hypothesis is discharged here (see Scope).

All declarations are in namespace `Langlands.Cohomology.HyperextScalarExtension`
and use the Library's `HyperextAbutment` namespace (`open HyperextAbutment`).
For a representation `ρ` of `Γ` over `R` on `V`, `S ⊗[R] ρ` below denotes the
Library's `baseChangeRepresentation S ρ`, the representation on `S ⊗[R] V` in
which `γ` acts by `(ρ γ).baseChange S`; `Hom_Γ(τ, ρ)` denotes Mathlib's
`τ.IntertwiningMap ρ`, and `ρ^Γ` Mathlib's `ρ.invariants`.

## Auxiliary constructions for representations

Section `Algebra` takes `R : Type uR` and `S : Type uS` commutative rings with
`[Algebra R S]` (`S` explicit), a group `Γ : Type uΓ`, `R`-modules `U`, `V`,
`W`, and representations `τ : Representation R Γ U`,
`ρ : Representation R Γ V`, `σ : Representation R Γ W`; from
`isotypicProdIntertwiningMap` on also a group `Δ : Type uΔ`, and then `ρ`, `σ`
are representations of `Γ × Δ`. Write `inl = MonoidHom.inl Γ Δ : Γ →* Γ × Δ`.

| Declaration | Statement |
| --- | --- |
| `intertwiningMapCompLinearMap τ φ` | For `φ : Hom_Γ(ρ, σ)`, composition with `φ` as an `R`-linear map `Hom_Γ(τ, ρ) →ₗ[R] Hom_Γ(τ, σ)`. A `def`. |
| `intertwiningMapCompLinearMap_apply_apply τ φ f u` | `intertwiningMapCompLinearMap τ φ f u = φ (f u)` (a `simp` lemma, by definition). |
| `intertwiningMapComp f φ` | For `f : Hom_Γ(ρ, σ)` and a group homomorphism `φ : Γ' →* Γ`, the intertwining map `ρ.comp φ → σ.comp φ` with the same underlying linear map. A `def`. |
| `invariantsLinearMap φ` | For `φ : Hom_Γ(ρ, σ)`, the restriction of `φ` to invariants, an `R`-linear map `ρ^Γ →ₗ[R] σ^Γ`. A `def`. |
| `coe_invariantsLinearMap_apply φ x` | The image of `x`, as an element of `W`, is `φ x` (a `simp` lemma, by definition). |
| `isotypicProdIntertwiningMap τ φ` | For representations `ρ`, `σ` of `Γ × Δ` and `φ : Hom_{Γ×Δ}(ρ, σ)`, the restriction of `φ` to `τ`-isotypic parts for `Γ`, as an intertwining map `isotypicProdRepresentation τ ρ → isotypicProdRepresentation τ σ` of representations of `Δ`. A `def`. |
| `coe_isotypicProdIntertwiningMap_apply τ φ x` | The image of `x`, as an element of `W`, is `φ x` (a `simp` lemma, by definition). |
| `isotypicProdBaseChangeIntertwiningMap S τ ρ` | For a representation `ρ` of `Γ × Δ`, the intertwining map of representations of `Δ` from `S ⊗[R] isotypicProdRepresentation τ ρ` to `isotypicProdRepresentation (S ⊗[R] τ) (S ⊗[R] ρ)` with underlying linear map `isotypicBaseChangeMap S τ (ρ.comp inl)`. A `def`. |
| `coe_isotypicProdBaseChangeIntertwiningMap_tmul S τ ρ s v` | The image of `s ⊗ₜ v`, as an element of `S ⊗[R] V`, is `s ⊗ₜ (v : V)` (a `simp` lemma, by definition). |

Proofs.

- `intertwiningMapCompLinearMap`: additivity and `R`-linearity are checked
  pointwise from those of `φ`.
- `intertwiningMapComp`: the intertwining identity at `g : Γ'` is that of `f`
  at `φ g`.
- `invariantsLinearMap`: the restriction (`LinearMap.restrict`) of `φ`; if `v`
  is invariant then `σ γ (φ v) = φ (ρ γ v) = φ v` for every `γ`.
- `isotypicProdIntertwiningMap`: the underlying map is
  `isotypicIntertwiningMap τ (intertwiningMapComp φ inl)`; it commutes with the
  action of `δ : Δ` because `φ` intertwines the actions of `(1, δ)`.
- `isotypicProdBaseChangeIntertwiningMap`: compatibility with the action of `Δ`
  holds on pure tensors by definition, and both sides are additive
  (`TensorProduct.inductionOn`).

## Edge maps and base-change maps

Section `Derived` takes `R : Type uR`, `S : Type uS` with `[Algebra R S]`, an
`R`-linear abelian category `C : Type uC` (`[Category.{vC} C] [Abelian C] [Linear R C]`,
`[HasDerivedCategory.{s} C]`), an `S`-linear abelian category `D : Type uD`
(`[Category.{vD} D] [Abelian D] [Linear S D]`, `[HasDerivedCategory.{s'} D]`),
a functor `F : C ⥤ D` with `[F.Additive]`, `[PreservesFiniteLimits F]` and
`[PreservesFiniteColimits F]` (so `F` is exact), `hF : IsSemilinear R S F`, a
group `Γ : Type uΓ` and an `R`-module `U`. Below `K` is an object of
`DerivedCategory C`, `W` an object of `C`, `n : ℤ`, `ρ : Γ →* Aut K`,
`σ : Γ →* Aut W` and `τ : Representation R Γ U`. Write `F K` for
`F.mapDerivedCategory.obj K`, and `ρ_F = (F.mapDerivedCategory.mapAut K).comp ρ`,
`σ_F = (F.mapAut W).comp σ` for the induced actions on `F K` and `F W`. Write
`e_R = edgeMapIntertwiningMap R ρ σ n` and
`e_S = edgeMapIntertwiningMap S ρ_F σ_F n` for the edge maps over `R` and over
`S`, and `τ_S = S ⊗[R] τ`.

| Declaration | Statement |
| --- | --- |
| `edgeMapIntertwiningMap_comp_abutmentBaseChangeIntertwiningMap F hF ρ σ n` | `e_S.comp (abutmentBaseChangeIntertwiningMap F hF ρ σ n) = (cohomologyHomBaseChangeIntertwiningMap F hF ρ σ n).comp (baseChangeIntertwiningMap S e_R)`. |
| `abutmentIsotypicBaseChangeIntertwiningMap F hF ρ σ n τ` | The intertwining map from `S ⊗[R] isotypicRepresentation τ (abutmentRepresentation R ρ σ n)` to `isotypicRepresentation τ_S (abutmentRepresentation S ρ_F σ_F n)`: `isotypicBaseChangeIntertwiningMap` followed by the restriction of `abutmentBaseChangeIntertwiningMap` to isotypic parts. A `def`. |
| `abutmentIsotypicBaseChangeIntertwiningMap_apply F hF ρ σ n τ x` | Its value at `x` is `abutmentIsotypicBaseChangeMap F hF ρ σ n τ x` (a `simp` lemma, by definition). |
| `cohomologyHomIsotypicBaseChangeIntertwiningMap F hF ρ σ n τ` | The analogous intertwining map for `cohomologyHomRepresentation`, built from `cohomologyHomBaseChangeIntertwiningMap`. A `def`. |
| `cohomologyHomIsotypicBaseChangeIntertwiningMap_apply F hF ρ σ n τ x` | Its value at `x` is `cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ x` (a `simp` lemma, by definition). |
| `isotypicEdgeMap_abutmentIsotypicBaseChangeMap F hF ρ σ n τ x` | For `x : S ⊗[R] isotypicPart τ (abutmentRepresentation R ρ σ n)`: `isotypicIntertwiningMap τ_S e_S (abutmentIsotypicBaseChangeMap F hF ρ σ n τ x) = cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ ((isotypicIntertwiningMap τ e_R).toLinearMap.baseChange S x)`. |
| `abutmentMultiplicityBaseChangeMap F hF ρ σ n τ` | The `S`-linear map `S ⊗[R] Hom_Γ(τ, abutmentRepresentation R ρ σ n) →ₗ[S] Hom_Γ(τ_S, abutmentRepresentation S ρ_F σ_F n)`: `multiplicityBaseChangeMap` followed by composition with `abutmentBaseChangeIntertwiningMap`. A `def`. |
| `abutmentMultiplicityBaseChangeMap_tmul_apply F hF ρ σ n τ s f u` | `abutmentMultiplicityBaseChangeMap F hF ρ σ n τ (s ⊗ₜ f) u = abutmentBaseChangeMap F hF K W n (s • f.toLinearMap.baseChange S u)` (a `simp` lemma, by definition). |
| `cohomologyHomMultiplicityBaseChangeMap F hF ρ σ n τ` | The analogous `S`-linear map `S ⊗[R] Hom_Γ(τ, cohomologyHomRepresentation R ρ σ n) →ₗ[S] Hom_Γ(τ_S, cohomologyHomRepresentation S ρ_F σ_F n)`. A `def`. |
| `cohomologyHomMultiplicityBaseChangeMap_tmul_apply F hF ρ σ n τ s g u` | `cohomologyHomMultiplicityBaseChangeMap F hF ρ σ n τ (s ⊗ₜ g) u = cohomologyHomBaseChangeMap F hF K W (-n) (s • g.toLinearMap.baseChange S u)` (a `simp` lemma, by definition). |
| `multiplicityEdgeMap_abutmentMultiplicityBaseChangeMap F hF ρ σ n τ x` | For `x : S ⊗[R] Hom_Γ(τ, abutmentRepresentation R ρ σ n)`: `intertwiningMapCompLinearMap τ_S e_S (abutmentMultiplicityBaseChangeMap F hF ρ σ n τ x) = cohomologyHomMultiplicityBaseChangeMap F hF ρ σ n τ ((intertwiningMapCompLinearMap τ e_R).baseChange S x)`. |
| `abutmentInvariantsBaseChangeMap F hF ρ σ n` | The `S`-linear map `S ⊗[R] (abutmentRepresentation R ρ σ n)^Γ →ₗ[S] (abutmentRepresentation S ρ_F σ_F n)^Γ`: `invariantsBaseChangeMap` followed by `invariantsLinearMap (abutmentBaseChangeIntertwiningMap F hF ρ σ n)`. A `def`. |
| `coe_abutmentInvariantsBaseChangeMap_tmul F hF ρ σ n s f` | The image of `s ⊗ₜ f`, as an element of `ShiftedHom (F K) (F W)₀ n`, is `s • abutmentMap F K W n f` (a `simp` lemma, by definition). |
| `cohomologyHomInvariantsBaseChangeMap F hF ρ σ n` | The analogous `S`-linear map `S ⊗[R] (cohomologyHomRepresentation R ρ σ n)^Γ →ₗ[S] (cohomologyHomRepresentation S ρ_F σ_F n)^Γ`. A `def`. |
| `coe_cohomologyHomInvariantsBaseChangeMap_tmul F hF ρ σ n s g` | The image of `s ⊗ₜ g`, as a morphism `H^{-n}(F K) ⟶ F W`, is `s • cohomologyHomMap F K W (-n) g` (a `simp` lemma, by definition). |
| `invariantsEdgeMap_abutmentInvariantsBaseChangeMap F hF ρ σ n x` | For `x : S ⊗[R] (abutmentRepresentation R ρ σ n)^Γ`: `invariantsLinearMap e_S (abutmentInvariantsBaseChangeMap F hF ρ σ n x) = cohomologyHomInvariantsBaseChangeMap F hF ρ σ n ((invariantsLinearMap e_R).baseChange S x)`. |

Now also a group `Δ : Type uΔ`; in the next table `ρ : Γ × Δ →* Aut K` and
`σ : Γ × Δ →* Aut W`, with `ρ_F`, `σ_F`, `e_R`, `e_S` defined as above.

| Declaration | Statement |
| --- | --- |
| `abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ` | The intertwining map of representations of `Δ` from `S ⊗[R] isotypicProdRepresentation τ (abutmentRepresentation R ρ σ n)` to `isotypicProdRepresentation τ_S (abutmentRepresentation S ρ_F σ_F n)`: `isotypicProdBaseChangeIntertwiningMap` followed by `isotypicProdIntertwiningMap τ_S (abutmentBaseChangeIntertwiningMap F hF ρ σ n)`. A `def`. |
| `coe_abutmentIsotypicProdBaseChangeIntertwiningMap_tmul F hF ρ σ n τ s f` | The image of `s ⊗ₜ f`, as an element of `ShiftedHom (F K) (F W)₀ n`, is `s • abutmentMap F K W n f` (a `simp` lemma, by definition). |
| `cohomologyHomIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ` | The analogous intertwining map for `cohomologyHomRepresentation`. A `def`. |
| `coe_cohomologyHomIsotypicProdBaseChangeIntertwiningMap_tmul F hF ρ σ n τ s g` | The image of `s ⊗ₜ g`, as a morphism `H^{-n}(F K) ⟶ F W`, is `s • cohomologyHomMap F K W (-n) g` (a `simp` lemma, by definition). |
| `isotypicProdEdgeMap_abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ x` | `isotypicProdIntertwiningMap τ_S e_S (abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ x) = cohomologyHomIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ ((isotypicProdIntertwiningMap τ e_R).toLinearMap.baseChange S x)`. |

Proofs.

- `edgeMapIntertwiningMap_comp_abutmentBaseChangeIntertwiningMap`: two
  intertwining maps with equal underlying linear maps are equal; the equality
  of the linear maps is the Library's
  `edgeMapLinearMap_comp_abutmentBaseChangeMap`.
- The `def`s are composites, and their `_apply` and `tmul` lemmas hold by
  definition (`abutmentIsotypicBaseChangeMap` and
  `cohomologyHomIsotypicBaseChangeMap` are defined in
  `HyperextIsotypicBaseChange` as the same composites of linear maps).
- `isotypicEdgeMap_abutmentIsotypicBaseChangeMap`,
  `invariantsEdgeMap_abutmentInvariantsBaseChangeMap` and
  `isotypicProdEdgeMap_abutmentIsotypicProdBaseChangeIntertwiningMap`: both
  sides are additive in `x` (`TensorProduct.inductionOn`); at a pure tensor
  `s ⊗ₜ f` the equality of underlying morphisms (`Subtype.ext`) is the
  Library's `edgeMap_abutmentBaseChangeMap` at `s ⊗ₜ f`.
- `multiplicityEdgeMap_abutmentMultiplicityBaseChangeMap`: both sides are
  additive in `x`; at `x = s ⊗ₜ f` the two intertwining maps are compared on
  `u : S ⊗[R] U`, again additively, and at `u = t ⊗ₜ v` the equality is
  `edgeMap_abutmentBaseChangeMap` at `(s • t) ⊗ₜ f v`.

## Degeneration isomorphisms

Now also `[HasExt.{t} C]` and `[HasExt.{t'} D]`. The degeneration hypotheses
are `b : ℤ`, `hK : ∀ i > b, IsZero (H^i K)`, `hW : ∀ k, ∀ i > 0,
Subsingleton (Ext^i(H^k K, W))` (`Abelian.Ext.{t}`) and `hW' : ∀ k, ∀ i > 0,
Subsingleton (Ext^i(H^k (F K), F W))` (`Abelian.Ext.{t'}`). The vanishing of
`H^i (F K)` for `i > b`, needed for the degeneration isomorphisms over `S`, is
`fun i hi => mapDerivedCategory_homology_isZero F K (hK i hi)`. Write
`Iso_R = degenerationIsotypicEquiv R b hK hW n ρ σ τ`,
`Iso_S = degenerationIsotypicEquiv S b _ hW' n ρ_F σ_F τ_S`, and similarly
`Mult_R`, `Mult_S` for `degenerationMultiplicityEquiv`, `Inv_R`, `Inv_S` for
`degenerationInvariantsLinearEquiv` (which has no `τ` argument) and `Prod_R`,
`Prod_S` for `degenerationIsotypicProdEquiv`. Each of these is the edge map on
underlying elements (Library lemmas `coe_degenerationIsotypicEquiv_apply`,
`degenerationMultiplicityEquiv_apply_apply`,
`coe_degenerationInvariantsLinearEquiv_apply`,
`coe_degenerationIsotypicProdEquiv_apply`).

| Declaration | Statement |
| --- | --- |
| `degenerationIsotypicEquiv_abutmentIsotypicBaseChangeMap F hF b hK hW hW' n ρ σ τ x` | `Iso_S (abutmentIsotypicBaseChangeMap F hF ρ σ n τ x) = cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ (Iso_R.toLinearMap.baseChange S x)`. |
| `abutmentIsotypicBaseChangeMap_eq_degeneration F hF b hK hW hW' n ρ σ τ` | `abutmentIsotypicBaseChangeMap F hF ρ σ n τ = Iso_S.toLinearEquiv.symm ∘ₗ cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ ∘ₗ Iso_R.toLinearEquiv.baseChange R S _ _`. |
| `abutmentIsotypicBaseChangeMap_bijective_iff F hF b hK hW hW' n ρ σ τ` | `abutmentIsotypicBaseChangeMap F hF ρ σ n τ` is bijective if and only if `cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ` is. |
| `abutmentIsotypicBaseChangeMap_injective_iff F hF b hK hW hW' n ρ σ τ` | The same with injective. |
| `abutmentIsotypicBaseChangeMap_surjective_iff F hF b hK hW hW' n ρ σ τ` | The same with surjective. |
| `abutmentIsotypicBaseChangeEquiv F hF b hK hW hW' n ρ σ τ h` | Given `h : Function.Bijective (cohomologyHomIsotypicBaseChangeMap F hF ρ σ n τ)`, an equivalence of representations of `Γ` (`Representation.Equiv`) from `S ⊗[R] isotypicRepresentation τ (abutmentRepresentation R ρ σ n)` to `isotypicRepresentation τ_S (abutmentRepresentation S ρ_F σ_F n)`. A `def`. |
| `abutmentIsotypicBaseChangeEquiv_apply F hF b hK hW hW' n ρ σ τ h x` | Its value at `x` is `abutmentIsotypicBaseChangeMap F hF ρ σ n τ x` (a `simp` lemma, by definition). |
| `degenerationMultiplicityEquiv_abutmentMultiplicityBaseChangeMap F hF b hK hW hW' n ρ σ τ x` | `Mult_S (abutmentMultiplicityBaseChangeMap F hF ρ σ n τ x) = cohomologyHomMultiplicityBaseChangeMap F hF ρ σ n τ (Mult_R.toLinearMap.baseChange S x)`. |
| `abutmentMultiplicityBaseChangeMap_eq_degeneration F hF b hK hW hW' n ρ σ τ` | `abutmentMultiplicityBaseChangeMap F hF ρ σ n τ = Mult_S.symm ∘ₗ cohomologyHomMultiplicityBaseChangeMap F hF ρ σ n τ ∘ₗ Mult_R.baseChange R S _ _`. |
| `abutmentMultiplicityBaseChangeMap_bijective_iff F hF b hK hW hW' n ρ σ τ` | `abutmentMultiplicityBaseChangeMap F hF ρ σ n τ` is bijective if and only if `cohomologyHomMultiplicityBaseChangeMap F hF ρ σ n τ` is. |
| `degenerationInvariantsLinearEquiv_abutmentInvariantsBaseChangeMap F hF b hK hW hW' n ρ σ x` | `Inv_S (abutmentInvariantsBaseChangeMap F hF ρ σ n x) = cohomologyHomInvariantsBaseChangeMap F hF ρ σ n (Inv_R.toLinearMap.baseChange S x)`. |
| `abutmentInvariantsBaseChangeMap_eq_degeneration F hF b hK hW hW' n ρ σ` | `abutmentInvariantsBaseChangeMap F hF ρ σ n = Inv_S.symm ∘ₗ cohomologyHomInvariantsBaseChangeMap F hF ρ σ n ∘ₗ Inv_R.baseChange R S _ _`. |
| `abutmentInvariantsBaseChangeMap_bijective_iff F hF b hK hW hW' n ρ σ` | `abutmentInvariantsBaseChangeMap F hF ρ σ n` is bijective if and only if `cohomologyHomInvariantsBaseChangeMap F hF ρ σ n` is. |
| `abutmentInvariantsBaseChangeEquiv F hF b hK hW hW' n ρ σ h` | Given `h : Function.Bijective (cohomologyHomInvariantsBaseChangeMap F hF ρ σ n)`, an `S`-linear equivalence `S ⊗[R] (abutmentRepresentation R ρ σ n)^Γ ≃ₗ[S] (abutmentRepresentation S ρ_F σ_F n)^Γ`. A `def`. |
| `abutmentInvariantsBaseChangeEquiv_apply F hF b hK hW hW' n ρ σ h x` | Its value at `x` is `abutmentInvariantsBaseChangeMap F hF ρ σ n x` (a `simp` lemma, by definition). |
| `degenerationIsotypicProdEquiv_abutmentIsotypicProdBaseChangeIntertwiningMap F hF b hK hW hW' n ρ σ τ x` | For actions of `Γ × Δ`: `Prod_S (abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ x) = cohomologyHomIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ (Prod_R.toLinearMap.baseChange S x)`. |
| `abutmentIsotypicProdBaseChangeIntertwiningMap_eq_degeneration F hF b hK hW hW' n ρ σ τ` | The underlying linear map of `abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ` is `Prod_S.toLinearEquiv.symm ∘ₗ (cohomologyHomIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ).toLinearMap ∘ₗ Prod_R.toLinearEquiv.baseChange R S _ _`. |
| `abutmentIsotypicProdBaseChangeIntertwiningMap_bijective_iff F hF b hK hW hW' n ρ σ τ` | `abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ` is bijective if and only if `cohomologyHomIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ` is. |
| `abutmentIsotypicProdBaseChangeEquiv F hF b hK hW hW' n ρ σ τ h` | Given `h : Function.Bijective (cohomologyHomIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ)`, an equivalence of representations of `Δ` from `S ⊗[R] isotypicProdRepresentation τ (abutmentRepresentation R ρ σ n)` to `isotypicProdRepresentation τ_S (abutmentRepresentation S ρ_F σ_F n)`. A `def`. |
| `abutmentIsotypicProdBaseChangeEquiv_apply F hF b hK hW hW' n ρ σ τ h x` | Its value at `x` is `abutmentIsotypicProdBaseChangeIntertwiningMap F hF ρ σ n τ x` (a `simp` lemma, by definition). |

Proofs.

- The four compatibility theorems: `Iso_S`, `Mult_S`, `Inv_S` and `Prod_S` are
  the edge map over `S` on underlying elements and `Iso_R`, `Mult_R`, `Inv_R`,
  `Prod_R` the edge map over `R`, by definition, so the statements are the
  edge-map compatibilities of the previous section.
- The `_eq_degeneration` lemmas: at each `x`, Mathlib's
  `LinearEquiv.eq_symm_apply` turns the equation into the corresponding
  compatibility theorem.
- The `_iff` lemmas: rewrite with the `_eq_degeneration` lemma; composing with
  linear equivalences on either side does not change bijectivity, injectivity
  or surjectivity (Mathlib's `EquivLike.comp_bijective`,
  `EquivLike.bijective_comp` and their injective and surjective analogues).
  For `Γ × Δ` the statement is first restated for the underlying linear maps.
- The equivalences are Mathlib's `Representation.IntertwiningMap.ofBijective`
  applied to `abutmentIsotypicBaseChangeIntertwiningMap` (resp.
  `abutmentIsotypicProdBaseChangeIntertwiningMap`) and the bijectivity given
  by the `_bijective_iff` lemma and `h`; `abutmentInvariantsBaseChangeEquiv`
  is Mathlib's `LinearEquiv.ofBijective` applied to
  `abutmentInvariantsBaseChangeMap` in the same way.

## Smooth representations

Section `Smooth` takes `R : Type uR` and `S : Type uS` with `[Algebra R S]` and
`[Module.Flat R S]`, a topological group `G : Type uG`, instances
`HasDerivedCategory.{s}` and `HasExt.{t}` on `SmoothRep.{uR, uG, w} R G`,
`HasDerivedCategory.{s'}` and `HasExt.{t'}` on
`SmoothRep.{uS, uG, max uS w} S G`, a group `Γ`, and `K`, `W`, `ρ`, `σ`, `n`,
`τ`, `b`, `hK`, `hW`, `hW'` as above with `C` the category
`SmoothRep.{uR, uG, w} R G` of smooth representations of `G` over `R` and `F`
the Library's extension of scalars `E = smoothRepExtendScalars.{w} R S G`,
which is exact for flat `S` (`HyperextScalarExtension`) and semilinear
(`smoothRepExtendScalars_isSemilinear`).

| Declaration | Statement |
| --- | --- |
| `smoothAbutmentIsotypicBaseChangeMap_bijective_iff R S G b hK hW hW' n ρ σ τ` | `smoothAbutmentIsotypicBaseChangeMap R S G ρ σ n τ` is bijective if and only if `smoothCohomologyHomIsotypicBaseChangeMap R S G ρ σ n τ` is. |
| `smoothAbutmentIsotypicBaseChangeEquiv R S G b hK hW hW' n ρ σ τ h` | Given `h : Function.Bijective (smoothCohomologyHomIsotypicBaseChangeMap R S G ρ σ n τ)`, `abutmentIsotypicBaseChangeEquiv` for `E`: an equivalence of representations of `Γ` from `S ⊗[R] isotypicRepresentation τ (abutmentRepresentation R ρ σ n)` to `isotypicRepresentation τ_S (abutmentRepresentation S ((E.mapDerivedCategory.mapAut K).comp ρ) ((E.mapAut W).comp σ) n)`. A `def`. |
| `smoothAbutmentInvariantsBaseChangeMap R S G ρ σ n` | `abutmentInvariantsBaseChangeMap` for `E`: the `S`-linear map `S ⊗[R] (abutmentRepresentation R ρ σ n)^Γ →ₗ[S] (abutmentRepresentation S ((E.mapDerivedCategory.mapAut K).comp ρ) ((E.mapAut W).comp σ) n)^Γ`. A `def` (it does not need the `HasExt` instances). |
| `smoothCohomologyHomInvariantsBaseChangeMap R S G ρ σ n` | `cohomologyHomInvariantsBaseChangeMap` for `E`. A `def` (it does not need the `HasExt` instances). |
| `smoothAbutmentInvariantsBaseChangeMap_bijective_iff R S G b hK hW hW' n ρ σ` | `smoothAbutmentInvariantsBaseChangeMap R S G ρ σ n` is bijective if and only if `smoothCohomologyHomInvariantsBaseChangeMap R S G ρ σ n` is. |
| `smoothAbutmentInvariantsBaseChangeEquiv R S G b hK hW hW' n ρ σ h` | Given `h : Function.Bijective (smoothCohomologyHomInvariantsBaseChangeMap R S G ρ σ n)`, `abutmentInvariantsBaseChangeEquiv` for `E`: an `S`-linear equivalence from `S ⊗[R] (abutmentRepresentation R ρ σ n)^Γ` to the `Γ`-invariants of `abutmentRepresentation S ((E.mapDerivedCategory.mapAut K).comp ρ) ((E.mapAut W).comp σ) n`. A `def`. |

Proofs. The two maps on invariants are the general maps for `F = E` and
`hF = smoothRepExtendScalars_isSemilinear R S G`; the other results are the
general results for this `F` and `hF`, since the smooth maps of
`HyperextIsotypicBaseChange` and of this module are by definition the general
maps for `E`.

## Provenance and interpretation

The statements, definitions and proofs are ours, assembled from Mathlib and the
Library. Worker 13, the first executor of the task, asked Worker 61 for the
change of coefficients from `𝒪` to `L_ℓ` and for the maps it induces on the
degeneration of Harris's spectral sequence and on its isotypic parts, with any
failure of extension of scalars to commute with isotypic parts kept as an
explicit obligation. `HyperextScalarEdgeMap` proves the compatibility of the
base-change maps with the edge map and the degeneration isomorphism without
group actions, and `HyperextIsotypicBaseChange` restricts the base-change maps
to isotypic parts. This module combines the two: the same compatibility on
isotypic parts, on multiplicity spaces, on invariants and for actions of
`Γ × Δ`.

The passages of Harris 1999 behind this module are those read, in the rendered
scans, for `Langlands.Cohomology.HyperextIsotypicBaseChange` and quoted in its
Markdown file:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`).
- §5, printed p.312 (one-based PDF page 14): "Using Proposition 4.10, we can
  now apply the arguments of [H1] and [H2, App.] to express the representation
  of the decomposition group `Z_v` on the `JL(π_f)`-isotypic component of
  `H^{n-1}(S̄_{K(N)}, W̃)`, which we denote `H^{n-1}(S̄_{K(N)}, W̃)[π]`." Later on
  the same page: "since `π_v` is supercuspidal, the higher
  Ext's vanish and the spectral sequence (4.10.1) degenerates to an isomorphism
  (5.2) `Hom_GJ(H_c^{2(n-1)-j}(M̆_N, 𝒪(n - 1)), 𝒜_ℓ(GJ, ρ, H)[π^v])[JL(π_v)] ≅ H^j(S̄_{K(N)}, W̃)[π]`".
- §3, printed p.307 (one-based PDF page 9), as quoted in the Markdown file of
  `Langlands.Cohomology.HyperextScalarExtension`: "Let `𝒪` denote the ring of
  integers of `L_ℓ` …".

Interpretation (explanation only). Both sides of (5.2) are isotypic parts of
the two sides of a degeneration isomorphism, while the cohomology
`H_c(M̆_N, 𝒪(n - 1))` is integral and `𝒜_ℓ(GJ, ρ, H)` and `W̃` have
`L_ℓ`-coefficients. With `R = 𝒪`, `S = L_ℓ` and extension of scalars as `F`,
the theorems of this module say that passing from an isotypic part over `𝒪` to
`L_ℓ ⊗_𝒪` of it and then to the isotypic part over `L_ℓ` is compatible with
the degeneration isomorphisms on both sides, and that, under the degeneration
hypotheses, it is an isomorphism on abutments exactly when it is one on
`Hom(H^{-n} K, W)`. The `Γ × Δ` version covers a second group acting on an
isotypic part cut out by the first, as the decomposition group `Z_v` acts on
the isotypic component `H^{n-1}(S̄_{K(N)}, W̃)[π]` in the quoted passage. The
groups `Γ` and `Δ`, the representation `τ`, `K` and `W` are arbitrary; the
formalization does not identify them with Harris's objects.

## Scope

- No base-change map is proved surjective or bijective. Extension of scalars
  need not commute with isotypic parts or with invariants, even along a flat
  map (see the example in the Markdown file of
  `Langlands.Cohomology.HyperextIsotypicBaseChange`). The equivalences
  `abutmentIsotypicBaseChangeEquiv`, `abutmentIsotypicProdBaseChangeEquiv`,
  `abutmentInvariantsBaseChangeEquiv`, `smoothAbutmentIsotypicBaseChangeEquiv`
  and `smoothAbutmentInvariantsBaseChangeEquiv` take the bijectivity of the map
  on `Hom(H^{-n} K, W)` as the hypothesis `h`; whether `h` holds in Harris's
  situation remains an open obligation.
- The compatibility theorems hold for any semilinear exact `F`; flatness of
  `S` over `R` is used only in the smooth section, where it makes
  `smoothRepExtendScalars` exact.
- The geometric inputs of Harris's Proposition 4.10 and (5.2), the groups and
  representations that cut out the isotypic parts, and their identification
  with `Γ`, `Δ`, `τ`, `K` and `W` are not formalized.
- `HasDerivedCategory` and `HasExt` are hypotheses; the results hold for each
  such instance.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
p.312 (rendered scan) as read for
`Langlands.Cohomology.HyperextIsotypicBaseChange`; printed p.307 as quoted in
`Langlands.Cohomology.HyperextScalarExtension`.

Dependencies: `Langlands.Cohomology.HyperextScalarEdgeMap` and
`Langlands.Cohomology.HyperextIsotypicBaseChange`, with Mathlib pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
