# Hom groups of representations and localization

Author: Worker 61. Built on the Library module
`Langlands.Cohomology.HyperextIsotypicBaseChange` (`invariantsBaseChangeMap`;
Worker 61). Through this import it also uses
`Langlands.Cohomology.HyperextScalarExtension` (`IsSemilinear`,
`baseChangeLift`, `cohomologyHomMap`, `cohomologyHomMap_apply`,
`cohomologyHomBaseChangeMap`, `cohomologyHomBaseChangeMap_tmul`,
`smoothCohomologyHomBaseChangeMap`, `repExtendScalars_isSemilinear`,
`smoothRepExtendScalars_isSemilinear`; Worker 61),
`Langlands.Cohomology.ExactDerivedHomology` (`exactDerivedHomologyIso`),
`Langlands.Cohomology.DivisibleSystem.ScalarExtension`
(`baseChangeRepresentation`, `baseChangeRepresentation_apply_tmul`,
`repExtendScalars`; Worker 61),
`Langlands.Cohomology.DivisibleSystem.SmoothScalarExtension`
(`smoothRepExtendScalars`; Worker 61) and
`Langlands.Representation.Category.Basic` (`SmoothRep`). From Mathlib it
imports `Mathlib.Algebra.Module.LocalizedModule.Int`,
`Mathlib.RingTheory.Flat.Localization` and
`Mathlib.RingTheory.Localization.BaseChange`.

Let `S` be the localization of a commutative ring `R` at a submonoid `M`. The
Library's `cohomologyHomBaseChangeMap` compares `S ⊗[R] Hom(H^q K, W)` with
`Hom(H^q (F K), F W)` for a semilinear exact functor `F`, and the Markdown file
of `HyperextScalarExtension` notes that it is in general not bijective. This
module proves that it is bijective for extension of scalars of representations
and of smooth representations along a localization when `H^q K` is finitely
generated over the monoid algebra `R[G]` and `W` has no `M`-torsion. On the way
it proves that invariants commute with localization for representations on
modules without `M`-torsion. The finite generation and the absence of torsion
remain explicit hypotheses.

All declarations are in namespace `Langlands.Cohomology.HyperextScalarExtension`.
For a representation `ρ` of a group `Γ` over `R` on `V`, `S ⊗[R] ρ` below
denotes the Library's `baseChangeRepresentation S ρ`, the representation on
`S ⊗[R] V` in which `γ` acts by `(ρ γ).baseChange S`, and `ρ^Γ` denotes
Mathlib's `ρ.invariants`. "`V` has no `M`-torsion" means
`∀ m : M, IsSMulRegular V (m : R)`: multiplication by every element of `M` is
injective on `V`. `1 ⊗ v` denotes `TensorProduct.mk R S V 1 v = 1 ⊗ₜ[R] v`.

## Localization of modules without torsion

Section `Algebra` takes commutative rings `R : Type uR`, `S : Type uS` with
`[Algebra R S]`, a submonoid `M : Submonoid R` with `[IsLocalization M S]`
(`S` and `M` explicit), a group `Γ : Type uΓ` and an `R`-module `V`.

| Declaration | Statement |
| --- | --- |
| `isLocalizedModule_mk_one S M V` | `IsLocalizedModule M (TensorProduct.mk R S V 1)`: `v ↦ 1 ⊗ v : V → S ⊗[R] V` is a localization of `V` at `M`. |
| `mk_one_injective_of_isSMulRegular S M hV` | If `hV : ∀ m : M, IsSMulRegular V (m : R)`, then `v ↦ 1 ⊗ v` is injective. |
| `invariantsBaseChangeMap_surjective_of_isSMulRegular S M hV` | For `ρ : Representation R Γ V` and `hV` as above: `invariantsBaseChangeMap S ρ : S ⊗[R] ρ^Γ → (S ⊗[R] ρ)^Γ` is surjective. |
| `invariantsBaseChangeMap_bijective_of_isSMulRegular S M hV` | Under the same hypotheses, `invariantsBaseChangeMap S ρ` is bijective. |
| `invariantsBaseChangeEquivOfIsSMulRegular S M hV` | Under the same hypotheses, the `S`-linear equivalence `S ⊗[R] ρ^Γ ≃ₗ[S] (S ⊗[R] ρ)^Γ` with underlying map `invariantsBaseChangeMap S ρ`. A `def`. |
| `invariantsBaseChangeEquivOfIsSMulRegular_apply S M hV x` | Its value at `x` is `invariantsBaseChangeMap S ρ x` (a `simp` lemma, by definition). |

Section `Generators` takes a commutative ring `R`, a monoid `G : Type uG` and
an `R`-module `V`.

| Declaration | Statement |
| --- | --- |
| `exists_finset_eq_top_of_finite_asModule ρ` | For `ρ : Representation R G V` with `[Module.Finite (MonoidAlgebra R G) ρ.asModule]`: there is `t : Finset V` such that every `R`-submodule `N` of `V` with `ρ g v ∈ N` for all `g : G` and `v ∈ N`, and with `t ⊆ N`, is `⊤`. |

Proofs.

- `isLocalizedModule_mk_one`: `S ⊗[R] V` with `v ↦ 1 ⊗ v` is a base change of
  `V` (Mathlib's `TensorProduct.isBaseChange`), and for a localization `S` base
  changes are localizations (Mathlib's `isLocalizedModule_iff_isBaseChange`).
- `mk_one_injective_of_isSMulRegular`: if `1 ⊗ v = 0`, then `c • v = 0` for
  some `c ∈ M` (Mathlib's `IsLocalizedModule.eq_zero_iff`), so `v = 0` because
  multiplication by `c` is injective.
- `invariantsBaseChangeMap_surjective_of_isSMulRegular`: an invariant
  `x : S ⊗[R] V` satisfies `m • x = 1 ⊗ v` for some `m ∈ M` and `v : V`
  (Mathlib's `IsLocalizedModule.surj`). For every `γ`,
  `1 ⊗ ρ γ v = (S ⊗[R] ρ) γ (m • x) = m • x = 1 ⊗ v`, so `ρ γ v = v` by the
  previous lemma: `v` is invariant. With `u = IsLocalization.mk' S 1 m` (so
  `u · m = 1` in `S`), `x = u ⊗ v`, which is the image of the element `u ⊗ v`
  of `S ⊗[R] ρ^Γ`.
- `invariantsBaseChangeMap_bijective_of_isSMulRegular`: `S` is flat over `R`
  (Mathlib's `IsLocalization.flat`), so injectivity is the Library's
  `invariantsBaseChangeMap_injective`; surjectivity is the previous theorem.
- `invariantsBaseChangeEquivOfIsSMulRegular`: Mathlib's
  `LinearEquiv.ofBijective` applied to the previous theorem.
- `exists_finset_eq_top_of_finite_asModule`: `ρ.asModule` has a finite
  generating set `t₀` over `R[G]` (Mathlib's `Module.Finite.fg_top`); `t` is
  its image under `ρ.asModuleEquiv : ρ.asModule ≃ₗ[R] V`. A `G`-stable
  `R`-submodule `N` pulls back to an `R[G]`-submodule of `ρ.asModule` (closure
  under `R[G]` is checked on `of g`, sums and scalar multiples, Mathlib's
  `MonoidAlgebra.induction_on` and `Representation.asAlgebraHom_of`), which
  contains `t₀` and hence is everything.

## The comparison map on Hom groups

Section `Hom` takes commutative rings `R`, `S` with `[Algebra R S]` (both
implicit), an `R`-linear abelian category `C : Type uC`
(`[Category.{vC} C] [Abelian C] [Linear R C]`), an `S`-linear abelian category
`D : Type uD` (`[Category.{vD} D] [Abelian D] [Linear S D]`) and a functor
`F : C ⥤ D` with `[F.Additive]` (explicit). Its section `Derived` also takes
`[PreservesFiniteLimits F]`, `[PreservesFiniteColimits F]`,
`[HasDerivedCategory.{s} C]` and `[HasDerivedCategory.{s'} D]`; there `K` is an
object of `DerivedCategory C`, `W` an object of `C`, `q : ℤ`, and
`H^q K = (DerivedCategory.homologyFunctor C q).obj K`.

| Declaration | Statement |
| --- | --- |
| `homBaseChangeMap F hF X Y` | For `hF : IsSemilinear R S F` and objects `X`, `Y` of `C`: the `S`-linear map `S ⊗[R] (X ⟶ Y) →ₗ[S] (F.obj X ⟶ F.obj Y)`, the Library's `baseChangeLift` of `F.mapAddHom`. A `def`. |
| `homBaseChangeMap_tmul F hF s f` | `homBaseChangeMap F hF X Y (s ⊗ₜ f) = s • F.map f` (a `simp` lemma, by definition). |
| `cohomologyHomBaseChangeMap_apply_eq F hF K W q t` | For `t : S ⊗[R] (H^q K ⟶ W)`: `cohomologyHomBaseChangeMap F hF K W q t = (exactDerivedHomologyIso F q).hom.app K ≫ homBaseChangeMap F hF (H^q K) W t`. |
| `cohomologyHomBaseChangeMap_bijective_iff F hF K W q` | `cohomologyHomBaseChangeMap F hF K W q` is bijective if and only if `homBaseChangeMap F hF (H^q K) W` is bijective. |

Proofs.

- `homBaseChangeMap_tmul`: the defining property of `baseChangeLift`.
- `cohomologyHomBaseChangeMap_apply_eq`: induction on `t`
  (`TensorProduct.inductionOn`). On `s ⊗ₜ φ` both sides are
  `s • ((exactDerivedHomologyIso F q).hom.app K ≫ F.map φ)` (the Library's
  `cohomologyHomBaseChangeMap_tmul` and `cohomologyHomMap_apply`, and Mathlib's
  `Linear.comp_smul`); both sides are additive in `t`.
- `cohomologyHomBaseChangeMap_bijective_iff`: by the previous theorem
  `cohomologyHomBaseChangeMap F hF K W q` is `homBaseChangeMap F hF (H^q K) W`
  followed by precomposition with the isomorphism
  `(exactDerivedHomologyIso F q).hom.app K`, which is bijective
  (Mathlib's `Function.Bijective.of_comp_iff'`).

## Representations

Section `Rep` takes `R`, `S`, `M` with `[IsLocalization M S]` as in section
`Algebra` (`S` and `M` explicit) and a monoid `G : Type uG`. Below `X`, `Y` are
objects of `Rep.{w} R G` (implicit), `E = repExtendScalars.{w} R S G` is the
Library's extension of scalars `Rep.{w} R G ⥤ Rep.{max uS w} S G`,
`hE = repExtendScalars_isSemilinear.{w} R S G`, and
`hY : ∀ m : M, IsSMulRegular Y (m : R)`. Its section `Derived` also takes
`[Module.Flat R S]`, `[HasDerivedCategory.{s} (Rep.{w} R G)]` and
`[HasDerivedCategory.{s'} (Rep.{max uS w} S G)]`; the flatness instance holds
for every localization (Mathlib's `IsLocalization.flat`) and is a separate
argument because the Library's `cohomologyHomBaseChangeMap` for `E` needs the
exactness instances of `E`, which the Library derives from it.

| Declaration | Statement |
| --- | --- |
| `repHomBaseChangeMap_injective S M hY` | `homBaseChangeMap E hE X Y : S ⊗[R] (X ⟶ Y) → (E.obj X ⟶ E.obj Y)` is injective. |
| `repHomBaseChangeMap_surjective S M hY` | If moreover `[Module.Finite (MonoidAlgebra R G) X.ρ.asModule]`: `homBaseChangeMap E hE X Y` is surjective. |
| `repHomBaseChangeMap_bijective S M hY` | Under the same hypotheses, `homBaseChangeMap E hE X Y` is bijective. |
| `repHomBaseChangeEquiv S M hY` | Under the same hypotheses, the `S`-linear equivalence `S ⊗[R] (X ⟶ Y) ≃ₗ[S] (E.obj X ⟶ E.obj Y)` with underlying map `homBaseChangeMap E hE X Y`. A `def`. |
| `repHomBaseChangeEquiv_apply S M hY t` | Its value at `t` is `homBaseChangeMap E hE X Y t` (a `simp` lemma, by definition). |
| `repCohomologyHomBaseChangeMap_bijective_of_isLocalization S M K q hW` | For `K : DerivedCategory (Rep.{w} R G)`, `W : Rep.{w} R G`, `q : ℤ` with `[Module.Finite (MonoidAlgebra R G) (H^q K).ρ.asModule]` and `hW : ∀ m : M, IsSMulRegular W (m : R)`: `cohomologyHomBaseChangeMap E hE K W q : S ⊗[R] (H^q K ⟶ W) → (H^q (E K) ⟶ E.obj W)` is bijective. |

Section `Torsion` takes a commutative ring `R` and a monoid `G`.

| Declaration | Statement |
| --- | --- |
| `repHom_isSMulRegular hY` | For `X Y : Rep.{w} R G`, `r : R` and `hY : IsSMulRegular Y r`: `IsSMulRegular (X ⟶ Y) r`. |
| `smoothRepHom_isSMulRegular hY` | For a topological group `G`, `X Y : SmoothRep.{uR, uG, w} R G`, `r : R` and `hY : IsSMulRegular Y r`: `IsSMulRegular (X ⟶ Y) r`. |

Proofs.

- `repHomBaseChangeMap_injective`: `S ⊗[R] (X ⟶ Y)` is the localization of
  `X ⟶ Y` at `M` (`isLocalizedModule_mk_one`), so for `t` in the kernel,
  `m • t = 1 ⊗ φ` for some `m ∈ M` and `φ : X ⟶ Y`. Applying the map gives
  `E.map φ = 0`, that is `1 ⊗ φ x = 0` for every `x : X`, so `φ x = 0` by
  `mk_one_injective_of_isSMulRegular` and `hY`. Hence `m • t = 0`, and `t = 0`
  because the image of `m` is a unit of `S`.
- `repHomBaseChangeMap_surjective`: let `g : E.obj X ⟶ E.obj Y` and let `t` be
  the finite set of `exists_finset_eq_top_of_finite_asModule X.ρ`. Since
  `S ⊗[R] Y` is the localization of `Y` at `M`, there is one `b ∈ M` such that
  `b • g (1 ⊗ x)` lies in the image of `y ↦ 1 ⊗ y` for every `x ∈ t`
  (Mathlib's `IsLocalizedModule.exist_integer_multiples`). The `R`-linear map
  `L : X → S ⊗[R] Y`, `x ↦ b • g (1 ⊗ x)`, is `G`-equivariant because `g` is,
  so the set of `x` with `L x` in this image is a `G`-stable `R`-submodule
  containing `t`, hence all of `X`. By injectivity of `y ↦ 1 ⊗ y`
  (`mk_one_injective_of_isSMulRegular`), `L = (y ↦ 1 ⊗ y) ∘ f` for a unique
  `R`-linear `f : X → Y`, which is `G`-equivariant by the same injectivity;
  let `φ : X ⟶ Y` be the corresponding morphism. With
  `u = IsLocalization.mk' S 1 b`, the morphism `u • E.map φ` agrees with `g` on
  every `s ⊗ x`, as `u • (s ⊗ φ x) = (u s) • (b • g (1 ⊗ x)) = g (s ⊗ x)`; both
  are additive, so `homBaseChangeMap E hE X Y (u ⊗ φ) = g`.
- `repHomBaseChangeMap_bijective`, `repHomBaseChangeEquiv`: the two previous
  theorems, and Mathlib's `LinearEquiv.ofBijective`.
- `repCohomologyHomBaseChangeMap_bijective_of_isLocalization`:
  `cohomologyHomBaseChangeMap_bijective_iff` and
  `repHomBaseChangeMap_bijective` for `X = H^q K` and `Y = W`.
- `repHom_isSMulRegular`: if `r • φ = r • ψ`, then `r • φ x = r • ψ x` for
  every `x`, so `φ x = ψ x` by `hY`.
- `smoothRepHom_isSMulRegular`: morphisms of smooth representations are
  morphisms of the underlying representations (Mathlib's
  `ObjectProperty.hom_ext`), so this is `repHom_isSMulRegular`.

## Smooth representations

Section `Smooth` takes `R` (implicit) and `S` (explicit) with `[Algebra R S]`
and a topological group `G : Type uG` (`[Group G] [TopologicalSpace G]`,
implicit). Below `X`, `Y` are objects of `SmoothRep.{uR, uG, w} R G`, with
underlying representations `X.obj`, `Y.obj`;
`E' = smoothRepExtendScalars.{w} R S G` is the Library's extension of scalars of
smooth representations, `hE' = smoothRepExtendScalars_isSemilinear.{w} R S G`,
and `E`, `hE` are as in section `Rep`. Write `ι` for Mathlib's `R`-linear
equivalence `InducedCategory.homLinearEquiv : (X ⟶ Y) ≃ₗ[R] (X.obj ⟶ Y.obj)`
between morphisms of smooth representations and morphisms of the underlying
representations. From `smoothHomBaseChangeMap_bijective` on the section also
takes `M : Submonoid R` with `[IsLocalization M S]` (explicit), and for the
last theorem `[Module.Flat R S]`,
`[HasDerivedCategory.{s} (SmoothRep.{uR, uG, w} R G)]` and
`[HasDerivedCategory.{s'} (SmoothRep.{uS, uG, max uS w} S G)]`.

| Declaration | Statement |
| --- | --- |
| `smoothHomBaseChangeMap_hom S X Y t` | For `t : S ⊗[R] (X ⟶ Y)`: the underlying morphism of representations of `homBaseChangeMap E' hE' X Y t` is `homBaseChangeMap E hE X.obj Y.obj (ι.baseChange R S _ _ t)`. |
| `smoothHomBaseChangeMap_bijective_iff S X Y` | `homBaseChangeMap E' hE' X Y` is bijective if and only if `homBaseChangeMap E hE X.obj Y.obj` is bijective. |
| `smoothHomBaseChangeMap_bijective S M hY` | For `[Module.Finite (MonoidAlgebra R G) X.obj.ρ.asModule]` and `hY : ∀ m : M, IsSMulRegular Y (m : R)`: `homBaseChangeMap E' hE' X Y` is bijective. |
| `smoothCohomologyHomBaseChangeMap_bijective_of_isLocalization S M K q hW` | For `K : DerivedCategory (SmoothRep.{uR, uG, w} R G)`, `W : SmoothRep.{uR, uG, w} R G`, `q : ℤ` with `[Module.Finite (MonoidAlgebra R G) (H^q K).obj.ρ.asModule]` and `hW : ∀ m : M, IsSMulRegular W (m : R)`: the Library's `smoothCohomologyHomBaseChangeMap R S G K W q` is bijective. |

Proofs.

- `smoothHomBaseChangeMap_hom`: induction on `t`; on `s ⊗ₜ f` both sides are
  `s • E.map f.hom` by definition, and both sides are additive in `t`.
- `smoothHomBaseChangeMap_bijective_iff`: by the previous theorem, composing
  `homBaseChangeMap E' hE' X Y` with the bijection `ι` for `E'.obj X`,
  `E'.obj Y` gives `homBaseChangeMap E hE X.obj Y.obj` composed with the
  bijection `ι.baseChange R S _ _`.
- `smoothHomBaseChangeMap_bijective`: `smoothHomBaseChangeMap_bijective_iff`
  and `repHomBaseChangeMap_bijective`.
- `smoothCohomologyHomBaseChangeMap_bijective_of_isLocalization`: the Library's
  `smoothCohomologyHomBaseChangeMap R S G K W q` is by definition
  `cohomologyHomBaseChangeMap E' hE' K W q`, so this is
  `cohomologyHomBaseChangeMap_bijective_iff` and
  `smoothHomBaseChangeMap_bijective` for `X = H^q K` and `Y = W`.

## Provenance and interpretation

The statements, definitions and proofs are ours, assembled from Mathlib and the
Library. That `S ⊗_R Hom_R(X, Y) → Hom_S(S ⊗_R X, S ⊗_R Y)` is an isomorphism
for a localization `S` and a finitely presented `X` is standard commutative
algebra; here `X` is only assumed finitely generated (over `R[G]`), and the
missing finite presentation is compensated by the hypothesis that `Y` has no
`M`-torsion. The Markdown file of `Langlands.Cohomology.HyperextScalarExtension`
records that the comparison maps there are in general not isomorphisms and that
whether they are in Harris's situation depends on finiteness properties that
are not formalized; this module gives one set of sufficient conditions for
the map on `Hom(H^q K, W)`.

The passage of Harris 1999 behind this module is the one quoted, from the
rendered scans, in the Markdown files of
`Langlands.Cohomology.HyperextScalarExtension` and
`Langlands.Cohomology.HyperextInvariantsLocalization`:

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`).
- §3, printed p.307 (one-based PDF page 9): "Let `𝒪` denote the ring of
  integers of `L_ℓ`, and let `𝓛_W` be a `K_ℓ`-stable `𝒪`-lattice in `W(L)`."
- §5, printed p.312 (one-based PDF page 14): "the spectral sequence (4.10.1)
  degenerates to an isomorphism (5.2)
  `Hom_GJ(H_c^{2(n-1)-j}(M̆_N, 𝒪(n - 1)), 𝒜_ℓ(GJ, ρ, H)[π^v])[JL(π_v)] ≅ H^j(S̄_{K(N)}, W̃)[π]`".

Interpretation (explanation only). In (5.2) a group of homomorphisms out of the
integral cohomology `H_c(M̆_N, 𝒪(n - 1))` is compared with objects with
`L_ℓ`-coefficients. With `R = 𝒪`, `S = L_ℓ = 𝒪[1/ℓ]` (a localization of `𝒪`
at the powers of `ℓ`, as explained in the Markdown file of
`HyperextScalarExtension`; the formalization does not construct this
`IsLocalization` instance), this module shows that
`L_ℓ ⊗_𝒪 Hom_G(H, W) → Hom_G(L_ℓ ⊗_𝒪 H, L_ℓ ⊗_𝒪 W)` is an isomorphism for
smooth representations when `H` is finitely generated over `𝒪[G]` and `W` has
no `ℓ`-torsion. For example, an `𝒪`-module on which `ℓ` acts invertibly, such
as an `L_ℓ`-vector space regarded as an `𝒪`-module, has no `ℓ`-torsion. The
module does not identify `G`, `K` or `W` with Harris's objects, and whether
Harris's cohomology groups are finitely generated over the relevant group
algebra is not addressed.

## Scope

- Without finite generation the conclusion fails even for the trivial group:
  in the example of the Markdown file of `HyperextScalarExtension`
  (explanation only, not formalized: `R = ℤ`, `S = ℚ`, `X = ⊕_{k ∈ ℕ} ℤ`,
  `Y = ℤ`), the map `ℚ ⊗_ℤ ℤ^ℕ → ℚ^ℕ` is not surjective. Without the torsion
  hypothesis on `Y` the injectivity proof does not apply.
- The finite generation of `H^q K` over `R[G]` and the absence of `M`-torsion
  in `W` are hypotheses; they are not verified for any complex, and whether they
  hold in Harris's situation remains an open obligation.
- Only `Hom(H^q K, W)` is treated. The maps on `Hom(K, W₀⟦n⟧)`, on `Ext`
  groups, on invariants of hyperext groups and on isotypic parts are not proved
  bijective here.
- `HasDerivedCategory` is a hypothesis; the results hold for each such
  instance.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
pp.307 and 312 (rendered scans) as quoted in
`Langlands.Cohomology.HyperextScalarExtension` and
`Langlands.Cohomology.HyperextInvariantsLocalization`.

Dependencies: `Langlands.Cohomology.HyperextIsotypicBaseChange`,
`Mathlib.Algebra.Module.LocalizedModule.Int`,
`Mathlib.RingTheory.Flat.Localization` and
`Mathlib.RingTheory.Localization.BaseChange`, with Mathlib pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
