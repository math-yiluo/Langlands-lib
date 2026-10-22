# Finite etale torsion of abelian schemes: proof

Author: Worker 268.

Module `Langlands.AbelianScheme.TorsionFiniteEtale`. This module proves the
Library statement `Langlands.AbelianScheme.TorsionFiniteEtaleStatement`
(module `Langlands.AbelianScheme.TorsionFiniteEtaleStatement`).

## Result

```lean
theorem Langlands.AbelianScheme.torsionFiniteEtale : TorsionFiniteEtaleStatement.{u}
```

So for every scheme `S : Scheme.{u}`, every `A : AbelianScheme S` and every
natural number `n` with `0 < n` and `IsUnit (n : Γ(S, ⊤))`, the structure
morphism `(GroupScheme.torsion A.toGrp (n : ℤ)).X.hom` is `IsFinite` and
`Etale`. The hypothesis `0 < n` is not used: invertibility of `n` alone gives
the conclusion. The proof uses only the axioms `propext`, `Classical.choice`
and `Quot.sound`.

The proof imports two helper modules, also part of this contribution:
`Langlands.AlgebraicGeometry.AffineChartPoints` (points `testObj hS₀ C ⟶ Y` over
`S` with values in `Spec C` for algebras `C` over the sections of an affine
open `S₀`, and affine charts `Chart S₀ Y`) and
`Langlands.AlgebraicGeometry.InfinitesimalKernel` (unique divisibility of
infinitesimal kernels of group objects). Their own Markdown files describe
them. The proof does not use the statements
`MultiplicationIsogenyStatement` or `MultiplicationEtaleStatement`.

Below, `π := (torsion A.toGrp (n : ℤ)).X.hom`, `ι := (torsionι A.toGrp (n :
ℤ)).hom.hom`, and `p := A.toGrp.X.hom`.

## Auxiliary morphism lemmas (namespace `Langlands.AlgebraicGeometry`)

- `locallyOfFinitePresentation_of_comp`: if `f ≫ g` is locally of finite
  presentation and `g` is locally of finite type, then `f` is locally of finite
  presentation. The proof uses the affine-local criterion
  `HasRingHomProperty.iff_exists_appLE`. For `x` it picks affine opens
  `U ∋ g (f x)`, `V ∋ f x` with `V ≤ g ⁻¹ᵁ U` and `W ∋ x` with `W ≤ f ⁻¹ᵁ V`. It
  factors `(f ≫ g).appLE U W` as `g.appLE U V` followed by `f.appLE V W`
  (`Scheme.Hom.appLE_comp_appLE`) and applies
  `RingHom.FinitePresentation.of_comp_finiteType`.
- `locallyQuasiFinite_of_etale`: an etale morphism is locally quasi-finite. On
  affine opens, `f.appLE U V e` is etale, so the algebra is
  `Algebra.QuasiFinite` by Mathlib's instance for etale algebras
  (`Mathlib.RingTheory.Unramified.LocalStructure`). Then
  `HasRingHomProperty.iff_appLE` concludes.

## Formal etaleness on charts (namespace `Langlands.AlgebraicGeometry.TorsionChart`)

The setting is a commutative group object `M : Over S` (`[GrpObj M]`,
`[IsCommMonObj M]`), an object `T : Over S` with a monomorphism `j : T ⟶ M`,
and a natural number `n`. The hypothesis

```lean
htors : ∀ {Y : Over S} (x : Y ⟶ M), (∃ y : Y ⟶ T, y ≫ j = x) ↔ x ^ n = 1
```

says that `T` is the `n`-torsion of `M`. Fix also an affine open `S₀` with
`hn : IsUnit (n : Γ(S, S₀))`, charts `cV : Chart S₀ T` and
`cA cW : Chart S₀ M`, and inclusions `hVA : cV.U ≤ j.left ⁻¹ᵁ cA.U` and
`hVW : cV.U ≤ (1 : T ⟶ M).left ⁻¹ᵁ cW.U`. Let `D` be a `Γ(S, S₀)`-algebra and
`I` an ideal with `I ^ 2 = ⊥`. Write `ρ` for the restriction along
`Spec (D ⧸ I) ⟶ Spec D`.

- `range_one_subset`: for every point `cV.pt ψ` over any algebra `C`, the unit
  `1 : testObj hS₀ C ⟶ M` equals `cV.pt ψ ≫ 1` (`MonObj.comp_one`), so its
  image lies in `cW.U` by `hVW`. With `C := D ⧸ I`, this is the hypothesis `hW`
  of the infinitesimal-kernel results for the chart `cW`.
- `isUnit_natCast`: `n` is a unit in every `Γ(S, S₀)`-algebra.
- `comp_injective`: reduction modulo `I` is injective on
  `cV.Ring →ₐ[Γ(S, S₀)] D`. Let `φ₁, φ₂` have equal reductions. Put
  `xᵢ := cV.pt φᵢ ≫ j`. Then `x₁ * x₂⁻¹` is trivial after `ρ` and has
  `(x₁ * x₂⁻¹) ^ n = 1` (by `htors` and commutativity, `mul_pow`). So
  `x₁ * x₂⁻¹ = 1` by `InfinitesimalKernel.eq_one_of_pow_eq_one`. Cancelling
  the monomorphism `j` and using `Chart.pt_injective` gives `φ₁ = φ₂`.
- `comp_surjective`: assume `[Algebra.FormallySmooth Γ(S, S₀) cA.Ring]`. Then
  every `φ : cV.Ring →ₐ[Γ(S, S₀)] D ⧸ I` lifts to `D`. The point
  `cV.pt φ ≫ j` lands in `cA.U` by `hVA`, so it is `cA.pt χ`
  (`Chart.exists_pt`). Formal smoothness lifts `χ` to `D`, giving a point `x`
  of `M` over `Spec D` with `ρ ≫ x = cV.pt φ ≫ j`. Hence `x ^ n` lies in the
  infinitesimal kernel, by `htors` and `MonObj.comp_pow`. By
  `InfinitesimalKernel.exists_pow_eq` there is `r` in the kernel with
  `r ^ n = x ^ n`. Then `(x * r⁻¹) ^ n = 1`, so `x * r⁻¹ = y ≫ j` for some
  `y : testObj hS₀ D ⟶ T` by `htors`. Moreover `ρ ≫ y = cV.pt φ` after
  cancelling `j`. The image of `y` equals the image of `ρ ≫ y`
  (`range_testHom_comp`), so it lies in `cV.U`. Thus `y = cV.pt ψ`, and
  `Chart.pt_injective` shows that `ψ` reduces to `φ`.
- `formallyEtale`: under the same assumption, `cV.Ring` is formally etale over
  `Γ(S, S₀)`, by `Algebra.FormallyEtale.iff_comp_bijective` and the two
  previous lemmas.

## The torsion scheme (namespace `Langlands.AbelianScheme`)

- `torsion_locallyOfFinitePresentation`: `π` is locally of finite
  presentation. Since `η.left ≫ p = 𝟙 S` (`Over.w`) and `p` is smooth, hence
  locally of finite type, the unit section `η[A.toGrp.X].left` is locally of
  finite presentation (`locallyOfFinitePresentation_of_comp`). The Library
  square `torsion_isPullback_scheme` exhibits `ι.left` as a base change of
  `η.left` along multiplication by `n`. So `ι.left` is locally of finite
  presentation (`MorphismProperty.of_isPullback`), and so is
  `π = ι.left ≫ p`.
- `torsion_isProper`: `π = ι.left ≫ p` is proper. Here `ι.left` is a closed
  immersion by the Library instance `torsionι_isClosedImmersion` (as `p` is
  proper, hence separated), and `p` is proper.
- `exists_torsion_lift_iff`: a point `x : Y ⟶ A.toGrp.X` over `S` factors
  through `ι` iff `x ^ n = 1`. This follows from the Library lemma
  `existsUnique_torsion_lift_iff` and `zpow_natCast`.
- `torsion_etale (hn : IsUnit (n : Γ(S, ⊤)))`: `π` is etale. The proof uses
  the affine-local criterion `HasRingHomProperty.iff_exists_appLE` for
  `@Etale`. Its hypothesis on localizations comes from
  `RingHom.Etale.stableUnderComposition` and `RingHom.Etale.propertyIsLocal`.
  For a point `x` of `A[n]` it chooses:
  - an affine open `S₀ ∋ π x` of `S`;
  - affine opens `UA ∋ ι x` and `W ∋ 1 x` of `A` inside `p ⁻¹ᵁ S₀`, where
    `1 : A[n] ⟶ A` is the unit point;
  - an affine open `V ∋ x` of `A[n]` inside `ι⁻¹ᵁ UA ⊓ 1⁻¹ᵁ W`, hence inside
    `π ⁻¹ᵁ S₀`.

  With charts `cV := ⟨V, …⟩`, `cA := ⟨UA, …⟩`, `cW := ⟨W, …⟩`, the
  `Γ(S, S₀)`-algebra `cA.Ring` is smooth, because `p` is smooth
  (`HasRingHomProperty.appLE`). The algebra `cV.Ring` is finitely presented by
  `torsion_locallyOfFinitePresentation`, and formally etale by
  `TorsionChart.formallyEtale` with `htors := exists_torsion_lift_iff` and the
  restriction of `hn` to `S₀`. Hence `π.appLE S₀ V _` is etale
  (`RingHom.etale_algebraMap`).
- `torsionFiniteEtale`: `π` is etale (`torsion_etale`) and proper
  (`torsion_isProper`). Being etale, it is locally quasi-finite
  (`locallyQuasiFinite_of_etale`). Zariski's main theorem in the form
  `IsFinite.of_isProper_of_locallyQuasiFinite` gives that `π` is finite.

## Relation to the literature

The statement's Markdown cites J. S. Milne, *Abelian Varieties* (registered as
`milne-abelian-varieties-1986-author-2022`), Proposition 20.7, p.44. As that
Markdown describes it, Milne's proof uses that multiplication by `n` is finite
flat (via Theorem 8.2) and a fibrewise etaleness result. The implemented proof
takes a different route and does not use that multiplication by `n` is an
isogeny.
Etaleness is proved by the infinitesimal lifting criterion on affine charts,
using smoothness of `A` and unique `n`-divisibility of infinitesimal kernels.
Finiteness follows from properness and local quasi-finiteness. Only the
invertibility of `n` on the base is used, never `0 < n`, a constant relative
dimension, or the geometric connectedness of the fibres.
