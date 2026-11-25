/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Polynomial
public import WeilConjectures.Mathlib.RingTheory.Regular.ProjectiveDimension
public import WeilConjectures.Mathlib.RingTheory.Smooth.Local
public import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmooth
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# The étale-local normal form of a smooth morphism

A smooth morphism of relative dimension `d` is, étale-locally on the source, the
projection of an affine space: if `g : X ⟶ Y` is smooth of relative dimension `d` and
`x : X`, then there are affine open neighbourhoods `V` of `x` and `U` of `g.base x` with
`V ≤ g ⁻¹ᵁ U` such that the restricted morphism `g.resLE U V` factors as an étale morphism
`V ⟶ 𝔸(d; U)` followed by the structure morphism `𝔸(d; U) ↘ U`.

The index type of the affine space is `ULift.{u} (Fin d)`, since
`AlgebraicGeometry.AffineSpace` takes an index type in the same universe as the scheme.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_etale_to_affineSpace_of_isStandardSmoothOfRelativeDimension`:
  the normal form over a pair of affine opens on which the morphism is standard smooth.
- `AlgebraicGeometry.Smooth.exists_etale_to_affineSpace`: the étale-local normal form of a
  smooth morphism of relative dimension `d`.
- `AlgebraicGeometry.Scheme.Hom.exists_etale_to_affineSpace_of_mem_smoothLocus`: the étale-local
  normal form of a morphism near a point at which it is smooth.
- `AlgebraicGeometry.Smooth.exists_etale_affineSpace`: a smooth morphism is, on an affine open
  neighbourhood of any point of the source, étale over an affine space over the target.
- `AlgebraicGeometry.smoothOfRelativeDimension_iff_topologicalKrullDim_eq`: an irreducible
  scheme smooth over a field is smooth of relative dimension `n` if and only if it has
  dimension `n`.
- `AlgebraicGeometry.topologicalKrullDim_le_of_smoothOfRelativeDimension`: a scheme smooth of
  relative dimension `n` over a field has dimension at most `n`.
- `AlgebraicGeometry.topologicalKrullDimAt_eq_of_smoothOfRelativeDimension`: a scheme smooth of
  relative dimension `n` over a field has local dimension `n` at every point.
- `AlgebraicGeometry.Smooth.isLocallyConstant_topologicalKrullDimAt_asFiber`: for a smooth
  morphism `f : X ⟶ Y`, the function `x ↦ dim_x (X_{f(x)})` is locally constant.
- `AlgebraicGeometry.AffineSpace.smoothOfRelativeDimension_over`: the affine space `𝔸(n; S)` in
  finitely many variables is smooth of relative dimension `#n` over `S`.
- `AlgebraicGeometry.AffineSpace.smoothOfRelativeDimension_reindex_succ`: forgetting the first
  coordinate `𝔸^{d+1}_S ⟶ 𝔸^d_S` is smooth of relative dimension one.
- `AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_resLE`: a smooth morphism is
  locally smooth of some relative dimension.
- `AlgebraicGeometry.smoothOfRelativeDimension_pullback_fst`,
  `AlgebraicGeometry.smoothOfRelativeDimension_pullback_snd`: smoothness of relative dimension `n`
  is inherited by the projections of a fibre product.
- `AlgebraicGeometry.coheight_le_of_smoothOfRelativeDimension`: every point of a scheme smooth of
  relative dimension `n` over a field has codimension at most `n`.
- `AlgebraicGeometry.smoothOfRelativeDimension_of_fiberToSpecResidueField`: a smooth morphism
  whose fibres are smooth of relative dimension `n` is smooth of relative dimension `n`.
- `AlgebraicGeometry.Smooth.isRegularLocalRing_stalk`: the local rings of a scheme smooth over a
  field are regular.
- `AlgebraicGeometry.Scheme.Hom.mem_smoothLocus_of_isRegularLocalRing`: over an algebraically
  closed field, a scheme locally of finite type is smooth at its regular closed points.
- `AlgebraicGeometry.Smooth.of_comp_of_flat_of_surjective_of_field`: smoothness over a field
  descends along flat surjections (Stacks, Tag 05AX).
- `AlgebraicGeometry.Smooth.of_comp_of_flat_of_surjective`: smoothness descends along flat
  surjections locally of finite presentation of the source.
- `AlgebraicGeometry.smoothOfRelativeDimension_of_comp_of_isFinite_of_surjective`: smoothness of
  relative dimension `n` descends along a finite locally free surjection of the source.

## References

- Stacks Project, Tag `054L`, <https://stacks.math.columbia.edu/tag/054L>
- Stacks Project, Tag `05AX`, <https://stacks.math.columbia.edu/tag/05AX>
- Stacks Project, Tag `05B5`, <https://stacks.math.columbia.edu/tag/05B5>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Limits in
instance smoothOfRelativeDimension_pullback_fst {X Y Z : Scheme.{u}} (n : ℕ) (f : X ⟶ Z)
    (g : Y ⟶ Z) [SmoothOfRelativeDimension n g] :
    SmoothOfRelativeDimension n (pullback.fst f g) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension n) _ _ inferInstance

open Limits in
instance smoothOfRelativeDimension_pullback_snd {X Y Z : Scheme.{u}} (n : ℕ) (f : X ⟶ Z)
    (g : Y ⟶ Z) [SmoothOfRelativeDimension n f] :
    SmoothOfRelativeDimension n (pullback.snd f g) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _ inferInstance

open MvPolynomial in
/-- Let `g : X ⟶ Y`, and let `U ⊆ Y`, `V ⊆ X` be affine opens with `V ≤ g ⁻¹ᵁ U` such that
`Γ(Y, U) ⟶ Γ(X, V)` is standard smooth of relative dimension `d`. Then `g.resLE U V hVU`
factors as an étale morphism `e : V ⟶ 𝔸(d; U)` followed by the projection `𝔸(d; U) ↘ U`:

```
V --e--> 𝔸(d; U)
 \          |
  \         ↓
g.resLE     U
```

On rings, this is `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`:
reading the last `d` variables of a submersive presentation as coordinates of the base turns
it into a square Jacobian presentation over `Γ(Y, U)[x₁, …, x_d]`. -/
theorem Scheme.Hom.exists_etale_to_affineSpace_of_isStandardSmoothOfRelativeDimension
    {X Y : Scheme.{u}} (g : X ⟶ Y) {d : ℕ} {U : Y.Opens} {V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hVU : V ≤ g ⁻¹ᵁ U)
    (H : (g.appLE U V hVU).hom.IsStandardSmoothOfRelativeDimension d) :
    ∃ e : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); U.toScheme),
      Etale e ∧ e ≫ (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme) = g.resLE U V hVU := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  obtain ⟨φ, hφC, hφ⟩ := H.exists_etale_mvPolynomial
  let ε : MvPolynomial (ULift.{u} (Fin d)) Γ(U.toScheme, ⊤) ≃+* MvPolynomial (Fin d) Γ(Y, U) :=
    (mapEquiv _ U.topIso.commRingCatIsoToRingEquiv).trans
      (renameEquiv Γ(Y, U) Equiv.ulift).toRingEquiv
  let ψ : MvPolynomial (ULift.{u} (Fin d)) Γ(U.toScheme, ⊤) →+* Γ(V.toScheme, ⊤) :=
    (V.topIso.symm.commRingCatIsoToRingEquiv.toRingHom.comp φ).comp ε.toRingHom
  have hψ : ψ.Etale :=
    RingHom.Etale.respectsIso.2 _ _ (RingHom.Etale.respectsIso.1 _ _ hφ)
  have hψC : CommRingCat.ofHom (ψ.comp C) = (g.resLE U V hVU).appTop := by
    ext r
    change ψ (C r) = (g.resLE U V hVU).app ⊤ r
    have := RingHom.congr_fun hφC (U.topIso.hom r)
    rw [RingHom.comp_apply] at this
    have hε : ε (C r) = C (U.topIso.hom r) := by simp [ε]
    rw [Scheme.Hom.resLE_app_top]
    simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hε,
      this]
    rfl
  have : Etale (Spec.map (CommRingCat.ofHom ψ)) := HasRingHomProperty.Spec_iff.mpr hψ
  refine ⟨V.toScheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ) ≫
    (AffineSpace.isoOfIsAffine _ U.toScheme).inv, inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, AffineSpace.isoOfIsAffine_inv_over, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp, hψC, Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The étale-local normal form (blueprint `sk-prop-normal-form`).
Let `g : X ⟶ Y` be smooth of relative dimension `d` and let `x : X`. After replacing
`X` and `Y` by affine open neighbourhoods `V ∋ x` and `U ∋ g.base x` with `V ≤ g ⁻¹ᵁ U`,
the morphism `g` factors as an étale morphism `e : V ⟶ 𝔸(d; U)` followed by the projection
`𝔸(d; U) ↘ U`:

```
V --e--> 𝔸(d; U)
 \          |
  \         ↓
g.resLE     U
```
-/
@[stacks 054L]
theorem Smooth.exists_etale_to_affineSpace {X Y : Scheme.{u}} (g : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d g] (x : X) :
    ∃ (U : Y.Opens) (V : X.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V)
      (_ : g.base x ∈ U) (_ : x ∈ V) (hVU : V ≤ g ⁻¹ᵁ U)
      (e : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); U.toScheme)),
      Etale e ∧ e ≫ (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme) = g.resLE U V hVU := by
  obtain ⟨U, hU, V, hV, hx, hVU, H⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := d) (f := g) x
  obtain ⟨e, he, hge⟩ :=
    g.exists_etale_to_affineSpace_of_isStandardSmoothOfRelativeDimension hU hV hVU H
  exact ⟨U, V, hU, hV, hVU hx, hx, hVU, e, he, hge⟩

/-- The étale-local normal form of a morphism smooth at a point (blueprint
`proposition-exceptional-inverse-image-smooth-morphism`). Let `g : X ⟶ Y` be locally of finite
presentation and smooth at `x : X`. Then there are `d : ℕ` and affine open neighbourhoods `V ∋ x`
and `U ∋ g.base x` with `V ≤ g ⁻¹ᵁ U` such that `g.resLE U V hVU` factors as an étale morphism
`e : V ⟶ 𝔸(d; U)` followed by the projection `𝔸(d; U) ↘ U`:

```
V --e--> 𝔸(d; U)
 \          |
  \         ↓
g.resLE     U
```

Near `x` the ring map `Γ(Y, U) ⟶ Γ(X, V)` is standard smooth, and
`Scheme.Hom.exists_etale_to_affineSpace_of_isStandardSmoothOfRelativeDimension` applies. -/
@[stacks 054L]
theorem Scheme.Hom.exists_etale_to_affineSpace_of_mem_smoothLocus {X Y : Scheme.{u}} (g : X ⟶ Y)
    [LocallyOfFinitePresentation g] {x : X} (hx : x ∈ g.smoothLocus) :
    ∃ (d : ℕ) (U : Y.Opens) (V : X.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V)
      (_ : g.base x ∈ U) (_ : x ∈ V) (hVU : V ≤ g ⁻¹ᵁ U)
      (e : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); U.toScheme)),
      Etale e ∧ e ≫ (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme) = g.resLE U V hVU := by
  obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ := exists_smooth_of_formallySmooth_stalk g x hx
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : Smooth (g.resLE U V hVU) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
    exact (RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso g U V hVU)).mpr H
  obtain ⟨U', hU', V', hV', hxV', hVU', H'⟩ :=
    Smooth.exists_isStandardSmooth (g.resLE U V hVU) ⟨x, hxV⟩
  let := ((g.resLE U V hVU).appLE U' V' hVU').hom.toAlgebra
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := H'
  obtain ⟨n, H''⟩ : ∃ n,
      ((g.resLE U V hVU).appLE U' V' hVU').hom.IsStandardSmoothOfRelativeDimension n :=
    ⟨_, _, _, _, ‹_›, P, rfl⟩
  rw [Scheme.Hom.resLE_appLE] at H''
  have hU'' := hU'.image_of_isOpenImmersion U.ι
  have hV'' := hV'.image_of_isOpenImmersion V.ι
  obtain ⟨e, he, hge⟩ :=
    g.exists_etale_to_affineSpace_of_isStandardSmoothOfRelativeDimension hU'' hV'' _ H''
  have hxV'' : x ∈ V.ι ''ᵁ V' := ⟨⟨x, hxV⟩, hxV', rfl⟩
  exact ⟨_, _, _, hU'', hV'', (le_resLE_preimage_iff g hVU U' V').mp hVU' hxV'', hxV'', _, e,
    he, hge⟩

/-- **Local structure of smooth morphisms**: around every point of `X`, a smooth morphism
`t : X ⟶ Y` is, on an affine open `W ⊆ X` (given by an open immersion `ι : W ⟶ X`), the
composite of an étale morphism `e : W ⟶ 𝔸ⁿ_Y` and the projection `𝔸ⁿ_Y ⟶ Y`:

```
W --e--> 𝔸ⁿ_Y
|ι         |
v          v
X ---t---> Y
```
-/
theorem Smooth.exists_etale_affineSpace {X Y : Scheme.{u}} (t : X ⟶ Y) [Smooth t] (x : X) :
    ∃ (W : Scheme.{u}) (ι : W ⟶ X) (_ : IsOpenImmersion ι) (_ : IsAffine W)
      (_ : x ∈ Set.range ι.base) (n : ℕ) (e : W ⟶ 𝔸(ULift.{u} (Fin n); Y)),
      Etale e ∧ e ≫ 𝔸(ULift.{u} (Fin n); Y) ↘ Y = ι ≫ t := by
  obtain ⟨U, hU, V, hV, hxV, eUV, hss⟩ := Smooth.exists_isStandardSmooth t x
  obtain ⟨n, g, hgC, hg⟩ := hss.exists_etale_mvPolynomial
  have : Etale (Spec.map (CommRingCat.ofHom g)) := HasRingHomProperty.Spec_iff.mpr hg
  let r := (MvPolynomial.renameEquiv Γ(Y, U) (Equiv.ulift (α := Fin n))).toRingEquiv
  have : IsIso (Spec.map (CommRingCat.ofHom r.toRingHom)) :=
    inferInstanceAs (IsIso (Spec.map r.toCommRingCatIso.hom))
  refine ⟨Spec Γ(X, V), hV.fromSpec, inferInstance, inferInstance, ?_, n,
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom r.toRingHom) ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) Γ(Y, U)).inv ≫
        AffineSpace.map (ULift.{u} (Fin n)) hU.fromSpec, inferInstance, ?_⟩
  · rw [hV.range_fromSpec]
    exact hxV
  · rw [Category.assoc, Category.assoc, Category.assoc, AffineSpace.map_over,
      AffineSpace.SpecIso_inv_over_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
      ← IsAffineOpen.SpecMap_appLE_fromSpec t hU hV eUV]
    congr 2
    ext1
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom,
      CommRingCat.hom_ofHom, ← hgC]
    ext a
    simp [r]

open Order in
/-- Let `φ : K[X₁, …, Xₙ] ⟶ A` be an étale ring map over a field `K`. Every point of `Spec A`
has codimension at most `n`, and every closed point has codimension exactly `n`: the étale map
`Spec A ⟶ 𝔸ⁿ_K` preserves codimension and maps closed points to closed points, and maximal
ideals of `K[X₁, …, Xₙ]` have height `n`. -/
theorem coheight_le_of_etale_mvPolynomial {K : Type u} [Field K] {A : CommRingCat.{u}} {n : ℕ}
    (φ : MvPolynomial (Fin n) K →+* A) (hφ : φ.Etale) (y : Spec A) :
    coheight y ≤ n ∧ (IsClosed {y} → coheight y = n) := by
  let g := Spec.map (CommRingCat.ofHom φ)
  have : Etale g := HasRingHomProperty.Spec_iff.mpr hφ
  rw [← g.coheight_apply_of_flat y, ← idealHeight_eq_coheight]
  refine ⟨?_, fun hy ↦ ?_⟩
  · have h := Ideal.height_le_ringKrullDim_of_ne_top (g y).2.ne_top
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field] at h
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
    exact_mod_cast h
  · have : (g y).asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
      (g.closedPoints_subset_preimage_closedPoints hy)
    exact MvPolynomial.height_eq_of_isMaximal n _

/-- A scheme `X` smooth of relative dimension `n` over a field `K` is covered by affine opens
`V` such that `Γ(X, V)` is étale over the polynomial ring `K[X₁, …, Xₙ]`. -/
theorem SmoothOfRelativeDimension.exists_etale_mvPolynomial_of_field {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (φ : MvPolynomial (Fin n) K →+* Γ(X, V)),
      φ.Etale := by
  obtain ⟨U, -, V, hV, hx, hVU, H⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  obtain rfl : U = ⊤ := eq_top_iff.mpr fun z _ ↦ Subsingleton.elim (f x) z ▸ hVU hx
  obtain ⟨φ, -, hφ⟩ := H.exists_etale_mvPolynomial
  let e : MvPolynomial (Fin n) K ≃+* MvPolynomial (Fin n) Γ(Spec (.of K), ⊤) :=
    MvPolynomial.mapEquiv _ (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  exact ⟨V, hV, hx, φ.comp e.toRingHom, RingHom.Etale.respectsIso.2 _ _ hφ⟩

open Order in
/-- Every point of a scheme smooth of relative dimension `n` over a field has codimension at
most `n`. -/
theorem coheight_le_of_smoothOfRelativeDimension {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    coheight x ≤ n := by
  obtain ⟨V, hV, hx, φ, hφ⟩ := SmoothOfRelativeDimension.exists_etale_mvPolynomial_of_field f n x
  obtain ⟨y, rfl⟩ : ∃ y, hV.fromSpec y = x := ⟨_, hV.fromSpec_primeIdealOf ⟨x, hx⟩⟩
  rw [coheight_eq_of_isOpenImmersion]
  exact (coheight_le_of_etale_mvPolynomial φ hφ _).1

open Order in
/-- A closed point of a scheme smooth of relative dimension `n` over a field has codimension
exactly `n`: in an affine chart étale over `K[X₁, …, Xₙ]` it is a maximal ideal, of height `n`. -/
theorem coheight_eq_of_smoothOfRelativeDimension_of_isClosed {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] {x : X}
    (hx : IsClosed ({x} : Set X)) : coheight x = n := by
  obtain ⟨V, hV, hxV, φ, hφ⟩ := SmoothOfRelativeDimension.exists_etale_mvPolynomial_of_field f n x
  obtain ⟨y, hy⟩ : ∃ y, hV.fromSpec y = x := ⟨_, hV.fromSpec_primeIdealOf ⟨x, hxV⟩⟩
  have hy' : IsClosed ({y} : Set (Spec Γ(X, V))) := by
    have : hV.fromSpec.base ⁻¹' {x} = {y} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h ↦ hV.fromSpec.isOpenEmbedding.injective (h.trans hy.symm), fun h ↦ h ▸ hy⟩
    rw [← this]
    exact hx.preimage hV.fromSpec.base.hom.continuous
  rw [← hy, coheight_eq_of_isOpenImmersion]
  exact (coheight_le_of_etale_mvPolynomial φ hφ y).2 hy'

/-- A scheme smooth of relative dimension `n` over a field has dimension at most `n`. It is
normal and locally noetherian, so its connected components are open and irreducible; each of
them is smooth of relative dimension `n`, hence of dimension `n` by
`AlgebraicGeometry.smoothOfRelativeDimension_iff_topologicalKrullDim_eq`. -/
theorem topologicalKrullDim_le_of_smoothOfRelativeDimension {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] :
    topologicalKrullDim X ≤ n := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints,
    Order.krullDim_eq_iSup_coheight]
  exact iSup_le fun x ↦ by exact_mod_cast coheight_le_of_smoothOfRelativeDimension f n x

/-- A nonempty scheme smooth of relative dimension `n` over a field has dimension exactly `n`:
each of its connected components is irreducible and smooth of relative dimension `n`, hence of
dimension `n` by `AlgebraicGeometry.smoothOfRelativeDimension_iff_topologicalKrullDim_eq`. -/
theorem topologicalKrullDim_eq_of_smoothOfRelativeDimension {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    [Nonempty X] : topologicalKrullDim X = n := by
  refine le_antisymm (topologicalKrullDim_le_of_smoothOfRelativeDimension f n) ?_
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨V, hV, hx, φ, hφ⟩ := SmoothOfRelativeDimension.exists_etale_mvPolynomial_of_field f n x
  obtain ⟨M, hM, -⟩ := Ideal.exists_le_maximal _ (hV.primeIdealOf ⟨x, hx⟩).2.ne_top
  let y : Spec Γ(X, V) := ⟨M, hM.isPrime⟩
  have := (coheight_le_of_etale_mvPolynomial φ hφ y).2
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hM)
  rw [← coheight_eq_of_isOpenImmersion hV.fromSpec] at this
  have h := Order.coheight_le_krullDim (hV.fromSpec y)
  rw [this] at h
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints]
  exact_mod_cast h

open Limits in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Affine space is smooth** (blueprint `sbc-lem-affine-space-smooth`). The affine space
`𝔸(n; S)` over `S` in finitely many variables is smooth of relative dimension `#n` over `S`.

The affine space of blueprint `def-sbc-affine-space` is Mathlib's `AlgebraicGeometry.AffineSpace`,
and the smooth morphisms (of relative dimension `n`) of blueprint `def-sbc-smooth-morphisms` are
Mathlib's `AlgebraicGeometry.Smooth` and `AlgebraicGeometry.SmoothOfRelativeDimension`; the
morphisms locally of finite presentation of blueprint `def-sbc-locally-finite-presentation` are
Mathlib's `AlgebraicGeometry.LocallyOfFinitePresentation`. -/
instance AffineSpace.smoothOfRelativeDimension_over (n : Type u) [Finite n] (S : Scheme.{u}) :
    SmoothOfRelativeDimension (Nat.card n) (𝔸(n; S) ↘ S) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := Nat.card n)
  MorphismProperty.pullback_fst _ _ <| by
  have := isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal (terminal.from _)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C)),
    MorphismProperty.cancel_right_of_respectsIso (P := @SmoothOfRelativeDimension (Nat.card n)),
    HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Nat.card n))]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (R := ULift.{u} ℤ)
    (S := MvPolynomial n (ULift.{u} ℤ)) (n := Nat.card n)).2
      (MvPolynomial.isStandardSmoothOfRelativeDimension _ _)

set_option backward.isDefEq.respectTransparency.types false in
/-- The map `𝔸^{d+1}_S ⟶ 𝔸^d_S` forgetting the first coordinate is smooth of relative
dimension one: it is isomorphic, over `𝔸^d_S`, to the affine line `𝔸^1` over `𝔸^d_S`. Writing
`𝔸^d_S ⟶ S` as the composite of `d` such maps reduces statements about smooth morphisms to
relative dimension one. -/
instance AffineSpace.smoothOfRelativeDimension_reindex_succ (d : ℕ) (S : Scheme.{u}) :
    SmoothOfRelativeDimension 1
      (reindex (fun i : ULift.{u} (Fin d) ↦ (⟨i.down.succ⟩ : ULift.{u} (Fin (d + 1)))) S) := by
  set r := reindex (fun i : ULift.{u} (Fin d) ↦ (⟨i.down.succ⟩ : ULift.{u} (Fin (d + 1)))) S
  let B := 𝔸(ULift.{u} (Fin d); S)
  let φ : 𝔸(ULift.{u} (Fin (d + 1)); S) ⟶ 𝔸(PUnit.{u + 1}; B) :=
    homOfVector r (fun _ ↦ coord S ⟨0⟩)
  let ψ : 𝔸(PUnit.{u + 1}; B) ⟶ 𝔸(ULift.{u} (Fin (d + 1)); S) :=
    homOfVector ((𝔸(PUnit.{u + 1}; B) ↘ B) ≫ (B ↘ S))
      (fun j ↦ Fin.cases (coord B PUnit.unit)
        (fun i ↦ (𝔸(PUnit.{u + 1}; B) ↘ B).appTop (coord S ⟨i⟩)) j.down)
  have h₁ : φ ≫ ψ = 𝟙 _ := by
    apply hom_ext
    · simp only [φ, ψ, Category.assoc, homOfVector_over, homOfVector_over_assoc, r,
        Category.id_comp]
      exact reindex_over _ _
    · rintro ⟨i⟩
      induction i using Fin.cases with
      | zero => simp [φ, ψ]
      | succ i =>
        simp only [φ, ψ, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, homOfVector_appTop_coord,
          Fin.cases_succ, Scheme.Hom.id_appTop, CommRingCat.id_apply]
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
        simp only [homOfVector_over, r]
        exact reindex_appTop_coord _ _ _
  have h₂ : ψ ≫ φ = 𝟙 _ := by
    apply hom_ext
    · apply hom_ext
      · simp [φ, ψ, r]
      · rintro ⟨i⟩
        simp only [φ, ψ, r, Category.assoc, homOfVector_over, Scheme.Hom.comp_appTop,
          CommRingCat.comp_apply, reindex_appTop_coord, homOfVector_appTop_coord,
          Fin.cases_succ, Category.id_comp]
        rfl
    · rintro ⟨⟩
      simp [φ, ψ]
  have : IsIso φ := ⟨ψ, h₁, h₂⟩
  have hr : r = φ ≫ (𝔸(PUnit.{u + 1}; B) ↘ B) := by simp [φ]
  have : SmoothOfRelativeDimension (0 + Nat.card PUnit.{u + 1}) (φ ≫ (𝔸(PUnit.{u + 1}; B) ↘ B)) :=
    inferInstance
  simpa [hr] using this

/-- A smooth morphism is, locally on the source and on the target, smooth of some relative
dimension: every point `x` has affine open neighbourhoods `V ∋ x` and `U ∋ f.base x` with
`V ≤ f ⁻¹ᵁ U` such that `f.resLE U V` is smooth of relative dimension `d` for some `d`.
This is the input needed to apply `AlgebraicGeometry.Smooth.exists_etale_to_affineSpace` to
a smooth morphism whose relative dimension varies. -/
theorem Smooth.exists_smoothOfRelativeDimension_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) :
    ∃ (U : Y.Opens) (V : X.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V) (_ : x ∈ V)
      (e : V ≤ f ⁻¹ᵁ U) (d : ℕ), SmoothOfRelativeDimension d (f.resLE U V e) := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := (Smooth.iff_forall_exists_isStandardSmooth f).mp ‹_› x
  let := (f.appLE U V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hf.out
  have hd : (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension P.dimension :=
    P.isStandardSmoothOfRelativeDimension rfl
  refine ⟨U, V, hU, hV, hx, e, P.dimension, ?_⟩
  have : IsAffine U := hU
  have : IsAffine V := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)]
  have : (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension P.dimension))).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp <|
      (HasRingHomProperty.isLocal_ringHomProperty
        (@SmoothOfRelativeDimension P.dimension)).respectsIso
  exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension P.dimension)))
      (arrowResLEAppIso f U V e)).mpr
    (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hd)

/-- Smoothness of relative dimension `n` is local on the source: if every point of `X` has an
open neighbourhood `V` such that `V ⟶ Y` is smooth of relative dimension `n`, then so is
`f : X ⟶ Y`. -/
theorem smoothOfRelativeDimension_of_forall_exists_mem {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (H : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ SmoothOfRelativeDimension n (V.ι ≫ f)) :
    SmoothOfRelativeDimension n f := by
  choose V hxV hV using H
  exact IsZariskiLocalAtSource.of_iSup_eq_top V
    (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩) hV

/-- The relative dimension of a smooth morphism from a nonempty scheme to the spectrum of a
field is unique: it is the dimension of the source. -/
theorem SmoothOfRelativeDimension.eq_of_field {K : Type u} [Field K] {X : Scheme.{u}}
    [Nonempty X] (f : X ⟶ Spec (.of K)) {m n : ℕ} (hm : SmoothOfRelativeDimension m f)
    (hn : SmoothOfRelativeDimension n f) : m = n := by
  have h₁ := topologicalKrullDim_eq_of_smoothOfRelativeDimension f m
  have h₂ := topologicalKrullDim_eq_of_smoothOfRelativeDimension f n
  exact_mod_cast h₁.symm.trans h₂

/-- An irreducible scheme `X` smooth over a field `K` is smooth of relative dimension `n` over
`K` if and only if `X` has dimension `n`: the relative dimension of a smooth morphism at a point
is the dimension of the fibre at that point, and an irreducible scheme locally of finite type
over a field has the same dimension at all of its points. -/
theorem smoothOfRelativeDimension_iff_topologicalKrullDim_eq {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [Smooth f] [IrreducibleSpace X] (n : ℕ) :
    SmoothOfRelativeDimension n f ↔ topologicalKrullDim X = n := by
  refine ⟨fun _ ↦ topologicalKrullDim_eq_of_smoothOfRelativeDimension f n, fun h ↦ ?_⟩
  have key (x : X) : ∃ (V : X.Opens) (_ : x ∈ V) (d : ℕ),
      SmoothOfRelativeDimension d (V.ι ≫ f) := by
    obtain ⟨U, V, -, -, hx, e, d, hd⟩ := Smooth.exists_smoothOfRelativeDimension_resLE f x
    refine ⟨V, hx, d, ?_⟩
    rw [← Scheme.Hom.resLE_comp_ι f e]
    have : SmoothOfRelativeDimension (d + 0) (f.resLE U V e ≫ U.ι) := inferInstance
    simpa using this
  choose V hxV d hd using key
  have hres {W W' : X.Opens} (hWW' : W ≤ W') (m : ℕ) [SmoothOfRelativeDimension m (W'.ι ≫ f)] :
      SmoothOfRelativeDimension m (W.ι ≫ f) := by
    rw [← X.homOfLE_ι hWW', Category.assoc]
    have : SmoothOfRelativeDimension (0 + m) (X.homOfLE hWW' ≫ W'.ι ≫ f) := inferInstance
    simpa using this
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have hd₀ (x : X) : d x = d x₀ := by
    obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (V x).isOpen (V x₀).isOpen
      ⟨x, hxV x⟩ ⟨x₀, hxV x₀⟩
    have : Nonempty (V x ⊓ V x₀ : X.Opens) := ⟨⟨z, hz⟩⟩
    exact SmoothOfRelativeDimension.eq_of_field _ (hres (W' := V x) inf_le_left (d x))
      (hres (W' := V x₀) inf_le_right (d x₀))
  have : SmoothOfRelativeDimension (d x₀) f :=
    smoothOfRelativeDimension_of_forall_exists_mem f _ fun x ↦ ⟨V x, hxV x, hd₀ x ▸ hd x⟩
  have hn := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (d x₀)
  rw [h] at hn
  obtain rfl : n = d x₀ := by exact_mod_cast hn
  exact this

/-- A scheme `X` smooth of relative dimension `n` over a field has local dimension `n` at every
point: every open neighbourhood of a point is a nonempty scheme smooth of relative dimension `n`
over the field, hence of dimension `n` by
`AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension`. -/
theorem topologicalKrullDimAt_eq_of_smoothOfRelativeDimension {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    topologicalKrullDimAt x = n := by
  refine topologicalKrullDimAt_eq_of_forall fun (U : X.Opens) hU ↦ ?_
  have : Nonempty U.toScheme := ⟨⟨x, hU⟩⟩
  have : SmoothOfRelativeDimension n (U.ι ≫ f) := by
    have : SmoothOfRelativeDimension (0 + n) (U.ι ≫ f) := inferInstance
    simpa using this
  exact topologicalKrullDim_eq_of_smoothOfRelativeDimension (U.ι ≫ f) n

open Limits in
/-- **Local constancy of the relative dimension** (blueprint
`lemma-smooth-morphisms-locally-constant-sheaves`). For a smooth morphism `f : X ⟶ Y`, the
function `x ↦ dim_x (X_{f(x)})`, the local dimension at `x` of the fibre of `f` through `x`, is
locally constant on `X`.

Near `x`, the morphism `f` restricts to a morphism `V ⟶ U` of open subschemes which is smooth
of some relative dimension `d`; for `x' ∈ V` the open subscheme `V ∩ X_{f(x')}` of the fibre
is its base change to `κ(f(x'))`, smooth of relative dimension `d` over that field, so that
`dim_{x'} (X_{f(x')}) = d` by
`AlgebraicGeometry.topologicalKrullDimAt_eq_of_smoothOfRelativeDimension`. -/
@[stacks 02G1]
theorem Smooth.isLocallyConstant_topologicalKrullDimAt_asFiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] : IsLocallyConstant fun x : X ↦ topologicalKrullDimAt (f.asFiber x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨U, V, -, -, hx, e, d, hd⟩ := Smooth.exists_smoothOfRelativeDimension_resLE f x
  suffices ∀ x' ∈ V, topologicalKrullDimAt (f.asFiber x') = d by
    filter_upwards [V.isOpen.mem_nhds hx] with x' hx' using (this x' hx').trans (this x hx).symm
  intro x' hx'
  let W := (f.fiberι (f x')) ⁻¹ᵁ V
  have hW : f.asFiber x' ∈ W := by
    change f.fiberι _ (f.asFiber x') ∈ V
    rwa [Scheme.Hom.fiberι_asFiber]
  have : SmoothOfRelativeDimension d (V.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f e]
    have : SmoothOfRelativeDimension (d + 0) (f.resLE U V e ≫ U.ι) := inferInstance
    simpa using this
  have hpb : IsPullback (f.fiberι (f x') ∣_ V) (W.ι ≫ f.fiberToSpecResidueField (f x'))
      (V.ι ≫ f) (Y.fromSpecResidueField (f x')) :=
    (isPullback_morphismRestrict (f.fiberι (f x')) V).paste_vert (IsPullback.of_hasPullback _ _)
  have : SmoothOfRelativeDimension d (W.ι ≫ f.fiberToSpecResidueField (f x')) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    exact MorphismProperty.of_isPullback hpb inferInstance
  rw [← IsOpen.topologicalKrullDimAt_eq W.isOpen hW]
  exact @topologicalKrullDimAt_eq_of_smoothOfRelativeDimension _ _ _
    (W.ι ≫ f.fiberToSpecResidueField (f x')) d this ⟨_, hW⟩

/-- **The relative dimension of a smooth morphism is read off its fibres.** A smooth morphism
`f : X ⟶ Y` whose fibres `X_y ⟶ Spec κ(y)` are all smooth of relative dimension `n` is smooth of
relative dimension `n`. -/
theorem smoothOfRelativeDimension_of_fiberToSpecResidueField {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] (n : ℕ) (h : ∀ y, SmoothOfRelativeDimension n (f.fiberToSpecResidueField y)) :
    SmoothOfRelativeDimension n f := by
  refine smoothOfRelativeDimension_of_forall_exists_mem f n fun x ↦ ?_
  obtain ⟨U, V, -, -, hx, e, d, hd⟩ := Smooth.exists_smoothOfRelativeDimension_resLE f x
  have : SmoothOfRelativeDimension d (V.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f e]
    have : SmoothOfRelativeDimension (d + 0) (f.resLE U V e ≫ U.ι) := inferInstance
    simpa using this
  let W := (f.fiberι (f x)) ⁻¹ᵁ V
  have hW : f.asFiber x ∈ W := by
    change f.fiberι _ (f.asFiber x) ∈ V
    rwa [Scheme.Hom.fiberι_asFiber]
  have : Nonempty W := ⟨⟨_, hW⟩⟩
  have hpb : IsPullback (f.fiberι (f x) ∣_ V) (W.ι ≫ f.fiberToSpecResidueField (f x))
      (V.ι ≫ f) (Y.fromSpecResidueField (f x)) :=
    (isPullback_morphismRestrict (f.fiberι (f x)) V).paste_vert (IsPullback.of_hasPullback _ _)
  have h₁ : SmoothOfRelativeDimension d (W.ι ≫ f.fiberToSpecResidueField (f x)) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    exact MorphismProperty.of_isPullback hpb inferInstance
  have h₂ : SmoothOfRelativeDimension n (W.ι ≫ f.fiberToSpecResidueField (f x)) := by
    have := h (f x)
    have : SmoothOfRelativeDimension (0 + n) (W.ι ≫ f.fiberToSpecResidueField (f x)) :=
      inferInstance
    simpa using this
  obtain rfl := SmoothOfRelativeDimension.eq_of_field _ h₁ h₂
  exact ⟨V, hx, inferInstance⟩

/-- Over a field, the relative dimension of a smooth morphism `f : X ⟶ Spec K` can be computed
after composing with a universally closed, locally quasi-finite surjection `u : X' ⟶ X`: such
a `u` preserves the dimension of open subschemes. -/
theorem smoothOfRelativeDimension_of_comp_of_surjective_of_field {K : Type u} [Field K]
    {X' X : Scheme.{u}} (u : X' ⟶ X) (f : X ⟶ Spec (.of K)) [Smooth f] [UniversallyClosed u]
    [LocallyQuasiFinite u] [Surjective u] (n : ℕ) [SmoothOfRelativeDimension n (u ≫ f)] :
    SmoothOfRelativeDimension n f := by
  refine smoothOfRelativeDimension_of_forall_exists_mem f n fun x ↦ ?_
  obtain ⟨U, V, -, -, hx, e, d, hd⟩ := Smooth.exists_smoothOfRelativeDimension_resLE f x
  have : SmoothOfRelativeDimension d (V.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f e]
    have : SmoothOfRelativeDimension (d + 0) (f.resLE U V e ≫ U.ι) := inferInstance
    simpa using this
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  obtain ⟨x', hx'⟩ := u.surjective x
  have : Nonempty (u ⁻¹ᵁ V) := ⟨⟨x', by simpa [hx'] using hx⟩⟩
  have : SmoothOfRelativeDimension n ((u ⁻¹ᵁ V).ι ≫ u ≫ f) := by
    have : SmoothOfRelativeDimension (0 + n) ((u ⁻¹ᵁ V).ι ≫ u ≫ f) := inferInstance
    simpa using this
  have : Surjective (u ∣_ V) :=
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_morphismRestrict u V).flip ‹_›
  have h := (u ∣_ V).topologicalKrullDim_eq_of_surjective
  rw [topologicalKrullDim_eq_of_smoothOfRelativeDimension ((u ⁻¹ᵁ V).ι ≫ u ≫ f) n,
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (V.ι ≫ f) d] at h
  obtain rfl : n = d := by exact_mod_cast h
  exact ⟨V, hx, inferInstance⟩

/-- Let `V` be an affine open of a scheme `X` and `R → Γ(X, V)` an étale ring map from a regular
ring `R`. Then the local rings of `X` at the points of `V` are regular: they are localizations of
`Γ(X, V)` at primes (`IsRegularLocalRing.localization_of_etale`). -/
theorem IsAffineOpen.isRegularLocalRing_stalk_of_etale {X : Scheme.{u}} {R : Type u}
    [CommRing R] [IsRegularRing R] {V : X.Opens} (hV : IsAffineOpen V) (φ : R →+* Γ(X, V))
    (hφ : φ.Etale) (x : X) (hx : x ∈ V) : IsRegularLocalRing (X.presheaf.stalk x) := by
  algebraize [φ]
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  have := IsRegularLocalRing.localization_of_etale (R := R) (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  exact .of_ringEquiv (IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv

/-- The local rings of a scheme smooth over a field `k` are regular local rings: near any point
the scheme is étale over an affine space `𝔸ⁿ_k`, whose local rings are regular, and étale maps
preserve regularity. -/
theorem Smooth.isRegularLocalRing_stalk {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, V, -, -, hx, e, d, hd⟩ := Smooth.exists_smoothOfRelativeDimension_resLE f x
  have : SmoothOfRelativeDimension d (V.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f e]
    exact smoothOfRelativeDimension_comp (n := d) (m := 0) _ _
  obtain ⟨W, hW, hxW, φ, hφ⟩ :=
    SmoothOfRelativeDimension.exists_etale_mvPolynomial_of_field (V.ι ≫ f) d ⟨x, hx⟩
  have := hW.isRegularLocalRing_stalk_of_etale φ hφ _ hxW
  exact .of_ringEquiv (V.stalkIso ⟨x, hx⟩).commRingCatIsoToRingEquiv

/-- Over an algebraically closed field `K`, a scheme locally of finite type over `K` is smooth at
every closed point whose local ring is regular. -/
theorem Scheme.Hom.mem_smoothLocus_of_isRegularLocalRing {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {x : X} (hx : IsClosed {x})
    [IsRegularLocalRing (X.presheaf.stalk x)] : x ∈ f.smoothLocus := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen (⊤ : (Spec (.of K)).Opens) := isAffineOpen_top _
  have hVU : V ≤ f ⁻¹ᵁ ⊤ := le_top
  have hft := f.finiteType_appLE hU hV hVU
  algebraize [(f.appLE ⊤ V hVU).hom]
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff ⊤ hU V hV hVU hxV]
  set q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : q.IsMaximal := hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx
  have : IsRegularLocalRing (Localization.AtPrime q) := by
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
    have := hV.isLocalization_stalk ⟨x, hxV⟩
    exact .of_ringEquiv (IsLocalization.algEquiv q.primeCompl (X.presheaf.stalk x)
      (Localization.AtPrime q)).toRingEquiv
  let e : K ≃+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  let : Algebra K Γ(X, V) := ((f.appLE ⊤ V hVU).hom.comp e.toRingHom).toAlgebra
  have : Algebra.FiniteType K Γ(X, V) :=
    RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _ e.surjective)
  have h : Algebra.FormallySmooth K (Localization.AtPrime q) :=
    Algebra.IsSmoothAt.of_isRegularLocalRing_of_isAlgClosed (k := K) q
  change Algebra.FormallySmooth Γ(Spec (.of K), ⊤) (Localization.AtPrime q)
  rw [← RingHom.formallySmooth_algebraMap] at h ⊢
  have heq : algebraMap K (Localization.AtPrime q) =
      (algebraMap Γ(Spec (.of K), ⊤) (Localization.AtPrime q)).comp e.toRingHom := by
    rw [IsScalarTower.algebraMap_eq K Γ(X, V), IsScalarTower.algebraMap_eq Γ(Spec (.of K), ⊤)
      Γ(X, V)]
    rfl
  rw [heq] at h
  have := RingHom.FormallySmooth.respectsIso.2 _ e.symm h
  convert this using 1
  refine RingHom.ext fun a ↦ ?_
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply]

open Limits in
/-- **Smoothness over a field descends along flat surjections** (Stacks, Tag 05AX). Let
`u : X' ⟶ X` be flat and surjective, and let `f : X ⟶ Spec K` be locally of finite type. If
`u ≫ f` is smooth, then so is `f`.

After base change to an algebraic closure of `K` (smoothness descends along the fpqc covering
`Spec K̄ ⟶ Spec K`), it suffices to show that `f` is smooth at the closed points, as the smooth
locus is open and `X` is a Jacobson space. At a closed point `x = u x'`, the local ring `𝒪_{X,x}`
is regular since `𝒪_{X,x} ⟶ 𝒪_{X',x'}` is a flat local homomorphism and `𝒪_{X',x'}` is regular
(`IsRegularLocalRing.of_flat`), and a regular point with residue field `K` is smooth. -/
@[stacks 05AX]
theorem Smooth.of_comp_of_flat_of_surjective_of_field {K : Type u} [Field K] {X' X : Scheme.{u}}
    (u : X' ⟶ X) (f : X ⟶ Spec (.of K)) [Flat u] [Surjective u] [LocallyOfFiniteType f]
    [Smooth (u ≫ f)] : Smooth f := by
  wlog hK : IsAlgClosed K generalizing K X X' with H
  · let g : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
    have h₁ : Smooth (pullback.snd (u ≫ f) g) := MorphismProperty.pullback_snd _ _ ‹_›
    have : Smooth (pullback.snd u (pullback.fst f g) ≫ pullback.snd f g) := by
      rw [← pullbackRightPullbackFstIso_hom_snd]
      have h₂ : Smooth (pullbackRightPullbackFstIso f g u).hom := inferInstance
      exact MorphismProperty.comp_mem _ _ _ h₂ h₁
    have hsnd := H (pullback.snd u (pullback.fst f g)) (pullback.snd f g)
      (AlgebraicClosure.isAlgClosed K)
    have : Surjective g := ⟨fun _ ↦ ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
    have : Flat g := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact RingHom.flat_algebraMap_iff.2 inferInstance
    exact MorphismProperty.of_pullback_snd_of_descendsAlong
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨⟨‹_›, ‹_›⟩, inferInstance⟩ hsnd
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  rw [← f.smoothLocus_eq_top_iff]
  by_contra hne
  obtain ⟨x, hxZ, hx⟩ := nonempty_inter_closedPoints (Z := (f.smoothLocus : Set X)ᶜ)
    (Set.nonempty_compl.2 fun h ↦ hne (TopologicalSpace.Opens.ext
      (h.trans TopologicalSpace.Opens.coe_top.symm)))
    f.smoothLocus.isOpen.isClosed_compl.isLocallyClosed
  obtain ⟨x', rfl⟩ := u.surjective x
  have : IsRegularLocalRing (X'.presheaf.stalk x') := Smooth.isRegularLocalRing_stalk (u ≫ f) x'
  have : IsRegularLocalRing (X.presheaf.stalk (u x')) := by
    let := (u.stalkMap x').hom.toAlgebra
    have : IsLocalHom (algebraMap (X.presheaf.stalk (u x')) (X'.presheaf.stalk x')) :=
      inferInstanceAs (IsLocalHom (u.stalkMap x').hom)
    have : Module.Flat (X.presheaf.stalk (u x')) (X'.presheaf.stalk x') := Flat.stalkMap u x'
    exact IsRegularLocalRing.of_flat (S := X'.presheaf.stalk x')
  exact hxZ (f.mem_smoothLocus_of_isRegularLocalRing hx)

open Limits in
/-- **Smoothness descends along flat surjections** (Stacks, Tag 05B5). Let `u : X' ⟶ X` be
flat, surjective and locally of finite presentation, and let `f : X ⟶ S`. If `u ≫ f` is smooth,
then so is `f`: the morphism `f` is flat and locally of finite presentation by descent, and its
fibres are smooth by `AlgebraicGeometry.Smooth.of_comp_of_flat_of_surjective_of_field` applied
to the base change of `u` to the fibres. -/
@[stacks 05B5]
theorem Smooth.of_comp_of_flat_of_surjective {X' X S : Scheme.{u}} (u : X' ⟶ X) (f : X ⟶ S)
    [Flat u] [Surjective u] [LocallyOfFinitePresentation u] [Smooth (u ≫ f)] : Smooth f := by
  have : LocallyOfFinitePresentation f := .of_comp_of_flat_of_surjective u f
  have : Flat f := Flat.of_comp_of_flat_of_surjective u f
  refine Smooth.of_smooth_fiberToSpecResidueField f fun s ↦ ?_
  let g := S.fromSpecResidueField s
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f g))
  have : Smooth (pullback.snd u (pullback.fst f g) ≫ f.fiberToSpecResidueField s) := by
    change Smooth (pullback.snd u (pullback.fst f g) ≫ pullback.snd f g)
    rw [← pullbackRightPullbackFstIso_hom_snd]
    infer_instance
  exact Smooth.of_comp_of_flat_of_surjective_of_field (pullback.snd u (pullback.fst f g)) _

open Limits in
/-- **Smoothness descends along finite locally free surjections.** Let `u : X' ⟶ X` be finite,
flat, locally of finite presentation and surjective, and let `f : X ⟶ S`. If `u ≫ f` is smooth of
relative dimension `n`, then so is `f`.

Smoothness descends along flat surjective morphisms locally of finite presentation (Stacks, Tag
05B5), and the relative dimension is preserved since `u` is finite flat surjective, so that
fibres of `u ≫ f` and of `f` have the same local dimensions. -/
theorem smoothOfRelativeDimension_of_comp_of_isFinite_of_surjective {X' X S : Scheme.{u}}
    (u : X' ⟶ X) (f : X ⟶ S) [IsFinite u] [Flat u] [LocallyOfFinitePresentation u]
    [Surjective u] (n : ℕ) [SmoothOfRelativeDimension n (u ≫ f)] :
    SmoothOfRelativeDimension n f := by
  have : Smooth (u ≫ f) := SmoothOfRelativeDimension.smooth n _
  have : Smooth f := Smooth.of_comp_of_flat_of_surjective u f
  refine smoothOfRelativeDimension_of_fiberToSpecResidueField f n fun s ↦ ?_
  let g := S.fromSpecResidueField s
  have : Smooth (f.fiberToSpecResidueField s) := inferInstanceAs (Smooth (pullback.snd f g))
  have : SmoothOfRelativeDimension n
      (pullback.snd u (pullback.fst f g) ≫ f.fiberToSpecResidueField s) := by
    change SmoothOfRelativeDimension n (pullback.snd u (pullback.fst f g) ≫ pullback.snd f g)
    rw [← pullbackRightPullbackFstIso_hom_snd]
    have : SmoothOfRelativeDimension (0 + n)
        ((pullbackRightPullbackFstIso f g u).hom ≫ pullback.snd (u ≫ f) g) := inferInstance
    simpa using this
  exact smoothOfRelativeDimension_of_comp_of_surjective_of_field
    (pullback.snd u (pullback.fst f g)) (f.fiberToSpecResidueField s) n

end AlgebraicGeometry
