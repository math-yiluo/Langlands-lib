/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import WeilConjectures.AlgebraicGeometry.Cohomology.DualityPairing
public import WeilConjectures.AlgebraicGeometry.Modules.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Resolution
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import WeilConjectures.AlgebraicGeometry.Modules.Ext
public import WeilConjectures.AlgebraicGeometry.Modules.Linear
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Serre duality on the projective line

Let `k` be a field, `ℙ¹_k = ProjectiveLine (Spec k)` and `ω = Ω¹_{ℙ¹_k/k}`. Every coherent
`𝒪_{ℙ¹}`-module `𝒢` has a resolution `0 → ℰ₂ → ℰ₁ → ℰ₀ → 𝒢 → 0` by finite direct sums of twists
`𝒪(d)`, and the two duality isomorphisms
`H¹(ℙ¹, 𝒢)^∨ ≅ Hom(𝒢, ω)` and `H⁰(ℙ¹, 𝒢)^∨ ≅ Ext¹(𝒢, ω)` hold.

## Main statements

- `AlgebraicGeometry.ProjectiveLine.exists_exact_sigma_twist`: resolutions by twists.
- `AlgebraicGeometry.ProjectiveLine.bijective_dualPairing_twist`: the duality pairing
  `Hom(𝒪(a), ω) → H¹(ℙ¹, 𝒪(a))^∨` is bijective.
- `AlgebraicGeometry.ProjectiveLine.bijective_dualPairing_of_isCoherent`: the duality pairing
  `Hom(𝒢, ω) → H¹(ℙ¹, 𝒢)^∨` is bijective for coherent `𝒢`.
- `AlgebraicGeometry.ProjectiveLine.nonempty_dual_H_one_iso`: `H¹(ℙ¹, 𝒢)^∨ ≅ Hom(𝒢, ω)`,
  naturally in coherent `𝒢`.
- `AlgebraicGeometry.Scheme.Modules.yonedaDualMap`: the Yoneda pairing
  `Ext¹(𝒢, ω) → H⁰(X, 𝒢)^∨`, `ξ ↦ (s ↦ t (s ∘ ξ))`, through `Ext¹(𝒪_X, ω) ≅ H¹(X, ω)`; it is
  natural in `𝒢` (`AlgebraicGeometry.Scheme.Modules.yonedaDualMap_naturality`).
- `AlgebraicGeometry.Scheme.Modules.bijective_yonedaDualMap_of_shortExact`: it is bijective on
  `𝒢` given a resolution `0 → 𝒦 → ℰ → 𝒢 → 0` on which the `H¹`-duality pairing is known.
- `AlgebraicGeometry.ProjectiveLine.bijective_yonedaDualMap`: it is bijective on `ℙ¹_k` for
  coherent `𝒢`.
- `AlgebraicGeometry.ProjectiveLine.extIsoDualHZero` and
  `AlgebraicGeometry.ProjectiveLine.nonempty_dual_H_zero_iso_ext`: `H⁰(ℙ¹, 𝒢)^∨ ≅ Ext¹(𝒢, ω)`,
  naturally in coherent `𝒢`, by the inverse of the Yoneda pairing.
- `AlgebraicGeometry.ProjectiveLine.dualHZeroLinearEquivExt`: the same for one `𝒢`.

## Implementation notes

Coherence is spelled as `AlgebraicGeometry.Scheme.Modules.isCoherent`. The `𝒪_{ℙ¹}`-module
`Hom(𝒢, ω)` of global homomorphisms is written as `H⁰(ℙ¹, Hom(𝒢, ω))`, the global sections of the
internal hom, so that it is a functor to `k`-vector spaces.

The resolutions by twists come from Castelnuovo–Mumford regularity
(`exists_shortExact_sigma_twist`), which gives them with `ℰ₂ = 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry

open Scheme.Modules

namespace ProjectiveSpace

variable (n : Type u) (S : Scheme.{u})

/-- **The dual of a twist.** `𝒪(a)ᵛ ≅ 𝒪(-a)` on `ℙ(n; S)`: both are tensor inverses of the
invertible module `𝒪(a)`. -/
theorem nonempty_dual_twist_iso (a : ℤ) : Nonempty ((twist n S a)ᵛ ≅ twist n S (-a)) := by
  obtain ⟨e⟩ := nonempty_tensorObj_twist_iso n S (-a) a
  obtain ⟨d⟩ := nonempty_tensorObj_dual_iso_unit (twist n S a)
  let e' : twist n S (-a) ⊗ twist n S a ≅ 𝟙_ _ :=
    e ≪≫ eqToIso (by rw [neg_add_cancel]) ≪≫ (unitIsoTwistZero n S).symm
  exact ⟨(λ_ _).symm ≪≫ whiskerRightIso e'.symm _ ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso _ d ≪≫ ρ_ _⟩

end ProjectiveSpace

namespace Scheme.Modules

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [HasExt.{u} X.Modules]
  {ω : X.Modules} (t : Module.Dual k (ω.H 1))

omit [HasExt X.Modules] in
/-- The duality pairing is `k`-linear, for the `k`-linear structure of `X.Modules`. -/
lemma dualPairing_smul (G : X.Modules) (c : k) (φ : G ⟶ ω) :
    dualPairing t G (c • φ) = c • dualPairing t G φ := by
  refine LinearMap.ext fun x ↦ ?_
  rw [dualPairing_apply, H.map_smul_hom, t.map_smul, LinearMap.smul_apply, dualPairing_apply]

omit [HasExt X.Modules] in
/-- The duality pairing `Hom(G, ω) → H¹(X, G)^∨`, `φ ↦ t ∘ H¹(φ)`, as a `k`-linear map. -/
@[simps]
noncomputable def dualPairingLinearMap (G : X.Modules) :
    (G ⟶ ω) →ₗ[k] Module.Dual k (G.H 1) where
  toFun := dualPairing t G
  map_add' := map_add _
  map_smul' := dualPairing_smul t G

/-- The comparison `Ext^n_X(𝒪_X, M) ≅ H^n(X, M)` of `extUnitAddEquivH` is `k`-linear. -/
lemma extUnitAddEquivH_smul (M : X.Modules) (n : ℕ) (c : k) (x : Ext (𝟙_ X.Modules) M n) :
    extUnitAddEquivH M n (c • x) = c • extUnitAddEquivH M n x := by
  rw [Abelian.Ext.smul_eq_comp_mk₀, extUnitAddEquivH_comp_mk₀, H.map_smul_hom, H.map_id_apply]

variable (k) in
/-- **`Ext` from the structure sheaf is sheaf cohomology, `k`-linearly**: the comparison
isomorphism `extUnitAddEquivH : Ext^n_X(𝒪_X, M) ≅ H^n(X, M)` as a `k`-linear equivalence. -/
noncomputable def extUnitLinearEquivH (M : X.Modules) (n : ℕ) :
    Ext (𝟙_ X.Modules) M n ≃ₗ[k] M.H n where
  __ := extUnitAddEquivH M n
  map_smul' := extUnitAddEquivH_smul M n

@[simp]
lemma extUnitLinearEquivH_apply (M : X.Modules) (n : ℕ) (x : Ext (𝟙_ X.Modules) M n) :
    extUnitLinearEquivH k M n x = extUnitAddEquivH M n x :=
  rfl

/-- **The Yoneda pairing** `Ext¹(𝒢, ω) × H⁰(X, 𝒢) → k`, as the `k`-linear map
`Ext¹(𝒢, ω) → H⁰(X, 𝒢)^∨`. A class `s ∈ H⁰(X, 𝒢) ≅ Hom(𝒪_X, 𝒢) = Ext⁰(𝒪_X, 𝒢)` and
`ξ ∈ Ext¹(𝒢, ω)` compose to the Yoneda product `s ∘ ξ ∈ Ext¹(𝒪_X, ω) ≅ H¹(X, ω)`
(`extUnitAddEquivH`), which `t: H¹(X, ω) → k` evaluates (`yonedaDualMap_apply`). It is natural
in `𝒢` (`yonedaDualMap_naturality`). -/
noncomputable def yonedaDualMap (G : X.Modules) : Ext G ω 1 →ₗ[k] Module.Dual k (G.H 0) :=
  (((Abelian.Ext.bilinearCompOfLinear k (𝟙_ X.Modules) G ω 0 1 1 (zero_add 1)).compr₂
      (t ∘ₗ (extUnitLinearEquivH k ω 1).toLinearMap)).comp
    (extUnitLinearEquivH k G 0).symm.toLinearMap).flip

lemma yonedaDualMap_apply (G : X.Modules) (ξ : Ext G ω 1) (s : G.H 0) :
    yonedaDualMap t G ξ s =
      t (extUnitAddEquivH ω 1 (((extUnitAddEquivH G 0).symm s).comp ξ (zero_add 1))) :=
  rfl

/-- **Naturality of the Yoneda pairing**: for `f : 𝒢 ⟶ 𝒢'`, the square formed by
`f^* : Ext¹(𝒢', ω) → Ext¹(𝒢, ω)` and the transpose of `H⁰(f)` commutes. -/
lemma yonedaDualMap_naturality {G G' : X.Modules} (f : G ⟶ G') (ξ : Ext G' ω 1) :
    yonedaDualMap t G ((Abelian.Ext.mk₀ f).comp ξ (zero_add 1)) =
      yonedaDualMap t G' ξ ∘ₗ H.mapLinearMap k f 0 := by
  refine LinearMap.ext fun s ↦ ?_
  have h : (extUnitAddEquivH G' 0).symm (H.map f 0 s) =
      ((extUnitAddEquivH G 0).symm s).comp (Abelian.Ext.mk₀ f) (add_zero 0) := by
    rw [AddEquiv.symm_apply_eq, extUnitAddEquivH_comp_mk₀, AddEquiv.apply_symm_apply]
  rw [LinearMap.comp_apply, yonedaDualMap_apply, yonedaDualMap_apply, H.mapLinearMap_apply, h,
    Abelian.Ext.comp_assoc_of_second_deg_zero]

variable (k ω) in
/-- `𝒢 ↦ Extⁿ(𝒢, ω)`, as a contravariant functor to `k`-vector spaces. -/
@[simps]
noncomputable def extLinearFunctor (n : ℕ) : X.Modulesᵒᵖ ⥤ ModuleCat.{u} k where
  obj G := ModuleCat.of k (Ext G.unop ω n)
  map f := ModuleCat.ofHom
    (Abelian.Ext.precompOfLinear (Abelian.Ext.mk₀ f.unop) k ω (zero_add n))
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun x ↦ Abelian.Ext.mk₀_id_comp x)
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun x ↦
    (Abelian.Ext.mk₀_comp_mk₀_assoc g.unop f.unop x).symm)

/-- **`H⁰`-duality from a resolution.** Let `0 → 𝒦 → ℰ → 𝒢 → 0` be a short exact sequence of
`𝒪_X`-modules with `H⁰(ℰ) = 0` and `Ext¹(ℰ, ω) = 0`, such that the duality pairing
`Hom(-, ω) → H¹(X, -)^∨` is bijective on `𝒦` and surjective on `ℰ`. Then the Yoneda pairing
`Ext¹(𝒢, ω) → H⁰(X, 𝒢)^∨` is bijective. -/
theorem bijective_yonedaDualMap_of_shortExact {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [Subsingleton (S.X₂.H 0)] [Subsingleton (Ext S.X₂ ω 1)]
    (h₁ : Function.Bijective (dualPairing t S.X₁))
    (h₂ : Function.Surjective (dualPairing t S.X₂)) :
    Function.Bijective (yonedaDualMap t S.X₃) := by
  let δ := H.δLinearMap k hS 0
  have hδ : Function.Injective δ := by
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    obtain ⟨y, rfl⟩ := (H.ker_δ_eq_range_map_g hS 0).le hx
    rw [Subsingleton.elim y 0, map_zero]
  have hfδ (x : S.X₃.H 0) : H.map S.f 1 (δ x) = 0 :=
    (H.ker_map_f_eq_range_δ hS 0).ge ⟨x, rfl⟩
  let Ψ : Ext S.X₁ ω 0 →ₗ[k] Module.Dual k (S.X₃.H 0) :=
    δ.dualMap ∘ₗ dualPairingLinearMap t S.X₁ ∘ₗ (Abelian.Ext.linearEquiv₀ (R := k)).toLinearMap
  let D : Ext S.X₁ ω 0 →ₗ[k] Ext S.X₃ ω 1 :=
    Abelian.Ext.precompOfLinear hS.extClass k ω (add_zero 1)
  have hΨφ (φ : S.X₁ ⟶ ω) :
      Ψ (Abelian.Ext.mk₀ φ) = δ.dualMap (dualPairing t S.X₁ φ) := by
    change δ.dualMap (dualPairing t S.X₁ (Abelian.Ext.addEquiv₀
      (Abelian.Ext.addEquiv₀.symm φ))) = _
    rw [AddEquiv.apply_symm_apply]
  have hD : Function.Surjective D := fun x ↦
    Abelian.Ext.contravariant_sequence_exact₃ hS ω x (Subsingleton.elim _ _) (add_zero 1)
  have hΨ : Function.Surjective Ψ := fun ν ↦ by
    obtain ⟨μ, rfl⟩ := LinearMap.dualMap_surjective_of_injective hδ ν
    obtain ⟨φ, hφ⟩ := h₁.2 μ
    exact ⟨Abelian.Ext.mk₀ φ, by rw [hΨφ, hφ]⟩
  have hker : LinearMap.ker D = LinearMap.ker Ψ := by
    ext x
    obtain ⟨φ, rfl⟩ := Abelian.Ext.addEquiv₀.symm.surjective x
    simp only [LinearMap.mem_ker]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS ω _ (add_zero 1) hx
      obtain ⟨ψ, rfl⟩ := Abelian.Ext.addEquiv₀.symm.surjective y
      have : φ = S.f ≫ ψ := by
        apply Abelian.Ext.addEquiv₀.symm.injective
        rw [← hy]
        exact Abelian.Ext.mk₀_comp_mk₀ _ _
      subst this
      change Ψ (Abelian.Ext.mk₀ (S.f ≫ ψ)) = 0
      rw [hΨφ, dualPairing_comp]
      refine LinearMap.ext fun x ↦ ?_
      change dualPairing t S.X₂ ψ (H.map S.f 1 (δ x)) = 0
      rw [hfδ, map_zero]
    · intro hx
      change Ψ (Abelian.Ext.mk₀ φ) = 0 at hx
      rw [hΨφ] at hx
      have hl : dualPairing t S.X₁ φ ∈
          (LinearMap.ker (H.mapLinearMap k S.f 1)).dualAnnihilator := by
        rw [Submodule.mem_dualAnnihilator]
        intro v hv
        obtain ⟨w, rfl⟩ := (H.ker_map_f_eq_range_δ hS 0).le hv
        exact LinearMap.congr_fun hx w
      rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hl
      obtain ⟨μ, hμ⟩ := hl
      obtain ⟨ψ, rfl⟩ := h₂ μ
      have : φ = S.f ≫ ψ := h₁.1 (by rw [dualPairing_comp]; exact hμ.symm)
      subst this
      change hS.extClass.comp (Abelian.Ext.mk₀ (S.f ≫ ψ)) (add_zero 1) = 0
      rw [← Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.comp_assoc_of_second_deg_zero,
        hS.extClass_comp, Abelian.Ext.zero_comp]
  -- the Yoneda pairing of `φ ∘ e` with `s` is `t (H¹(φ) (δ s))`
  have hYD (x : Ext S.X₁ ω 0) : yonedaDualMap t S.X₃ (D x) = Ψ x := by
    obtain ⟨φ, rfl⟩ := (Abelian.Ext.mk₀_bijective S.X₁ ω).2 x
    rw [hΨφ]
    refine LinearMap.ext fun s ↦ ?_
    let α := (extUnitAddEquivH S.X₃ 0).symm s
    have key : extUnitAddEquivH S.X₁ 1 (α.comp hS.extClass (zero_add 1)) =
        H.δ hS 0 (extUnitAddEquivH S.X₃ 0 α) :=
      extUnitToH_comp_extClass hS α
    change t (extUnitAddEquivH ω 1 (α.comp (hS.extClass.comp (Abelian.Ext.mk₀ φ) (add_zero 1))
      (zero_add 1))) = t (H.map φ 1 (δ s))
    rw [← Abelian.Ext.comp_assoc_of_third_deg_zero, extUnitAddEquivH_comp_mk₀, key,
      AddEquiv.apply_symm_apply]
    rfl
  refine ⟨fun x y hxy ↦ ?_, fun ν ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := hD x
    obtain ⟨y, rfl⟩ := hD y
    rw [hYD, hYD] at hxy
    have h : x - y ∈ LinearMap.ker Ψ := by rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
    rw [← hker, LinearMap.mem_ker, map_sub, sub_eq_zero] at h
    exact h
  · obtain ⟨x, rfl⟩ := hΨ ν
    exact ⟨D x, hYD x⟩

/-- **`H⁰`-duality from a resolution.** Let `0 → 𝒦 → ℰ → 𝒢 → 0` be a short exact sequence of
`𝒪_X`-modules with `H⁰(ℰ) = 0` and `Ext¹(ℰ, ω) = 0`, such that the duality pairing
`Hom(-, ω) → H¹(X, -)^∨` is bijective on `𝒦` and surjective on `ℰ`. Then
`H⁰(X, 𝒢)^∨ ≅ Ext¹(𝒢, ω)`, by the inverse of the Yoneda pairing
(`bijective_yonedaDualMap_of_shortExact`). -/
lemma nonempty_dual_H_zero_addEquiv_ext_of_shortExact {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [Subsingleton (S.X₂.H 0)] [Subsingleton (Ext S.X₂ ω 1)]
    (h₁ : Function.Bijective (dualPairing t S.X₁))
    (h₂ : Function.Surjective (dualPairing t S.X₂)) :
    Nonempty (Module.Dual k (S.X₃.H 0) ≃+ Ext S.X₃ ω 1) :=
  ⟨(LinearEquiv.ofBijective _ (bijective_yonedaDualMap_of_shortExact t hS h₁ h₂)).symm.toAddEquiv⟩

/-- **`H⁰`-duality from a resolution, `k`-linearly.** Let `0 → 𝒦 → ℰ → 𝒢 → 0` be a short exact
sequence of `𝒪_X`-modules with `H⁰(ℰ) = 0` and `Ext¹(ℰ, ω) = 0`, such that the duality pairing
`Hom(-, ω) → H¹(X, -)^∨` is bijective on `𝒦` and surjective on `ℰ`. Then
`H⁰(X, 𝒢)^∨ ≅ Ext¹(𝒢, ω)` as `k`-vector spaces, for the `k`-linear structure of `X.Modules`
(`Scheme.Modules.linearOfOver`), by the inverse of the Yoneda pairing
(`bijective_yonedaDualMap_of_shortExact`). -/
lemma nonempty_dual_H_zero_linearEquiv_ext_of_shortExact {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [Subsingleton (S.X₂.H 0)] [Subsingleton (Ext S.X₂ ω 1)]
    (h₁ : Function.Bijective (dualPairing t S.X₁))
    (h₂ : Function.Surjective (dualPairing t S.X₂)) :
    Nonempty (Module.Dual k (S.X₃.H 0) ≃ₗ[k] Ext S.X₃ ω 1) :=
  ⟨(LinearEquiv.ofBijective _ (bijective_yonedaDualMap_of_shortExact t hS h₁ h₂)).symm⟩

end Scheme.Modules

namespace ProjectiveLine

variable (k : Type u) [Field k]

/-- **Resolutions by twists on `ℙ¹_k`.** Every coherent `𝒪_{ℙ¹_k}`-module `𝒢` has a resolution
`0 → ℰ₂ → ℰ₁ → ℰ₀ → 𝒢 → 0` in which each `ℰᵢ` is a finite direct sum of twists `𝒪(d)`. -/
theorem exists_exact_sigma_twist (𝒢 : (ProjectiveLine (Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢]
    [SheafOfModules.IsFinitePresentation (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢] :
    let 𝒪 : ℤ → (ProjectiveLine (Spec (.of k))).Modules :=
      ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k))
    ∃ (n₀ n₁ n₂ : ℕ) (d₀ : Fin n₀ → ℤ) (d₁ : Fin n₁ → ℤ) (d₂ : Fin n₂ → ℤ)
      (f₂ : ∐ (fun j ↦ 𝒪 (d₂ j)) ⟶ ∐ (fun j ↦ 𝒪 (d₁ j)))
      (f₁ : ∐ (fun j ↦ 𝒪 (d₁ j)) ⟶ ∐ (fun j ↦ 𝒪 (d₀ j)))
      (f₀ : ∐ (fun j ↦ 𝒪 (d₀ j)) ⟶ 𝒢),
      Mono f₂ ∧ Epi f₀ ∧ (ComposableArrows.mk₃ f₂ f₁ f₀).Exact := by
  intro 𝒪
  obtain ⟨J₁, J₀, _, _, d₁, d₀, f, g, w, hS⟩ := exists_shortExact_sigma_twist 𝒢
  let ε₁ := (Finite.equivFin J₁).symm
  let ε₀ := (Finite.equivFin J₀).symm
  have hS' := shortExact_of_isos hS (Sigma.reindex ε₁ fun _ ↦ 𝒪 d₁).symm
    (Sigma.reindex ε₀ fun _ ↦ 𝒪 d₀).symm (Iso.refl 𝒢)
  have hz : IsZero (∐ fun j : Fin 0 ↦ 𝒪 (Fin.elim0 j)) :=
    (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun j ↦ j.elim0)
  refine ⟨_, _, 0, fun _ ↦ d₀, fun _ ↦ d₁, Fin.elim0, 0, _, _, ⟨fun g h _ ↦ hz.eq_of_tgt g h⟩,
    hS'.epi_g, ComposableArrows.exact_of_δ₀ (ComposableArrows.exact₂_mk _ (zero_comp) ?_)
      (ComposableArrows.exact₂_mk _ _ hS'.exact)⟩
  have := hS'.mono_f
  exact (ShortComplex.exact_iff_mono _ rfl).2 this

/-- `Hom(𝒪(a), Ω¹_{ℙ¹_k/k}) ≅ 𝒪(-a - 2)`, since `Ω¹_{ℙ¹_k/k} ≅ 𝒪(-2)` is invertible and
`𝒪(a)ᵛ ≅ 𝒪(-a)`. -/
theorem nonempty_homObj_twist_iso (a : ℤ) :
    Nonempty (homObj (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) a)
        (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials ≅
      ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) (-a + -2)) := by
  obtain ⟨eω⟩ := nonempty_relativeDifferentials_iso_twist k
  have : (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials.IsInvertible :=
    IsInvertible.of_iso eω.symm
  obtain ⟨ed⟩ := ProjectiveSpace.nonempty_dual_twist_iso (ULift.{u} (Fin 2)) (Spec (.of k)) a
  obtain ⟨et⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso (ULift.{u} (Fin 2)) (Spec (.of k))
    (-a) (-2)
  exact ⟨(asIso (dualTensorHom _ _)).symm ≪≫ (ed ⊗ᵢ eω) ≪≫ et⟩

local notation3 "𝒪(" a ")" => ProjectiveSpace.twist (ULift (Fin 2)) (Spec (CommRingCat.of k)) a

local notation3 "ω" =>
  Scheme.Hom.relativeDifferentials (ProjectiveLine (Spec (CommRingCat.of k)) ↘
    Spec (CommRingCat.of k))

lemma finiteDimensional_homogeneousSubmodule (d : ℕ) :
    FiniteDimensional k (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) k d) :=
  Module.Finite.iff_fg.2 (MvPolynomial.homogeneousSubmodule_fg _ _ d)

lemma finrank_homogeneousSubmodule_zero :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) k 0) = 1 := by
  rw [Module.finrank_eq_nat_card_basis (ProjectiveSpace.homogeneousSubmoduleBasis _ k 0)]
  have : Unique {s : ULift.{u} (Fin 2) →₀ ℕ | s.degree = 0} :=
    ⟨⟨⟨0, by simp⟩⟩, fun s ↦ Subtype.ext ((Finsupp.degree_eq_zero_iff _).1 s.2)⟩
  exact Nat.card_unique

lemma finiteDimensional_H_zero_twist (b : ℤ) : FiniteDimensional k ((𝒪(b)).H 0) := by
  rcases lt_or_ge b 0 with hb | hb
  · have := subsingleton_H_zero_twist_of_neg k b hb
    infer_instance
  · rw [← Int.toNat_of_nonneg hb]
    obtain ⟨e⟩ := nonempty_H_zero_twist_equiv k b.toNat
    have := finiteDimensional_homogeneousSubmodule k b.toNat
    exact e.symm.finiteDimensional

lemma finiteDimensional_H_one_twist (a : ℤ) : FiniteDimensional k ((𝒪(a)).H 1) := by
  rcases lt_or_ge a (-1) with ha | ha
  · obtain ⟨e⟩ := nonempty_H_one_twist_equiv_dual k a (by omega)
    have := finiteDimensional_homogeneousSubmodule k (-a - 2).toNat
    exact e.symm.finiteDimensional
  · have := subsingleton_H_one_twist k a ha
    infer_instance

/-- `H⁰(ℙ¹_k, Hom(𝒪(a), Ω¹)) ≅ H⁰(ℙ¹_k, 𝒪(-a - 2))`. -/
noncomputable def homObjTwistHZeroLinearEquiv (a : ℤ) :
    H (homObj (𝒪(a)) ω) 0 ≃ₗ[k] (𝒪(-a + -2)).H 0 :=
  ((cohomologyFunctor k 0).mapIso (nonempty_homObj_twist_iso k a).some).toLinearEquiv

/-- **The dimension count for the twists.** `H⁰(ℙ¹_k, Hom(𝒪(a), Ω¹))` and `H¹(ℙ¹_k, 𝒪(a))^∨`
have the same dimension, `max(0, -a - 1)`. -/
lemma finrank_H_zero_homObj_twist (a : ℤ) :
    Module.finrank k (H (homObj (𝒪(a)) ω) 0) = Module.finrank k (Module.Dual k ((𝒪(a)).H 1)) := by
  have := finiteDimensional_H_one_twist k a
  rw [(homObjTwistHZeroLinearEquiv k a).finrank_eq, Subspace.dual_finrank_eq]
  rcases lt_or_ge a (-1) with ha | ha
  · obtain ⟨e⟩ := nonempty_H_one_twist_equiv_dual k a (by omega)
    have := finiteDimensional_homogeneousSubmodule k (-a - 2).toNat
    rw [e.finrank_eq, Subspace.dual_finrank_eq]
    have hb : -a + -2 = (((-a - 2).toNat : ℕ) : ℤ) := by omega
    rw [hb]
    obtain ⟨e'⟩ := nonempty_H_zero_twist_equiv k (-a - 2).toNat
    exact e'.finrank_eq
  · have := subsingleton_H_one_twist k a ha
    have := subsingleton_H_zero_twist_of_neg k (-a + -2) (by omega)
    rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]

/-- For the twists, surjectivity of the duality pairing implies bijectivity, by the dimension
count `finrank_H_zero_homObj_twist`. -/
lemma bijective_dualPairing_twist_of_surjective (t : Module.Dual k ((ω).H 1)) (a : ℤ)
    (h : Function.Surjective (dualPairing t (𝒪(a)))) :
    Function.Bijective (dualPairing t (𝒪(a))) := by
  rw [← bijective_dualPairingH_iff]
  have hs : Function.Surjective (dualPairingH t (𝒪(a))) := fun y ↦ by
    obtain ⟨φ, rfl⟩ := h y
    exact ⟨(homObjHZeroAddEquiv _ _).symm φ, by rw [dualPairingH_apply, AddEquiv.apply_symm_apply]⟩
  have := finiteDimensional_H_one_twist k a
  have : FiniteDimensional k (H (homObj (𝒪(a)) ω) 0) := by
    have := finiteDimensional_H_zero_twist k (-a + -2)
    exact (homObjTwistHZeroLinearEquiv k a).symm.finiteDimensional
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_H_zero_homObj_twist k a)).2 hs, hs⟩

lemma finrank_dual_H_one_twist_neg_two :
    Module.finrank k (Module.Dual k ((𝒪(-2)).H 1)) = 1 := by
  obtain ⟨e⟩ := nonempty_H_one_twist_equiv_dual k (-2) le_rfl
  have := finiteDimensional_homogeneousSubmodule k 0
  have := finiteDimensional_H_one_twist k (-2)
  rw [Subspace.dual_finrank_eq, e.finrank_eq, Subspace.dual_finrank_eq]
  exact finrank_homogeneousSubmodule_zero k

/-- `H¹(ℙ¹_k, Ω¹)` is nonzero, so it has a nonzero linear form. -/
lemma exists_dual_H_one_relativeDifferentials_ne_zero :
    ∃ t : Module.Dual k ((ω).H 1), t ≠ 0 := by
  let ι := (nonempty_relativeDifferentials_iso_twist k).some
  let e : (ω).H 1 ≃ₗ[k] (𝒪(-2)).H 1 := ((cohomologyFunctor k 1).mapIso ι).toLinearEquiv
  have := finiteDimensional_H_one_twist k (-2)
  have : FiniteDimensional k ((ω).H 1) := e.symm.finiteDimensional
  have h : Module.finrank k (Module.Dual k ((ω).H 1)) = 1 := by
    rw [Subspace.dual_finrank_eq, e.finrank_eq, ← Subspace.dual_finrank_eq]
    exact finrank_dual_H_one_twist_neg_two k
  have : Nontrivial (Module.Dual k ((ω).H 1)) := Module.nontrivial_of_finrank_eq_succ h
  exact exists_ne 0

/-- The base case `𝒪(-2) ≅ Ω¹` of the duality on the twists: the pairing is nonzero on the
isomorphism `𝒪(-2) ≅ Ω¹`, and `H¹(ℙ¹_k, 𝒪(-2))^∨` is one-dimensional. -/
lemma surjective_dualPairing_twist_neg_two (t : Module.Dual k ((ω).H 1)) (ht : t ≠ 0) :
    Function.Surjective (dualPairing t (𝒪(-2))) := by
  let ι := (nonempty_relativeDifferentials_iso_twist k).some
  obtain ⟨c, hc⟩ : ∃ c, t c ≠ 0 := by
    by_contra! h
    exact ht (LinearMap.ext h)
  have hne : dualPairingH t (𝒪(-2)) ((homObjHZeroAddEquiv _ _).symm ι.inv) ≠ 0 := by
    rw [dualPairingH_apply, AddEquiv.apply_symm_apply]
    intro h0
    refine hc ?_
    have := LinearMap.congr_fun h0 (H.map ι.hom 1 c)
    rwa [dualPairing_apply, ← H.map_comp_apply, ι.hom_inv_id, H.map_id_apply] at this
  have hd := finrank_dual_H_one_twist_neg_two k
  have := finiteDimensional_H_one_twist k (-2)
  have hr : LinearMap.range (dualPairingH t (𝒪(-2))) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    refine le_antisymm (Submodule.finrank_le _) ?_
    rw [hd, Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    have hmem := LinearMap.mem_range_self (dualPairingH t (𝒪(-2)))
      ((homObjHZeroAddEquiv _ _).symm ι.inv)
    exact fun h ↦ hne (by rw [h] at hmem; exact (Submodule.mem_bot k).1 hmem)
  intro y
  obtain ⟨x, rfl⟩ := LinearMap.range_eq_top.1 hr y
  exact ⟨_, rfl⟩

/-- **Duality on the projective line for the twists.** For every `a`, the duality pairing
`Hom(𝒪(a), Ω¹) → H¹(ℙ¹_k, 𝒪(a))^∨` is bijective. -/
theorem bijective_dualPairing_twist (t : Module.Dual k ((ω).H 1)) (ht : t ≠ 0) (a : ℤ) :
    Function.Bijective (dualPairing t (𝒪(a))) := by
  refine bijective_dualPairing_twist_of_surjective k t a ?_
  rcases le_or_gt (-1) a with ha | ha
  · have := subsingleton_H_one_twist k a ha
    intro y
    refine ⟨0, LinearMap.ext fun z ↦ ?_⟩
    rw [Subsingleton.elim z 0, map_zero, map_zero]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = -2 - n := ⟨(-2 - a).toNat, by omega⟩
    clear ha
    induction n with
    | zero =>
      rw [Nat.cast_zero, sub_zero]
      exact surjective_dualPairing_twist_neg_two k t ht
    | succ n ih =>
      have hb := bijective_dualPairing_twist_of_surjective k t _ ih
      have e : -2 - ((n + 1 : ℕ) : ℤ) + 1 = -2 - n := by push_cast; ring
      rw [← e] at hb
      set m : ℤ := -2 - ((n + 1 : ℕ) : ℤ)
      have : Subsingleton ((koszul (Spec (.of k)) m).X₃.H 0) := by
        rw [koszul_X₃]
        exact subsingleton_H_zero_twist_of_neg k _ (by simp only [m]; omega)
      exact surjective_dualPairing_of_injective t (koszulLeft (Spec (.of k)) m)
        (H.injective_map_f_one (S := koszul (Spec (.of k)) m) (koszul_shortExact _ m))
        (bijective_dualPairing_biprod t _ _ hb hb).2

/-- **Duality on the projective line for coherent modules.** For a coherent `𝒪_{ℙ¹_k}`-module
`𝒢`, the duality pairing `Hom(𝒢, Ω¹) → H¹(ℙ¹_k, 𝒢)^∨` is bijective. -/
theorem bijective_dualPairing_of_isCoherent (t : Module.Dual k ((ω).H 1)) (ht : t ≠ 0)
    (G : (ProjectiveLine (Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) G]
    [SheafOfModules.IsFinitePresentation (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) G] :
    Function.Bijective (dualPairing t G) := by
  have hsig (ι : Type u) [Finite ι] (e : ι → ℕ) :=
    bijective_dualPairing_sigma t _ fun j ↦ bijective_dualPairing_twist k t ht (-(e j : ℤ))
  obtain ⟨ι₀, _, e₀, φ₀, hφ₀, hK₀, hK₀'⟩ := ProjectiveSpace.exists_epi_sigma_twist k G
  obtain ⟨ι₁, _, e₁, φ₁, hφ₁, -, -⟩ := ProjectiveSpace.exists_epi_sigma_twist k (kernel φ₀)
  have hS : (ShortComplex.mk (kernel.ι φ₀) φ₀ (kernel.condition φ₀)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel φ₀))
      inferInstance hφ₀
  have : Subsingleton ((kernel φ₀).H (1 + 1)) := subsingleton_H_of_two_le k (kernel φ₀) le_rfl
  exact bijective_dualPairing_of_epi t φ₀ φ₁ (hsig ι₀ e₀) (hsig ι₁ e₁).1
    (H.surjective_map_g (S := ShortComplex.mk (kernel.ι φ₀) φ₀ (kernel.condition φ₀)) hS 1)

/-- **Duality on the projective line, `H¹`.** For coherent `𝒪_{ℙ¹_k}`-modules `𝒢`, there is an
isomorphism `H¹(ℙ¹_k, 𝒢)^∨ ≅ Hom(𝒢, Ω¹_{ℙ¹_k/k})`, natural in `𝒢`. -/
theorem nonempty_dual_H_one_iso :
    Nonempty ((Scheme.Modules.isCoherent (ProjectiveLine (Spec (.of k)))).ι.op ⋙
        (Scheme.Modules.cohomologyFunctor k 1).op ⋙ ModuleCat.dualFunctor k ≅
      (Scheme.Modules.isCoherent (ProjectiveLine (Spec (.of k)))).ι.op ⋙
        (SheafOfModules.homFunctor (ProjectiveLine (Spec (.of k))).sheaf).flip.obj
          (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials ⋙
        Scheme.Modules.cohomologyFunctor k 0) := by
  obtain ⟨t, ht⟩ := exists_dual_H_one_relativeDifferentials_ne_zero k
  let η : (Scheme.Modules.isCoherent (ProjectiveLine (Spec (.of k)))).ι.op ⋙
        (SheafOfModules.homFunctor (ProjectiveLine (Spec (.of k))).sheaf).flip.obj ω ⋙
        Scheme.Modules.cohomologyFunctor k 0 ⟶
      (Scheme.Modules.isCoherent (ProjectiveLine (Spec (.of k)))).ι.op ⋙
        (Scheme.Modules.cohomologyFunctor k 1).op ⋙ ModuleCat.dualFunctor k :=
    { app G := ModuleCat.ofHom (dualPairingH t G.unop.obj)
      naturality G G' f := by
        ext x : 2
        refine LinearMap.ext fun z ↦ ?_
        change dualPairing t _ (homObjHZeroAddEquiv _ _ (H.map
            (SheafOfModules.homObjMap (R := (ProjectiveLine (Spec (.of k))).sheaf) f.unop.hom
              (𝟙 _)) 0 x)) z =
          dualPairing t _ (homObjHZeroAddEquiv _ _ x) (H.map f.unop.hom 1 z)
        rw [homObjHZeroAddEquiv_map, dualPairing_comp]
        rfl }
  have (G : (Scheme.Modules.isCoherent (ProjectiveLine (Spec (.of k)))).FullSubcategoryᵒᵖ) :
      IsIso (η.app G) := by
    have := G.unop.property.1
    have := G.unop.property.2
    have hb := (bijective_dualPairingH_iff t G.unop.obj).2
      (bijective_dualPairing_of_isCoherent k t ht G.unop.obj)
    exact (ConcreteCategory.isIso_iff_bijective _).2 hb
  have := NatIso.isIso_of_isIso_app η
  exact ⟨(asIso η).symm⟩

/-- **The Yoneda pairing on `ℙ¹_k` is bijective.** For a coherent `𝒪_{ℙ¹_k}`-module `𝒢` and a
nonzero linear form `t` on `H¹(ℙ¹_k, Ω¹) ≅ k`, the Yoneda pairing
`Ext¹(𝒢, Ω¹) → H⁰(ℙ¹_k, 𝒢)^∨`, `ξ ↦ (s ↦ t (s ∘ ξ))`, is bijective. -/
theorem bijective_yonedaDualMap [HasExt.{u} (ProjectiveLine (Spec (.of k))).Modules]
    (t : Module.Dual k ((ω).H 1)) (ht : t ≠ 0) (𝒢 : (ProjectiveLine (Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢]
    [SheafOfModules.IsFinitePresentation (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢] :
    Function.Bijective (yonedaDualMap t 𝒢) := by
  obtain ⟨ι, _, e, φ₀, hφ₀, -, -⟩ := ProjectiveSpace.exists_epi_sigma_twist k 𝒢
  -- `ℰ = ⨁_{j, i} 𝒪(-eⱼ - 1)`, mapping onto `⨁ⱼ 𝒪(-eⱼ)` by the Koszul maps `xᵢ`
  let m : ι → ℤ := fun j ↦ -(e j : ℤ) - 2
  have hm (j : ι) : 𝒪(m j + 1 + 1) = 𝒪(-(e j : ℤ)) := by
    congr 1
    simp only [m]
    omega
  let E := ∐ fun p : ι × ULift.{u} (Fin 2) ↦ 𝒪(m p.1 + 1)
  let ψ : E ⟶ ∐ fun j ↦ 𝒪(-(e j : ℤ)) := Sigma.desc fun p ↦
    mulX (Spec (.of k)) (m p.1 + 1) p.2.down ≫ eqToHom (hm p.1) ≫
      Sigma.ι (fun j ↦ 𝒪(-(e j : ℤ))) p.1
  have hψ : Epi ψ := by
    refine ⟨fun {Z} g h hgh ↦ Sigma.hom_ext _ _ fun j ↦ ?_⟩
    have : Epi (koszulRight (Spec (.of k)) (m j)) :=
      (koszul_shortExact (Spec (.of k)) (m j)).epi_g
    rw [← cancel_epi (koszulRight (Spec (.of k)) (m j) ≫ eqToHom (hm j))]
    simp only [Category.assoc]
    refine biprod.hom_ext' _ _ ?_ ?_
    · have h₀ := Sigma.ι (fun p : ι × ULift.{u} (Fin 2) ↦ 𝒪(m p.1 + 1)) (j, ULift.up 0) ≫= hgh
      simpa [koszulRight, ψ, E] using h₀
    · have h₁ := Sigma.ι (fun p : ι × ULift.{u} (Fin 2) ↦ 𝒪(m p.1 + 1)) (j, ULift.up 1) ≫= hgh
      simpa [koszulRight, ψ, E] using h₁
  let S := ShortComplex.mk (kernel.ι (ψ ≫ φ₀)) (ψ ≫ φ₀) (kernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
      inferInstance (epi_comp ψ φ₀)
  have : IsLocallyNoetherian (ProjectiveLine (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
  have := isQuasicoherent_sigma fun p : ι × ULift.{u} (Fin 2) ↦ 𝒪(m p.1 + 1)
  have := isFinitePresentation_sigma fun p : ι × ULift.{u} (Fin 2) ↦ 𝒪(m p.1 + 1)
  have : SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf)
      S.X₁ := isQuasicoherent_kernel _
  have : SheafOfModules.IsFinitePresentation (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf)
      S.X₁ := isFinitePresentation_kernel _
  have : ∀ p : ι × ULift.{u} (Fin 2), Subsingleton ((𝒪(m p.1 + 1)).H 0) := fun p ↦
    subsingleton_H_zero_twist_of_neg k _ (by simp only [m]; omega)
  have : Subsingleton (S.X₂.H 0) := subsingleton_H_sigma _ 0
  have (p : ι × ULift.{u} (Fin 2)) : Subsingleton (Ext (𝒪(m p.1 + 1)) ω 1) := by
    obtain ⟨eE⟩ := nonempty_ext_addEquiv_H (𝒪(m p.1 + 1)) ω 1
    obtain ⟨eω⟩ := nonempty_relativeDifferentials_iso_twist k
    have : (ω).IsInvertible := IsInvertible.of_iso eω.symm
    let i := asIso (dualTensorHom (𝒪(m p.1 + 1)) ω) ≪≫
      (nonempty_homObj_twist_iso k (m p.1 + 1)).some
    have := subsingleton_H_one_twist k (-(m p.1 + 1) + -2) (by simp only [m]; omega)
    have : Subsingleton (((𝒪(m p.1 + 1))ᵛ ⊗ ω).H 1) :=
      (H.mapLinearEquiv i 1).toEquiv.subsingleton
    exact eE.toEquiv.subsingleton
  have : Subsingleton (Ext S.X₂ ω 1) := Abelian.Ext.subsingleton_sigma _ ω 1
  exact bijective_yonedaDualMap_of_shortExact t hS
    (bijective_dualPairing_of_isCoherent k t ht S.X₁)
    (bijective_dualPairing_sigma t _ fun p ↦ bijective_dualPairing_twist k t ht _).2

/-- **Duality on the projective line, `H⁰`, for one module.** For a coherent
`𝒪_{ℙ¹_k}`-module `𝒢` and a nonzero linear form `t` on `H¹(ℙ¹_k, Ω¹) ≅ k`,
`H⁰(ℙ¹_k, 𝒢)^∨ ≅ Ext¹(𝒢, Ω¹_{ℙ¹_k/k})`: the inverse of the Yoneda pairing
(`bijective_yonedaDualMap`). -/
noncomputable def dualHZeroLinearEquivExt [HasExt.{u} (ProjectiveLine (Spec (.of k))).Modules]
    (t : Module.Dual k ((ω).H 1)) (ht : t ≠ 0) (𝒢 : (ProjectiveLine (Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢]
    [SheafOfModules.IsFinitePresentation (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢] :
    Module.Dual k (𝒢.H 0) ≃ₗ[k] Ext 𝒢 ω 1 :=
  (LinearEquiv.ofBijective (yonedaDualMap t 𝒢) (bijective_yonedaDualMap k t ht 𝒢)).symm

/-- The inverse of `dualHZeroLinearEquivExt` is the Yoneda pairing. -/
lemma dualHZeroLinearEquivExt_symm_apply [HasExt.{u} (ProjectiveLine (Spec (.of k))).Modules]
    (t : Module.Dual k ((ω).H 1)) (ht : t ≠ 0) (𝒢 : (ProjectiveLine (Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢]
    [SheafOfModules.IsFinitePresentation (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢]
    (ξ : Ext 𝒢 ω 1) :
    (dualHZeroLinearEquivExt k t ht 𝒢).symm ξ = yonedaDualMap t 𝒢 ξ :=
  rfl

/-- **The Yoneda pairing on `ℙ¹_k` as a natural isomorphism**: on coherent
`𝒪_{ℙ¹_k}`-modules `𝒢`, the Yoneda pairings `Ext¹(𝒢, Ω¹) → H⁰(ℙ¹_k, 𝒢)^∨` of
`Scheme.Modules.yonedaDualMap` for a nonzero linear form `t` on `H¹(ℙ¹_k, Ω¹) ≅ k` form a natural
isomorphism (`bijective_yonedaDualMap`, `Scheme.Modules.yonedaDualMap_naturality`). -/
noncomputable def extIsoDualHZero [HasExt.{u} (ProjectiveLine (Spec (.of k))).Modules]
    (t : Module.Dual k ((ω).H 1)) (ht : t ≠ 0) :
    (Scheme.Modules.isCoherent (ProjectiveLine (Spec (.of k)))).ι.op ⋙
        Scheme.Modules.extLinearFunctor k ω 1 ≅
      (Scheme.Modules.isCoherent (ProjectiveLine (Spec (.of k)))).ι.op ⋙
        (Scheme.Modules.cohomologyFunctor k 0).op ⋙ ModuleCat.dualFunctor k :=
  NatIso.ofComponents
    (fun G ↦
      haveI := G.unop.property.1
      haveI := G.unop.property.2
      (LinearEquiv.ofBijective (yonedaDualMap t G.unop.obj)
        (bijective_yonedaDualMap k t ht G.unop.obj)).toModuleIso)
    (fun f ↦ by
      ext ξ : 2
      exact yonedaDualMap_naturality t f.unop.hom ξ)

/-- `extIsoDualHZero` is the Yoneda pairing. -/
lemma extIsoDualHZero_hom_app [HasExt.{u} (ProjectiveLine (Spec (.of k))).Modules]
    (t : Module.Dual k ((ω).H 1)) (ht : t ≠ 0)
    (G : (Scheme.Modules.isCoherent (ProjectiveLine (Spec (.of k)))).FullSubcategoryᵒᵖ)
    (ξ : Ext G.unop.obj ω 1) :
    (extIsoDualHZero k t ht).hom.app G ξ = yonedaDualMap t G.unop.obj ξ :=
  rfl

/-- **Duality on the projective line, `H⁰`.** For coherent `𝒪_{ℙ¹_k}`-modules `𝒢`, there is an
isomorphism `H⁰(ℙ¹_k, 𝒢)^∨ ≅ Ext¹(𝒢, Ω¹_{ℙ¹_k/k})`, natural in `𝒢`. -/
theorem nonempty_dual_H_zero_iso_ext [HasExt.{u} (ProjectiveLine (Spec (.of k))).Modules] :
    Nonempty ((Scheme.Modules.isCoherent (ProjectiveLine (Spec (.of k)))).ι.op ⋙
        (Scheme.Modules.cohomologyFunctor k 0).op ⋙ ModuleCat.dualFunctor k ≅
      (Scheme.Modules.isCoherent (ProjectiveLine (Spec (.of k)))).ι.op ⋙
        Scheme.Modules.extLinearFunctor k
          (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials 1) := by
  obtain ⟨t, ht⟩ := exists_dual_H_one_relativeDifferentials_ne_zero k
  exact ⟨(extIsoDualHZero k t ht).symm⟩

/-- **Duality on the projective line, `H⁰`, additively.** For a coherent `𝒪_{ℙ¹_k}`-module
`𝒢`, `H⁰(ℙ¹_k, 𝒢)^∨ ≅ Ext¹(𝒢, Ω¹_{ℙ¹_k/k})`, by the inverse of the Yoneda pairing
(`dualHZeroLinearEquivExt`). -/
theorem nonempty_dual_H_zero_addEquiv_ext [HasExt.{u} (ProjectiveLine (Spec (.of k))).Modules]
    (𝒢 : (ProjectiveLine (Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢]
    [SheafOfModules.IsFinitePresentation (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢] :
    Nonempty (Module.Dual k (𝒢.H 0) ≃+
      Scheme.Modules.Ext 𝒢 (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials
        1) := by
  obtain ⟨t, ht⟩ := exists_dual_H_one_relativeDifferentials_ne_zero k
  exact ⟨(dualHZeroLinearEquivExt k t ht 𝒢).toAddEquiv⟩

/-- **Duality on the projective line, `H⁰`, `k`-linearly.** For a coherent `𝒪_{ℙ¹_k}`-module
`𝒢`, `H⁰(ℙ¹_k, 𝒢)^∨ ≅ Ext¹(𝒢, Ω¹_{ℙ¹_k/k})` as `k`-vector spaces, for the `k`-linear structure
of `𝒪_{ℙ¹_k}`-modules (`Scheme.Modules.linearOfOver`) and the induced `k`-vector space structure
on `Ext`, by the inverse of the Yoneda pairing (`dualHZeroLinearEquivExt`); it is natural in `𝒢`
(`nonempty_dual_H_zero_iso_ext`). -/
theorem nonempty_dual_H_zero_linearEquiv_ext [HasExt.{u} (ProjectiveLine (Spec (.of k))).Modules]
    (𝒢 : (ProjectiveLine (Spec (.of k))).Modules)
    [SheafOfModules.IsQuasicoherent (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢]
    [SheafOfModules.IsFinitePresentation (R := (ProjectiveLine (Spec (.of k))).ringCatSheaf) 𝒢] :
    Nonempty (Module.Dual k (𝒢.H 0) ≃ₗ[k]
      Scheme.Modules.Ext 𝒢 (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials
        1) := by
  obtain ⟨t, ht⟩ := exists_dual_H_one_relativeDifferentials_ne_zero k
  exact ⟨dualHZeroLinearEquivExt k t ht 𝒢⟩

end ProjectiveLine

end AlgebraicGeometry
