/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
public import WeilConjectures.AlgebraicGeometry.Modules.HomObjSections

/-!
# The duality pairing on `H¹`

Let `X` be a scheme over a field `k`, `ω` an `𝒪_X`-module and `t : H¹(X, ω) → k` a linear
form. For every `𝒪_X`-module `G` this file considers the map
`Hom(G, ω) → H¹(X, G)^∨`, `φ ↦ t ∘ H¹(φ)`, which is natural in `G`. By the Yoneda lemma every
natural transformation `Hom(-, ω) ⟶ H¹(X, -)^∨` is of this form.

We prove the formal properties used to show that it is bijective on the coherent modules of a
curve: it is compatible with finite coproducts, surjectivity can be transported along a
morphism inducing an injection on `H¹`, and bijectivity extends from the terms of a
presentation `E₁ ⟶ E₀ ⟶ G ⟶ 0` to `G` when `H¹(E₀) ⟶ H¹(G)` is surjective.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

section LongExact

variable {X : Scheme.{u}} {S : ShortComplex X.Modules}

/-- In a short exact sequence `0 → M₁ → M₂ → M₃ → 0` with `H⁰(M₃) = 0`, the map
`H¹(M₁) ⟶ H¹(M₂)` is injective. -/
lemma H.injective_map_f_one (hS : S.ShortExact) [Subsingleton (S.X₃.H 0)] :
    Function.Injective (H.map S.f 1) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := (H.ker_map_f_eq_range_δ hS 0).le hx
  rw [Subsingleton.elim y 0, map_zero]

/-- In a short exact sequence `0 → M₁ → M₂ → M₃ → 0` with `H^{n+1}(M₁) = 0`, the map
`H^n(M₂) ⟶ H^n(M₃)` is surjective. -/
lemma H.surjective_map_g (hS : S.ShortExact) (n : ℕ) [Subsingleton (S.X₁.H (n + 1))] :
    Function.Surjective (H.map S.g n) := by
  intro x
  exact (H.ker_δ_eq_range_map_g hS n).le (Subsingleton.elim (H.δ hS n x) 0)

end LongExact

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] {ω : X.Modules}
  (t : Module.Dual k (ω.H 1))

/-- The duality pairing `Hom(G, ω) → H¹(X, G)^∨`, `φ ↦ t ∘ H¹(φ)`. -/
def dualPairing (G : X.Modules) : (G ⟶ ω) →+ Module.Dual k (G.H 1) where
  toFun φ := t ∘ₗ H.mapLinearMap k φ 1
  map_zero' := by
    ext x
    simp
  map_add' φ ψ := by
    ext x
    simp

lemma dualPairing_apply {G : X.Modules} (φ : G ⟶ ω) (x : G.H 1) :
    dualPairing t G φ x = t (H.map φ 1 x) :=
  rfl

/-- **Naturality of the duality pairing.** -/
lemma dualPairing_comp {G' G : X.Modules} (f : G' ⟶ G) (φ : G ⟶ ω) :
    dualPairing t G' (f ≫ φ) = dualPairing t G φ ∘ₗ H.mapLinearMap k f 1 := by
  ext x
  simp [dualPairing_apply, H.map_comp_apply]

/-- **Transport of surjectivity.** If `u : A ⟶ E` induces an injection on `H¹` and the duality
pairing of `E` is surjective, then so is the one of `A`. -/
lemma surjective_dualPairing_of_injective {A E : X.Modules} (u : A ⟶ E)
    (hu : Function.Injective (H.map u 1)) (hE : Function.Surjective (dualPairing t E)) :
    Function.Surjective (dualPairing t A) := by
  intro y
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (H.mapLinearMap k u 1)
    (LinearMap.ker_eq_bot.2 hu)
  obtain ⟨ψ, hψ⟩ := hE (y ∘ₗ g)
  refine ⟨u ≫ ψ, ?_⟩
  rw [dualPairing_comp, hψ, LinearMap.comp_assoc, hg, LinearMap.comp_id]

/-- **The duality pairing and finite coproducts.** If the duality pairing is bijective for every
`f j`, it is bijective for the coproduct `∐ f`. -/
lemma bijective_dualPairing_sigma {ι : Type u} [Finite ι] (f : ι → X.Modules)
    (hf : ∀ j, Function.Bijective (dualPairing t (f j))) :
    Function.Bijective (dualPairing t (∐ f)) := by
  classical
  have := Fintype.ofFinite ι
  have : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  have htot : ∑ j, (Sigma.desc (biproduct.ι f) ≫ biproduct.π f j) ≫ Sigma.ι f j = 𝟙 (∐ f) := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    simp [Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp]
  have hsum (c : (∐ f).H 1) : c = ∑ j, H.map (Sigma.ι f j) 1
      (H.map (Sigma.desc (biproduct.ι f) ≫ biproduct.π f j) 1 c) := by
    conv_lhs => rw [← H.map_id_apply (∐ f) 1 c, ← htot]
    rw [H.map_sum_apply]
    simp only [H.map_comp_apply]
  constructor
  · intro x y hxy
    refine Sigma.hom_ext _ _ fun j ↦ (hf j).1 ?_
    rw [dualPairing_comp, dualPairing_comp, hxy]
  · intro y
    choose x hx using fun j ↦ (hf j).2 (y ∘ₗ H.mapLinearMap k (Sigma.ι f j) 1)
    refine ⟨Sigma.desc x, LinearMap.ext fun c ↦ ?_⟩
    rw [hsum c, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [dualPairing_apply, ← H.map_comp_apply, Sigma.ι_comp_desc, ← dualPairing_apply, hx j]
    rfl

/-- **The duality pairing and binary biproducts.** -/
lemma bijective_dualPairing_biprod (A B : X.Modules) (hA : Function.Bijective (dualPairing t A))
    (hB : Function.Bijective (dualPairing t B)) :
    Function.Bijective (dualPairing t (A ⊞ B)) := by
  have hsum (c : (A ⊞ B).H 1) :
      c = H.map biprod.inl 1 (H.map biprod.fst 1 c) +
        H.map biprod.inr 1 (H.map biprod.snd 1 c) := by
    conv_lhs => rw [← H.map_id_apply (A ⊞ B) 1 c, ← biprod.total]
    rw [H.map_add_apply, H.map_comp_apply, H.map_comp_apply]
  constructor
  · intro x y hxy
    refine biprod.hom_ext' _ _ (hA.1 ?_) (hB.1 ?_) <;>
    rw [dualPairing_comp, dualPairing_comp, hxy]
  · intro y
    obtain ⟨x₁, hx₁⟩ := hA.2 (y ∘ₗ H.mapLinearMap k biprod.inl 1)
    obtain ⟨x₂, hx₂⟩ := hB.2 (y ∘ₗ H.mapLinearMap k biprod.inr 1)
    have e₁ (z : A.H 1) : t (H.map (biprod.desc x₁ x₂) 1 (H.map biprod.inl 1 z)) =
        y (H.map biprod.inl 1 z) := by
      rw [← H.map_comp_apply, biprod.inl_desc]
      exact LinearMap.congr_fun hx₁ z
    have e₂ (z : B.H 1) : t (H.map (biprod.desc x₁ x₂) 1 (H.map biprod.inr 1 z)) =
        y (H.map biprod.inr 1 z) := by
      rw [← H.map_comp_apply, biprod.inr_desc]
      exact LinearMap.congr_fun hx₂ z
    refine ⟨biprod.desc x₁ x₂, LinearMap.ext fun c ↦ ?_⟩
    rw [hsum c, map_add, map_add, dualPairing_apply, dualPairing_apply, e₁, e₂]

/-- **The duality pairing on a presentation.** Let `E₁ ⟶ E₀ ⟶ G ⟶ 0` be exact, i.e. `p : E₀ ⟶ G`
is an epimorphism and `q : E₁ ⟶ ker p` is an epimorphism, and assume that `H¹(p)` is
surjective. If the duality pairing is bijective for `E₀` and injective for `E₁`, then it is
bijective for `G`. -/
lemma bijective_dualPairing_of_epi {E₀ E₁ G : X.Modules} (p : E₀ ⟶ G) [Epi p]
    (q : E₁ ⟶ kernel p) [Epi q] (h₀ : Function.Bijective (dualPairing t E₀))
    (h₁ : Function.Injective (dualPairing t E₁)) (hp : Function.Surjective (H.map p 1)) :
    Function.Bijective (dualPairing t G) := by
  have hp' : Function.Injective fun a : Module.Dual k (G.H 1) ↦ a ∘ₗ H.mapLinearMap k p 1 := by
    intro a b hab
    ext c
    obtain ⟨c, rfl⟩ := hp c
    exact LinearMap.congr_fun hab c
  constructor
  · intro x y hxy
    refine (cancel_epi p).1 (h₀.1 ?_)
    rw [dualPairing_comp, dualPairing_comp, hxy]
  · intro y
    obtain ⟨z, hz⟩ := h₀.2 (y ∘ₗ H.mapLinearMap k p 1)
    have hz' : kernel.ι p ≫ z = 0 := by
      refine (cancel_epi q).1 (h₁ ?_)
      rw [comp_zero, ← Category.assoc, dualPairing_comp, hz, map_zero, LinearMap.comp_assoc,
        ← H.mapLinearMap_comp, Category.assoc, kernel.condition, comp_zero]
      ext c
      simp
    obtain ⟨x, hx⟩ := CokernelCofork.IsColimit.desc'
      (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel p)) z hz'
    refine ⟨x, hp' ?_⟩
    change dualPairing t G x ∘ₗ H.mapLinearMap k p 1 = y ∘ₗ H.mapLinearMap k p 1
    rw [← dualPairing_comp]
    exact (congrArg (dualPairing t E₀) hx).trans hz

/-- **The duality pairing on `H⁰(X, Hom(G, ω))`**, as a `k`-linear map
`H⁰(X, Hom(G, ω)) ⟶ H¹(X, G)^∨`: the duality pairing `dualPairing` composed with
`H⁰(X, Hom(G, ω)) ≃ Hom(G, ω)`. -/
def dualPairingH (G : X.Modules) :
    H (X := X) (SheafOfModules.homObj (R := X.sheaf) G ω) 0 →ₗ[k] Module.Dual k (G.H 1) where
  toFun x := dualPairing t G (homObjHZeroAddEquiv G ω x)
  map_add' x y := by
    rw [map_add, map_add]
  map_smul' c x := by
    rw [smul_H_eq_globalSectionsRingHom_smul, homObjHZeroAddEquiv_smul]
    ext y
    rw [dualPairing_apply, H.map_comp_apply, ← smul_H_eq_map,
      ← smul_H_eq_globalSectionsRingHom_smul, LinearMap.map_smul, RingHom.id_apply,
      LinearMap.smul_apply, dualPairing_apply]

lemma dualPairingH_apply (G : X.Modules)
    (x : H (X := X) (SheafOfModules.homObj (R := X.sheaf) G ω) 0) :
    dualPairingH t G x = dualPairing t G (homObjHZeroAddEquiv G ω x) :=
  rfl

lemma bijective_dualPairingH_iff (G : X.Modules) :
    Function.Bijective (dualPairingH t G) ↔ Function.Bijective (dualPairing t G) := by
  change Function.Bijective (dualPairing t G ∘ homObjHZeroAddEquiv G ω) ↔ _
  exact Function.Bijective.of_comp_iff _ (homObjHZeroAddEquiv G ω).bijective

end AlgebraicGeometry.Scheme.Modules
