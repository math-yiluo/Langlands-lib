/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
import WeilConjectures.AlgebraicGeometry.Morphisms.GenericFibreHomExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Detecting the torsor identity on the generic fibre

## References

* Stacks Project, Tag 0BQM and Tag 0EYJ, proof
* Stacks Project, Tag 0BQM, proof
* Tag 0EYJ, proof (extended action)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem genericFibre_isIso {S C : Scheme.{u}}
    [IsIntegral S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [Smooth c] [GeometricallyConnected c]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    {X Y Xη Yη : Scheme.{u}} (πX : X ⟶ C) (πY : Y ⟶ C)
    [IsFinite πX] [Etale πX] [IsFinite πY] [Etale πY]
    (πXη : Xη ⟶ Cη) (πYη : Yη ⟶ Cη) (ψX : Xη ⟶ X) (ψY : Yη ⟶ Y)
    (hX : IsPullback ψX πXη πX j) (hY : IsPullback ψY πYη πY j)
    (f : X ⟶ Y) (hf : f ≫ πY = πX)
    (fη : Xη ⟶ Yη) [IsIso fη] (hfη : fη ≫ πYη = πXη)
    (hcompat : ψX ≫ f = fη ≫ ψY) : IsIso f := by
  have hbη : inv fη ≫ πXη = πYη := by
    rw [← hfη, IsIso.inv_hom_id_assoc]
  obtain ⟨b, hb, _⟩ := finiteEtale_genericFibre_hom_extension hS c q j hCη
    πY πX πYη πXη ψY ψX hY hX (inv fη) hbη
  have hfb : f ≫ b = 𝟙 X := by
    have hx := finiteEtale_genericFibre_hom_extension hS c q j hCη
      πX πX πXη πXη ψX ψX hX hX (𝟙 Xη) (by simp)
    apply hx.unique
    · constructor
      · simp [hb.1, hf]
      · calc
          ψX ≫ (f ≫ b) = fη ≫ (ψY ≫ b) := by rw [← Category.assoc, hcompat, Category.assoc]
          _ = (fη ≫ inv fη) ≫ ψX := by rw [hb.2, Category.assoc]
          _ = 𝟙 Xη ≫ ψX := by simp
    · simp
  have hbf : b ≫ f = 𝟙 Y := by
    have hy := finiteEtale_genericFibre_hom_extension hS c q j hCη
      πY πY πYη πYη ψY ψY hY hY (𝟙 Yη) (by simp)
    apply hy.unique
    · constructor
      · simp [hf, hb.1]
      · calc
          ψY ≫ (b ≫ f) = inv fη ≫ (ψX ≫ f) := by rw [← Category.assoc, hb.2, Category.assoc]
          _ = (inv fη ≫ fη) ≫ ψY := by rw [hcompat, Category.assoc]
          _ = 𝟙 Yη ≫ ψY := by simp
    · simp
  exact ⟨⟨b, hfb, hbf⟩⟩

/-- Any family of endomorphisms over C compatible with the generic torsor action
has an invertible canonical torsor map. No action laws are assumed here. -/
theorem GaloisCover.isIso_sigmaDesc_of_genericFibre {S C : Scheme.{u}}
    [IsIntegral S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [Smooth c] [GeometricallyConnected c]
    (G : Type (u + 1)) [Group G] [Finite G]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (Z : GaloisCover G Cη) {P : Scheme.{u}} (π : P ⟶ C)
    [IsFinite π] [Etale π] (ψ : Z.P ⟶ P) (hψ : IsPullback ψ Z.π π j)
    (a : G → (P ⟶ P)) (ha : ∀ g : G, a g ≫ π = π)
    (hcompat : ∀ g : G, Z.smul g ≫ ψ = ψ ≫ a g) :
    IsIso (Sigma.desc fun g : G ↦
      pullback.lift (f := π) (g := π) (a g) (𝟙 P) (by simp [ha])) := by
  let t : (∐ fun _ : G ↦ P) ⟶ pullback π π := Sigma.desc fun g : G ↦
    pullback.lift (f := π) (g := π) (a g) (𝟙 P) (by simp [ha])
  let tη : (∐ fun _ : G ↦ Z.P) ⟶ pullback Z.π Z.π := Sigma.desc fun g : G ↦
    pullback.lift (f := Z.π) (g := Z.π) (Z.smul g) (𝟙 Z.P) (by simp [Z.smul_π])
  have : IsIso tη := Z.isIso_sigmaDesc
  let σ : (∐ fun _ : G ↦ P) ⟶ C := Sigma.desc fun _ : G ↦ π
  let ση : (∐ fun _ : G ↦ Z.P) ⟶ Cη := Sigma.desc fun _ : G ↦ Z.π
  let Ψ : (∐ fun _ : G ↦ Z.P) ⟶ (∐ fun _ : G ↦ P) :=
    Sigma.desc fun g : G ↦ ψ ≫ Sigma.ι (fun _ : G ↦ P) g
  let ρ : pullback π π ⟶ C := pullback.snd π π ≫ π
  let ρη : pullback Z.π Z.π ⟶ Cη := pullback.snd Z.π Z.π ≫ Z.π
  let R : pullback Z.π Z.π ⟶ pullback π π :=
    pullback.map Z.π Z.π π π ψ ψ j hψ.w.symm hψ.w.symm
  have hσ : IsFinite σ := inferInstance
  have hσe : Etale σ := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  have hSigma : IsPullback Ψ ση σ j := by
    have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts
      (coproductIsCoproduct (fun _ : G ↦ P))
    have hs := hu.isPullback_of_isColimit_left (fun _ : G ↦ π) σ j
      (fun _ : G ↦ Z.π) (fun _ : G ↦ ψ) (fun _ : G ↦ hψ.flip)
      (coproductIsCoproduct (fun _ : G ↦ Z.P))
    simpa [Cofan.IsColimit.desc, coproductIsCoproduct, Ψ, ση, σ] using hs.flip
  have hR : IsPullback R ρη ρ j := by
    apply IsPullback.mk'
    · simp [R, ρη, ρ, Category.assoc, hψ.w]
    · intro T φ φ' h₁ h₂
      apply pullback.hom_ext
      · apply hψ.hom_ext
        · simpa [R] using congrArg (fun k ↦ k ≫ pullback.fst π π) h₁
        · simpa [ρη, ← pullback.condition] using h₂
      · apply hψ.hom_ext
        · simpa [R] using congrArg (fun k ↦ k ≫ pullback.snd π π) h₁
        · exact h₂
    · intro T f b hf
      have hf₂ : (f ≫ pullback.snd π π) ≫ π = b ≫ j := by
        simpa [ρ] using hf
      have hf₁ : (f ≫ pullback.fst π π) ≫ π = b ≫ j := by
        simpa [Category.assoc, pullback.condition] using hf₂
      let z₁ := hψ.lift (f ≫ pullback.fst π π) b hf₁
      let z₂ := hψ.lift (f ≫ pullback.snd π π) b hf₂
      have hz : z₁ ≫ Z.π = z₂ ≫ Z.π := by simp [z₁, z₂]
      refine ⟨pullback.lift z₁ z₂ hz, ?_, ?_⟩
      · apply pullback.hom_ext <;> simp [R, z₁, z₂]
      · simp [ρη, z₂]
  have ht : t ≫ ρ = σ := by
    ext g
    simp only [colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt,
      Cofan.mk_ι_app, limit.lift_π_assoc, cospan_right, PullbackCone.mk_π_app,
      colimit.ι_desc, t, ρ, σ]
    change 𝟙 P ≫ π = π
    simp
  have htη : tη ≫ ρη = ση := by
    ext g
    simp only [colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt,
      Cofan.mk_ι_app, limit.lift_π_assoc, cospan_right, PullbackCone.mk_π_app,
      colimit.ι_desc, tη, ρη, ση]
    change 𝟙 Z.P ≫ Z.π = Z.π
    simp
  have hc : Ψ ≫ t = tη ≫ R := by
    apply Sigma.hom_ext
    intro g
    apply pullback.hom_ext
    · simp only [colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt,
        Cofan.mk_ι_app, Category.assoc, colimit.ι_desc, limit.lift_π,
        PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left, hcompat, Ψ, t, tη, R]
    · simp only [colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt,
        Cofan.mk_ι_app, Category.assoc, colimit.ι_desc, limit.lift_π,
        PullbackCone.mk_π_app, Category.comp_id, limit.lift_π_assoc,
        cospan_right, Ψ, t, tη, R]
      change ψ = 𝟙 Z.P ≫ ψ
      simp
  exact genericFibre_isIso hS c q j hCη σ ρ ση ρη Ψ R hSigma hR t ht tη htη hc


end AlgebraicGeometry.Scheme
