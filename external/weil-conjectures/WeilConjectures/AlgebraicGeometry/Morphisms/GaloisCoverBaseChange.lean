/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

/-! # Base change of finite Galois torsors

## References

* Stacks Project, Tag 0EZJ, final pullback step
* Tag 0BTV
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

private theorem torsor_comparison_baseChange
    {X Y : Scheme.{u}} (G : Type (u + 1)) [Group G] [Finite G]
    (Z : GaloisCover G X) (j : Y ⟶ X)
    {P : Scheme.{u}} (p : P ⟶ Y) (ψ : P ⟶ Z.P)
    (hψ : IsPullback ψ p Z.π j)
    (a : G → (P ⟶ P)) (ha : ∀ g, a g ≫ p = p)
    (hcompat : ∀ g, a g ≫ ψ = ψ ≫ Z.smul g) :
    IsIso (Sigma.desc fun g : G ↦
      pullback.lift (f := p) (g := p) (a g) (𝟙 P) (by simp [ha])) := by
  let t : (∐ fun _ : G ↦ Z.P) ⟶ pullback Z.π Z.π := Sigma.desc fun g : G ↦
    pullback.lift (f := Z.π) (g := Z.π) (Z.smul g) (𝟙 Z.P) (by simp [Z.smul_π])
  let tη : (∐ fun _ : G ↦ P) ⟶ pullback p p := Sigma.desc fun g : G ↦
    pullback.lift (f := p) (g := p) (a g) (𝟙 P) (by simp [ha])
  have : IsIso t := Z.isIso_sigmaDesc
  let σ : (∐ fun _ : G ↦ Z.P) ⟶ X := Sigma.desc fun _ : G ↦ Z.π
  let ση : (∐ fun _ : G ↦ P) ⟶ Y := Sigma.desc fun _ : G ↦ p
  let Ψ : (∐ fun _ : G ↦ P) ⟶ (∐ fun _ : G ↦ Z.P) :=
    Sigma.desc fun g : G ↦ ψ ≫ Sigma.ι (fun _ : G ↦ Z.P) g
  let ρ : pullback Z.π Z.π ⟶ X := pullback.snd Z.π Z.π ≫ Z.π
  let ρη : pullback p p ⟶ Y := pullback.snd p p ≫ p
  let R : pullback p p ⟶ pullback Z.π Z.π :=
    pullback.map p p Z.π Z.π ψ ψ j hψ.w.symm hψ.w.symm
  have hSigma : IsPullback Ψ ση σ j := by
    have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts
      (coproductIsCoproduct (fun _ : G ↦ Z.P))
    have hs := hu.isPullback_of_isColimit_left (fun _ : G ↦ Z.π) σ j
      (fun _ : G ↦ p) (fun _ : G ↦ ψ) (fun _ : G ↦ hψ.flip)
      (coproductIsCoproduct (fun _ : G ↦ P))
    simpa [Cofan.IsColimit.desc, coproductIsCoproduct, Ψ, ση, σ] using hs.flip
  have hR : IsPullback R ρη ρ j := by
    apply IsPullback.mk'
    · simp [R, ρη, ρ, Category.assoc, hψ.w]
    · intro T φ φ' h₁ h₂
      apply pullback.hom_ext
      · apply hψ.hom_ext
        · simpa [R] using congrArg (fun k ↦ k ≫ pullback.fst Z.π Z.π) h₁
        · simpa [ρη, ← pullback.condition] using h₂
      · apply hψ.hom_ext
        · simpa [R] using congrArg (fun k ↦ k ≫ pullback.snd Z.π Z.π) h₁
        · exact h₂
    · intro T f b hf
      have hf₂ : (f ≫ pullback.snd Z.π Z.π) ≫ Z.π = b ≫ j := by
        simpa [ρ] using hf
      have hf₁ : (f ≫ pullback.fst Z.π Z.π) ≫ Z.π = b ≫ j := by
        simpa [Category.assoc, pullback.condition] using hf₂
      let z₁ := hψ.lift (f ≫ pullback.fst Z.π Z.π) b hf₁
      let z₂ := hψ.lift (f ≫ pullback.snd Z.π Z.π) b hf₂
      have hz : z₁ ≫ p = z₂ ≫ p := by simp [z₁, z₂]
      refine ⟨pullback.lift z₁ z₂ hz, ?_, ?_⟩
      · apply pullback.hom_ext <;> simp [R, z₁, z₂]
      · simp [ρη, z₂]
  have ht : t ≫ ρ = σ := by
    ext g
    simp only [colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt,
      Cofan.mk_ι_app, limit.lift_π_assoc, cospan_right, PullbackCone.mk_π_app,
      colimit.ι_desc, t, ρ, σ]
    change 𝟙 Z.P ≫ Z.π = Z.π
    simp
  have htη : tη ≫ ρη = ση := by
    ext g
    simp only [colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt,
      Cofan.mk_ι_app, limit.lift_π_assoc, cospan_right, PullbackCone.mk_π_app,
      colimit.ι_desc, tη, ρη, ση]
    change 𝟙 P ≫ p = p
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
      change ψ = 𝟙 P ≫ ψ
      simp
  have hs : IsPullback Ψ (tη ≫ ρη) (t ≫ ρ) j := by
    rw [ht, htη]
    exact hSigma
  exact (hs.of_bot hc hR).isIso_snd_of_isIso

/-- A finite Galois torsor has a base change along every morphism of schemes. -/
theorem GaloisCover.exists_baseChange
    {X Y : Scheme.{u}} (G : Type (u + 1)) [Group G] [Finite G]
    (Z : GaloisCover G X) (f : Y ⟶ X) :
    ∃ (W : GaloisCover G Y) (ρ : W.P ⟶ Z.P), IsPullback ρ W.π Z.π f := by
  let P := pullback Z.π f
  let p : P ⟶ Y := pullback.snd _ _
  let ψ : P ⟶ Z.P := pullback.fst _ _
  have hp : IsPullback ψ p Z.π f := .of_hasPullback _ _
  let a : G → (P ⟶ P) := fun g ↦ hp.lift (ψ ≫ Z.smul g) p (by
    rw [Category.assoc, Z.smul_π, hp.w])
  have ha : ∀ g, a g ≫ p = p := fun g ↦ hp.lift_snd _ _ _
  have hcompat : ∀ g, a g ≫ ψ = ψ ≫ Z.smul g := fun g ↦ hp.lift_fst _ _ _
  have hone : a 1 = 𝟙 P := by
    apply hp.hom_ext <;> simp [ha, hcompat, Z.one_smul]
  have hmul : ∀ g h, a (g * h) = a h ≫ a g := by
    intro g h
    apply hp.hom_ext
    · simp only [Category.assoc, hcompat, Z.mul_smul]
      rw [← Category.assoc (a h) ψ (Z.smul g), hcompat, Category.assoc]
    · simp only [Category.assoc, ha]
  have : IsFinite Z.π := Z.isFinite
  have : Etale Z.π := Z.etale
  have : Surjective Z.π := Z.surjective
  let W : GaloisCover G Y :=
    { P := P
      π := p
      isFinite := by dsimp [p, P]; infer_instance
      etale := by dsimp [p, P]; infer_instance
      surjective := by dsimp [p, P]; infer_instance
      smul := a
      smul_π := ha
      one_smul := hone
      mul_smul := hmul
      isIso_sigmaDesc := torsor_comparison_baseChange G Z f p ψ hp a ha hcompat }
  exact ⟨W, ψ, hp⟩

end AlgebraicGeometry.Scheme
