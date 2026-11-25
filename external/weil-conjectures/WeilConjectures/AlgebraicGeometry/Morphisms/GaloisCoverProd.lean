/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

/-!

# Products of Galois covers

For finite étale Galois covers `P₁ ⟶ Y₁` and `P₂ ⟶ Y₂` with groups `G₁` and `G₂`, and morphisms
`a₁ : Y₁ ⟶ S`, `a₂ : Y₂ ⟶ S`, the fibre product `P₁ ×_S P₂ ⟶ Y₁ ×_S Y₂` is a finite étale
Galois cover with group `G₁ × G₂` (`AlgebraicGeometry.Scheme.GaloisCover.prod`).

This is used to show that the termwise monodromy of an external tensor product `N' ⊠ Q'`
factors through the finite `ℓ`-group `P₁ × P₂`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.GaloisCover

variable {G₁ G₂ : Type (u + 1)} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂]
  {S Y₁ Y₂ : Scheme.{u}} (c₁ : GaloisCover G₁ Y₁) (c₂ : GaloisCover G₂ Y₂)
  (a₁ : Y₁ ⟶ S) (a₂ : Y₂ ⟶ S)

attribute [instance] isFinite etale surjective

attribute [reassoc] smul_π

/-- The structure morphism `P₁ ×_S P₂ ⟶ Y₁ ×_S Y₂` of the product cover. -/
noncomputable def prodπ : pullback (c₁.π ≫ a₁) (c₂.π ≫ a₂) ⟶ pullback a₁ a₂ :=
  pullback.map _ _ _ _ c₁.π c₂.π (𝟙 S) (by simp) (by simp)

@[reassoc (attr := simp)]
lemma prodπ_fst : prodπ c₁ c₂ a₁ a₂ ≫ pullback.fst a₁ a₂ = pullback.fst _ _ ≫ c₁.π := by
  simp [prodπ]

@[reassoc (attr := simp)]
lemma prodπ_snd : prodπ c₁ c₂ a₁ a₂ ≫ pullback.snd a₁ a₂ = pullback.snd _ _ ≫ c₂.π := by
  simp [prodπ]

/-- The action of `G₁ × G₂` on `P₁ ×_S P₂`. -/
noncomputable def prodSMul (γ : G₁ × G₂) :
    pullback (c₁.π ≫ a₁) (c₂.π ≫ a₂) ⟶ pullback (c₁.π ≫ a₁) (c₂.π ≫ a₂) :=
  pullback.map _ _ _ _ (c₁.smul γ.1) (c₂.smul γ.2) (𝟙 S) (by simp [c₁.smul_π_assoc])
    (by simp [c₂.smul_π_assoc])

@[reassoc (attr := simp)]
lemma prodSMul_fst (γ : G₁ × G₂) :
    prodSMul c₁ c₂ a₁ a₂ γ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ c₁.smul γ.1 := by
  simp [prodSMul]

@[reassoc (attr := simp)]
lemma prodSMul_snd (γ : G₁ × G₂) :
    prodSMul c₁ c₂ a₁ a₂ γ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ c₂.smul γ.2 := by
  simp [prodSMul]

/-- The structure morphism `P₁ ×_{Y₁} P₁ ⟶ S`. -/
noncomputable abbrev pairToBase {G : Type (u + 1)} [Group G] [Finite G] {Y : Scheme.{u}}
    (c : GaloisCover G Y) (a : Y ⟶ S) : pullback c.π c.π ⟶ S :=
  pullback.fst c.π c.π ≫ c.π ≫ a

/-- The comparison map `(P₁ ×_{Y₁} P₁) ×_S (P₂ ×_{Y₂} P₂) ⟶ P ×_Y P`, where
`P = P₁ ×_S P₂` and `Y = Y₁ ×_S Y₂`. -/
noncomputable def prodPairMap :
    pullback (c₁.pairToBase a₁) (c₂.pairToBase a₂) ⟶
      pullback (prodπ c₁ c₂ a₁ a₂) (prodπ c₁ c₂ a₁ a₂) :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst _ _)
      (by simpa using pullback.condition (f := c₁.pairToBase a₁) (g := c₂.pairToBase a₂)))
    (pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _ ≫ pullback.snd _ _)
      (by
        have h := pullback.condition (f := c₁.pairToBase a₁) (g := c₂.pairToBase a₂)
        simp only [pairToBase, Category.assoc] at h ⊢
        rw [← pullback.condition_assoc (f := c₁.π) (g := c₁.π),
          ← pullback.condition_assoc (f := c₂.π) (g := c₂.π)]
        exact h))
    (by
      apply pullback.hom_ext
      · simp [pullback.condition]
      · simp [pullback.condition])

/-- The inverse of `prodPairMap`. -/
noncomputable def prodPairMapInv :
    pullback (prodπ c₁ c₂ a₁ a₂) (prodπ c₁ c₂ a₁ a₂) ⟶
      pullback (c₁.pairToBase a₁) (c₂.pairToBase a₂) :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst _ _)
      (by
        simpa using congrArg (· ≫ pullback.fst a₁ a₂)
          (pullback.condition (f := prodπ c₁ c₂ a₁ a₂) (g := prodπ c₁ c₂ a₁ a₂))))
    (pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _ ≫ pullback.snd _ _)
      (by
        simpa using congrArg (· ≫ pullback.snd a₁ a₂)
          (pullback.condition (f := prodπ c₁ c₂ a₁ a₂) (g := prodπ c₁ c₂ a₁ a₂))))
    (by simp [pullback.condition])

instance isIso_prodPairMap : IsIso (prodPairMap c₁ c₂ a₁ a₂) := by
  refine ⟨⟨prodPairMapInv c₁ c₂ a₁ a₂, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [prodPairMap, prodPairMapInv]
    · apply pullback.hom_ext <;> simp [prodPairMap, prodPairMapInv]
  · apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [prodPairMap, prodPairMapInv]
    · apply pullback.hom_ext <;> simp [prodPairMap, prodPairMapInv]

/-- **Product of Galois covers**: for finite
étale Galois covers `P₁ ⟶ Y₁`, `P₂ ⟶ Y₂` with groups `G₁`, `G₂` and morphisms `a₁: Y₁ ⟶ S`,
`a₂: Y₂ ⟶ S`, the fibre product `P₁ ×_S P₂ ⟶ Y₁ ×_S Y₂` is a finite étale Galois cover with
group `G₁ × G₂`. -/
@[simps P π smul]
noncomputable def prod : GaloisCover (G₁ × G₂) (pullback a₁ a₂) where
  P := pullback (c₁.π ≫ a₁) (c₂.π ≫ a₂)
  π := prodπ c₁ c₂ a₁ a₂
  isFinite := MorphismProperty.pullbackMap (P := @IsFinite) (e₁ := rfl) (e₂ := rfl)
    (inferInstanceAs (IsFinite c₁.π)) (inferInstanceAs (IsFinite c₂.π))
  etale := MorphismProperty.pullbackMap (P := @Etale) (e₁ := rfl) (e₂ := rfl)
    (inferInstanceAs (Etale c₁.π)) (inferInstanceAs (Etale c₂.π))
  surjective := MorphismProperty.pullbackMap (P := @Surjective) (e₁ := rfl) (e₂ := rfl)
    (inferInstanceAs (Surjective c₁.π)) (inferInstanceAs (Surjective c₂.π))
  smul := prodSMul c₁ c₂ a₁ a₂
  smul_π γ := by
    apply pullback.hom_ext <;> simp [c₁.smul_π, c₂.smul_π]
  one_smul := by
    apply pullback.hom_ext <;> simp [c₁.one_smul, c₂.one_smul]
  mul_smul γ δ := by
    apply pullback.hom_ext <;> simp [c₁.mul_smul, c₂.mul_smul]
  isIso_sigmaDesc := by
    have := c₁.isIso_sigmaDesc
    have := c₂.isIso_sigmaDesc
    let l₁ := fun γ : G₁ ↦ pullback.lift (f := c₁.π) (g := c₁.π) (c₁.smul γ) (𝟙 c₁.P)
      (by simp [c₁.smul_π])
    let l₂ := fun γ : G₂ ↦ pullback.lift (f := c₂.π) (g := c₂.π) (c₂.smul γ) (𝟙 c₂.P)
      (by simp [c₂.smul_π])
    have h₁ : Sigma.desc (fun _ : G₁ ↦ c₁.π ≫ a₁) ≫ 𝟙 S =
        Sigma.desc l₁ ≫ c₁.pairToBase a₁ := by
      refine Sigma.hom_ext _ _ (fun γ ↦ ?_)
      simp [l₁, c₁.smul_π_assoc]
    have h₂ : Sigma.desc (fun _ : G₂ ↦ c₂.π ≫ a₂) ≫ 𝟙 S =
        Sigma.desc l₂ ≫ c₂.pairToBase a₂ := by
      refine Sigma.hom_ext _ _ (fun γ ↦ ?_)
      simp [l₂, c₂.smul_π_assoc]
    have : Sigma.desc (fun γ : G₁ × G₂ ↦ pullback.lift (f := prodπ c₁ c₂ a₁ a₂)
        (g := prodπ c₁ c₂ a₁ a₂) (prodSMul c₁ c₂ a₁ a₂ γ) (𝟙 _)
        (by apply pullback.hom_ext <;> simp [c₁.smul_π, c₂.smul_π])) =
        Sigma.desc (fun (p : G₁ × G₂) ↦
          pullback.map (c₁.π ≫ a₁) (c₂.π ≫ a₂) (Sigma.desc (fun _ : G₁ ↦ c₁.π ≫ a₁))
            (Sigma.desc (fun _ : G₂ ↦ c₂.π ≫ a₂)) (Sigma.ι (fun _ : G₁ ↦ c₁.P) p.1)
            (Sigma.ι (fun _ : G₂ ↦ c₂.P) p.2) (𝟙 S) (by simp) (by simp)) ≫
          pullback.map _ _ _ _ (Sigma.desc l₁) (Sigma.desc l₂) (𝟙 S) h₁ h₂ ≫
          prodPairMap c₁ c₂ a₁ a₂ := by
      refine Sigma.hom_ext _ _ (fun γ ↦ ?_)
      apply pullback.hom_ext
      · apply pullback.hom_ext <;> simp [prodPairMap, l₁, l₂, prodSMul]
      · apply pullback.hom_ext <;> simp [prodPairMap, l₁, l₂, prodSMul]
    rw [this]
    infer_instance

end AlgebraicGeometry.Scheme.GaloisCover
