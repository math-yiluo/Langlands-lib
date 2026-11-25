/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

/-!
# Base change of Galois covers

The base change `P ×_Y X ⟶ X` of a finite étale Galois cover `P ⟶ Y` with group `G`
(`AlgebraicGeometry.Scheme.GaloisCover`) along any morphism `f : X ⟶ Y` is a Galois cover of
`X` with group `G`, the action being the base change of the action on `P`.

## Main definitions

- `AlgebraicGeometry.Scheme.GaloisCover.pullback`: the base change of a Galois cover.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.GaloisCover

variable {G : Type (u + 1)} [Group G] [Finite G] {X Y : Scheme.{u}}

/-- The base change `P ×_Y X ⟶ P ×_Y X` of the action of `g` on the total space `P` of a Galois
cover. -/
noncomputable def pullbackSMul (c : Y.GaloisCover G) (f : X ⟶ Y) (g : G) :
    Limits.pullback c.π f ⟶ Limits.pullback c.π f :=
  pullback.map c.π f c.π f (c.smul g) (𝟙 X) (𝟙 Y) (by simp [c.smul_π]) (by simp)

@[reassoc (attr := simp)]
lemma pullbackSMul_fst (c : Y.GaloisCover G) (f : X ⟶ Y) (g : G) :
    c.pullbackSMul f g ≫ pullback.fst c.π f = pullback.fst c.π f ≫ c.smul g := by
  simp [pullbackSMul]

@[reassoc (attr := simp)]
lemma pullbackSMul_snd (c : Y.GaloisCover G) (f : X ⟶ Y) (g : G) :
    c.pullbackSMul f g ≫ pullback.snd c.π f = pullback.snd c.π f := by
  simp [pullbackSMul]

/-- The morphism `∐_{g ∈ G} P ×_Y X ⟶ (P ×_Y X) ×_X (P ×_Y X)` for the base-changed action is
an isomorphism: it is the base change of the isomorphism `∐_{g ∈ G} P ⟶ P ×_Y P`, finite
coproducts of schemes being universal. -/
lemma isIso_sigmaDesc_pullbackSMul (c : Y.GaloisCover G) (f : X ⟶ Y) :
    IsIso (Sigma.desc fun g : G ↦ pullback.lift (f := pullback.snd c.π f)
      (g := pullback.snd c.π f) (c.pullbackSMul f g) (𝟙 _) (by simp)) := by
  refine (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk _ fun g : G ↦
    pullback.lift (f := pullback.snd c.π f) (g := pullback.snd c.π f) (c.pullbackSMul f g) (𝟙 _)
      (by simp))).mp ?_
  have := c.isIso_sigmaDesc
  have h₀ := (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk _ fun g : G ↦
    pullback.lift (f := c.π) (g := c.π) (c.smul g) (𝟙 c.P) (by simp [c.smul_π]))).mpr this
  refine FinitaryPreExtensive.isUniversal_finiteCoproducts h₀.some _
    (Discrete.natTrans fun _ ↦ pullback.fst c.π f)
    (pullback.map _ _ c.π c.π (pullback.fst c.π f) (pullback.fst c.π f) f
      pullback.condition.symm pullback.condition.symm) ?_ (.of_discrete _) ?_
  · ext ⟨g⟩
    refine pullback.hom_ext (by simp) ?_
    simp only [Discrete.functor_obj_eq_as, Cofan.mk_pt, NatTrans.comp_app, Functor.const_obj_obj,
      Discrete.natTrans_app, Cofan.mk_ι_app, Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
      Category.comp_id, Functor.const_map_app, limit.lift_π_assoc, cospan_right]
    exact (Category.id_comp _).symm
  · rintro ⟨g⟩
    refine IsPullback.of_right (h₁₂ := pullback.snd _ _) (h₂₂ := pullback.snd c.π c.π) ?_ ?_
      (IsPullback.of_bot (v₁₂ := pullback.fst c.π f) (v₂₁ := pullback.fst c.π c.π) (v₂₂ := c.π)
        (h₃₁ := c.π) ?_ ?_
        (IsPullback.of_hasPullback c.π c.π).flip)
    · simpa using IsPullback.id_horiz (pullback.fst c.π f)
    · refine pullback.hom_ext (by simp) ?_
      simp only [Discrete.functor_obj_eq_as, Cofan.mk_pt, Cofan.mk_ι_app, Category.assoc,
        limit.lift_π, PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_right,
        Discrete.natTrans_app, Category.comp_id]
      exact Category.id_comp _
    · have := (IsPullback.of_hasPullback (pullback.snd c.π f)
        (pullback.snd c.π f)).flip.paste_vert (IsPullback.of_hasPullback c.π f).flip
      simpa [pullback.condition] using this
    · simp

/-- The base change `P ×_Y X ⟶ X` of a Galois cover `P ⟶ Y` with group `G` along `f : X ⟶ Y`,
with `G` acting on the first factor: `P := Limits.pullback c.π f` and
`π := Limits.pullback.snd c.π f`. -/
noncomputable def pullback (c : Y.GaloisCover G) (f : X ⟶ Y) : X.GaloisCover G where
  P := Limits.pullback c.π f
  π := Limits.pullback.snd c.π f
  isFinite := by have := c.isFinite; infer_instance
  etale := by have := c.etale; infer_instance
  surjective := by have := c.surjective; infer_instance
  smul := c.pullbackSMul f
  smul_π g := c.pullbackSMul_snd f g
  one_smul := by ext <;> simp [c.one_smul]
  mul_smul g h := by ext <;> simp [c.mul_smul]
  isIso_sigmaDesc := c.isIso_sigmaDesc_pullbackSMul f

variable (c : Y.GaloisCover G) (f : X ⟶ Y)

@[simp]
lemma pullback_P : (c.pullback f).P = Limits.pullback c.π f :=
  rfl

@[simp]
lemma pullback_π : (c.pullback f).π = Limits.pullback.snd c.π f :=
  rfl

lemma pullback_smul (g : G) : (c.pullback f).smul g = c.pullbackSMul f g :=
  rfl

/-- The square `P ×_Y X ⟶ P`, `P ×_Y X ⟶ X` over `Y` commutes. -/
@[reassoc]
lemma pullback_fst_comp_π : pullback.fst c.π f ≫ c.π = (c.pullback f).π ≫ f :=
  pullback.condition

end AlgebraicGeometry.Scheme.GaloisCover
