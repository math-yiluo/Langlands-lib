/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModule
import WeilConjectures.Mathlib.CategoryTheory.Extensive

/-!
# Evaluation of equivariant sections on the graph upstairs

Source: Stacks Project, Tags 0DV5 (3) and 0DV6.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.GaloisCover

variable {V : Scheme.{u}} {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)

/-- The graph in the pullback of the torsor to an etale object upstairs. -/
noncomputable def diagonalSection (W : c.P.Etale) :
    W.left ⟶ c.sectionSpace ((MorphismProperty.Over.map ⊤ c.etale).obj W) :=
  pullback.lift (𝟙 W.left) W.hom (by simp)

/-- Evaluation on the graph, with the coefficient scalars already restricted. -/
noncomputable def diagonalEvaluation (ℓ : ℕ)
    (N : Rep.{u + 1} (ZMod ℓ) P) (W : c.P.Etale) :
    (ModuleCat.restrictScalars
      (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ)).obj
      (ModuleCat.of _ (c.equivariantSections ℓ N
        ((MorphismProperty.Over.map ⊤ c.etale).obj W))) ⟶
    ModuleCat.of (ULift.{u + 1} (ZMod ℓ))
      (LocallyConstant W.left ((ModuleCat.restrictScalars
        (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ)).obj
          (ModuleCat.of (ZMod ℓ) N.V))) :=
  ModuleCat.ofHom
    { toFun s := LocallyConstant.comap
        ⟨c.diagonalSection W, (c.diagonalSection W).continuous⟩ s.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

private theorem graphCoproduct_isIso (W : c.P.Etale) :
    IsIso (Sigma.desc fun g : P ↦
      c.diagonalSection W ≫ c.sectionAction
        ((MorphismProperty.Over.map ⊤ c.etale).obj W) g) := by
  let D := Sigma.desc fun g : ULift.{u + 1} P ↦
    pullback.lift (f := c.π) (g := c.π) (c.smul g) (𝟙 c.P) (by simp [c.smul_π])
  have : IsIso D := c.isIso_sigmaDesc
  let D' := Sigma.desc fun g : P ↦
    pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (c.smul ⟨g⟩) (by simp [c.smul_π])
  have hD' : D' = (Sigma.reindex Equiv.ulift.symm (fun _ : ULift.{u + 1} P ↦ c.P)).hom ≫
      D ≫ (pullbackSymmetry c.π c.π).hom := by
    apply Sigma.hom_ext
    intro g
    dsimp only [D']
    erw [Sigma.ι_comp_desc, ← Category.assoc, ← Category.assoc,
      (Sigma.ι_reindex_hom Equiv.ulift.symm (fun _ : ULift.{u + 1} P ↦ c.P) g),
      Category.assoc]
    apply pullback.hom_ext <;> simp [D]
  have : IsIso D' := by rw [hD']; infer_instance
  have h := FinitaryPreExtensive.isIso_sigmaDesc_lift_comp
    c.π (fun g : P ↦ c.smul ⟨g⟩) (fun g ↦ c.smul_π ⟨g⟩) W.hom
  have he : (Sigma.desc fun g : P ↦
      c.diagonalSection W ≫ c.sectionAction
        ((MorphismProperty.Over.map ⊤ c.etale).obj W) g) =
      (Sigma.desc fun g : P ↦ pullback.lift (f := W.hom ≫ c.π) (g := c.π)
        (𝟙 W.left) (W.hom ≫ c.smul ⟨g⟩) (by simp [c.smul_π])) := by
    apply Sigma.hom_ext
    intro g
    simp only [Sigma.ι_comp_desc]
    apply pullback.hom_ext
    · simp only [diagonalSection, sectionAction, pullback.map, Category.assoc,
        pullback.lift_fst, Category.comp_id]
      exact (pullback.lift_fst _ _ _).symm
    · simp only [diagonalSection, sectionAction, pullback.map, Category.assoc,
        pullback.lift_snd, pullback.lift_snd_assoc]
      exact (pullback.lift_snd _ _ _).symm
  rw [he]
  exact h

private noncomputable def graphHomeo (W : c.P.Etale) :
    (Σ _ : P, W.left) ≃ₜ
      c.sectionSpace ((MorphismProperty.Over.map ⊤ c.etale).obj W) :=
  haveI := graphCoproduct_isIso c W
  (AlgebraicGeometry.sigmaMk (fun _ : P ↦ W.left)).trans
    (Scheme.homeoOfIso (asIso (Sigma.desc fun g : P ↦
      c.diagonalSection W ≫ c.sectionAction
        ((MorphismProperty.Over.map ⊤ c.etale).obj W) g)))

private theorem graphHomeo_mk (W : c.P.Etale) (g : P) (x : W.left) :
    graphHomeo c W ⟨g, x⟩ =
      c.sectionAction ((MorphismProperty.Over.map ⊤ c.etale).obj W) g
        (c.diagonalSection W x) := by
  change (Sigma.desc fun g : P ↦ c.diagonalSection W ≫
    c.sectionAction ((MorphismProperty.Over.map ⊤ c.etale).obj W) g)
      (AlgebraicGeometry.sigmaMk (fun _ : P ↦ W.left) ⟨g, x⟩) = _
  rw [AlgebraicGeometry.sigmaMk_mk, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
  rfl

private theorem sectionAction_mul (W : V.Etale) (g h : P) :
    c.sectionAction W (g * h) = c.sectionAction W h ≫ c.sectionAction W g := by
  apply pullback.hom_ext
  · simp [sectionAction]
  · simp only [sectionAction, pullback.map, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, ← c.mul_smul]
    rfl

private theorem sectionAction_one (W : V.Etale) : c.sectionAction W 1 = 𝟙 _ := by
  apply pullback.hom_ext
  · simp [sectionAction]
  · simp only [sectionAction, pullback.map, pullback.lift_snd, Category.id_comp]
    change _ ≫ c.smul (1 : ULift.{u + 1} P) = _
    rw [c.one_smul, Category.comp_id]

private theorem graphHomeo_action (W : c.P.Etale) (g h : P) (x : W.left) :
    c.sectionAction ((MorphismProperty.Over.map ⊤ c.etale).obj W) g
      (graphHomeo c W ⟨h, x⟩) = graphHomeo c W ⟨g * h, x⟩ := by
  rw [graphHomeo_mk, graphHomeo_mk, sectionAction_mul, Scheme.Hom.comp_apply]

/-- Graph evaluation is bijective on each etale object upstairs.
Source: Stacks Project, Tags 0DV5 (3) and 0DV6.
(blueprint: lem-weil-pbc-torsor-diagonal-evaluation-bijective)

Proof: Base change the torsor isomorphism to W. It identifies W times_V c.P
with the disjoint union of the translates of the graph W to c.P, indexed by P.
On the g-th translate extend a locally constant function t by rho(g)(t(w)).
Each translate is open, so these functions define a locally constant function
on the disjoint union and hence on W times_V c.P. The action law rho(hg) =
rho(h) rho(g) proves equivariance. On the graph g = 1, the value is t(w), so
extension is a right inverse to evaluation. Equivariance forces the value on
each other translate from the graph value, making it also a left inverse.
The same argument applies to an empty W and to the zero module. Restriction
of scalars changes neither underlying functions nor bijectivity. -/
theorem diagonalEvaluation_bijective (ℓ : ℕ)
    (N : Rep.{u + 1} (ZMod ℓ) P) (W : c.P.Etale) :
    Function.Bijective (c.diagonalEvaluation ℓ N W) := by
  let E := graphHomeo c W
  have hE (g : P) (x : W.left) :
      E ⟨g, x⟩ = c.sectionAction ((MorphismProperty.Over.map ⊤ c.etale).obj W) g
        (c.diagonalSection W x) := graphHomeo_mk c W g x
  refine ⟨?_, ?_⟩
  · intro s t h
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    obtain ⟨⟨g, w⟩, rfl⟩ := E.surjective x
    rw [hE, s.property, t.property]
    exact congrArg (N.ρ g) (congrArg (fun f ↦ f w) h)
  · intro t
    let : TopologicalSpace N.V := ⊥
    let : DiscreteTopology N.V := ⟨rfl⟩
    let t' : LocallyConstant W.left N.V := t
    let f : LocallyConstant (Σ _ : P, W.left) N.V :=
      ⟨fun z ↦ N.ρ z.1 (t z.2), (IsLocallyConstant.iff_continuous _).2
        (continuous_sigma fun g ↦
          (continuous_of_discreteTopology (f := fun n : N.V ↦ N.ρ g n)).comp
            t'.continuous)⟩
    let s : LocallyConstant
        (c.sectionSpace ((MorphismProperty.Over.map ⊤ c.etale).obj W)) N.V :=
      f.comap ⟨E.symm, E.symm.continuous⟩
    have hs (g : P) (w : W.left) : s (E ⟨g, w⟩) = N.ρ g (t w) := by
      change f (E.symm (E ⟨g, w⟩)) = _
      rw [E.symm_apply_apply]
      rfl
    refine ⟨⟨s, ?_⟩, ?_⟩
    · intro g x
      obtain ⟨⟨h, w⟩, rfl⟩ := E.surjective x
      rw [graphHomeo_action, hs, hs]
      rw [map_mul]
      rfl
    · apply LocallyConstant.ext
      intro w
      change s (c.diagonalSection W w) = t w
      have hw : E ⟨1, w⟩ = c.diagonalSection W w := by
        rw [hE, sectionAction_one]
        rfl
      rw [← hw, hs]
      simp


end AlgebraicGeometry.Scheme.GaloisCover
