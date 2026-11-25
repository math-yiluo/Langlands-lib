/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteRingTorsorAssociatedModule
import all WeilConjectures.ConstructibleSheaf.TorsorDiagonalEvaluationBijective
import WeilConjectures.ConstructibleSheaf.ConstantModuleLocallyConstant
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Pullback and coefficient comparisons for finite-ring associated module sheaves

## References

* Stacks Project, Tags 0DV5 (3), 0DV6, 04TR and 04TS
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.GaloisCover

variable {V : Scheme.{u}} {P : Type u} [Group P] [Finite P]
  (c : Scheme.GaloisCover (ULift.{u + 1} P) V)

private noncomputable def diagonalEvaluationOver
    (Λ : Type (u + 1)) [CommRing Λ]
    (N : Rep.{u + 1} Λ P) (W : c.P.Etale) :
    ModuleCat.of Λ (c.equivariantSectionsOver Λ N
      ((MorphismProperty.Over.map ⊤ c.etale).obj W)) ⟶
      ModuleCat.of Λ (LocallyConstant W.left N.V) :=
  ModuleCat.ofHom
    { toFun s := LocallyConstant.comap
        ⟨c.diagonalSection W, (c.diagonalSection W).continuous⟩ s.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

private theorem diagonalEvaluationOver_bijective (Λ : Type (u + 1)) [CommRing Λ]
    (N : Rep.{u + 1} Λ P) (W : c.P.Etale) :
    Function.Bijective (diagonalEvaluationOver c Λ N W) := by
  -- Reuse the coefficient-independent graph splitting from the imported source module.
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

private theorem presheaf_diagonal (Λ : Type (u + 1)) [CommRing Λ] :
    Nonempty (
      c.equivariantModulePresheafFunctorOver Λ ⋙
        (Functor.whiskeringLeft c.P.Etaleᵒᵖ V.Etaleᵒᵖ _).obj
          (MorphismProperty.Over.map ⊤ c.etale).op ≅
      forget₂ (Rep.{u + 1} Λ P) (ModuleCat.{u + 1} Λ) ⋙
        constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        sheafToPresheaf c.P.smallEtaleTopology _) := by
  let F := c.equivariantModulePresheafFunctorOver Λ ⋙
    (Functor.whiskeringLeft c.P.Etaleᵒᵖ V.Etaleᵒᵖ _).obj
      (MorphismProperty.Over.map ⊤ c.etale).op
  let G := forget₂ (Rep.{u + 1} Λ P) (ModuleCat.{u + 1} Λ)
  let e : F ≅ G ⋙ Scheme.Etale.locallyConstantModulePresheafFunctor c.P Λ :=
    NatIso.ofComponents (fun N ↦
      NatIso.ofComponents (fun W ↦
        (LinearEquiv.ofBijective (diagonalEvaluationOver c Λ N W.unop).hom
          (diagonalEvaluationOver_bijective c Λ N W.unop)).toModuleIso) (by
        intro W W' f
        ext s
        apply LocallyConstant.ext
        intro x
        change s.val (c.sectionRestriction
          ((MorphismProperty.Over.map ⊤ c.etale).map f.unop)
          (c.diagonalSection W'.unop x)) =
          s.val (c.diagonalSection W.unop (f.unop.left x))
        have h : c.diagonalSection W'.unop ≫ c.sectionRestriction
            ((MorphismProperty.Over.map ⊤ c.etale).map f.unop) =
            f.unop.left ≫ c.diagonalSection W.unop := by
          apply Limits.pullback.hom_ext <;>
            simp [diagonalSection, sectionRestriction, MorphismProperty.Over.w f.unop]
        simpa only [Scheme.Hom.comp_apply] using
          congrArg (fun k ↦ s.val (k x)) h)) (by
      intro N N' f
      ext W s
      rfl)
  obtain ⟨h⟩ := Scheme.Etale.locallyConstantModulePresheafFunctor_iso_constantSheaf c.P Λ
  exact ⟨e ≪≫ Functor.isoWhiskerLeft G h⟩

private noncomputable def constantToInvariant {V : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]
    {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) :
    (Functor.const V.Etaleᵒᵖ).obj
        (ModuleCat.of (Λ) (Λ)) ⟶
      c.equivariantModulePresheafOver Λ
          (Rep.trivial Λ P Λ) where
  app W := ModuleCat.ofHom
    { toFun := fun a ↦ ⟨LocallyConstant.const _ a, by intro g x; rfl⟩
      map_add' := by intro a b; rfl
      map_smul' := by intro r a; rfl }
  naturality _ _ _ := by rfl

private theorem trivial_comparison (Λ : Type (u + 1)) [CommRing Λ] :
    Nonempty ((c.associatedModuleFunctorOver Λ).obj (Rep.trivial Λ P Λ) ≅
      (constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ)) := by
  have := c.etale
  have := c.surjective
  let Q := c.equivariantModulePresheafOver Λ (Rep.trivial Λ P Λ)
  let η := constantToInvariant Λ c
  have hηinj : Presheaf.IsLocallyInjective V.smallEtaleTopology η := by
    constructor
    intro W a b hab
    by_cases h : a = b
    · subst h
      exact V.smallEtaleTopology.superset_covering (fun _ _ _ ↦ rfl)
        (V.smallEtaleTopology.top_mem _)
    · have : IsEmpty (Opposite.unop W).left := ⟨fun w ↦ by
        obtain ⟨x, hx⟩ := Surjective.surj (f := Limits.pullback.fst (Opposite.unop W).hom c.π) w
        exact h (congrArg (fun s ↦ s.val x) hab)⟩
      apply V.smallEtaleTopology.superset_covering _
        ((Scheme.ofArrows_mem_smallEtaleTopology_iff (Z := PEmpty.elim) (W := Opposite.unop W)
          (fun i : PEmpty.{1} ↦ i.elim)).2
          (Set.eq_univ_of_forall fun x ↦ isEmptyElim x))
      rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      exact i.elim
  have hηsurj : Presheaf.IsLocallySurjective V.smallEtaleTopology η := by
    constructor
    intro W s
    let U (a : Λ) : (c.sectionSpace W).Opens :=
      ⟨s.val ⁻¹' {a}, s.val.isLocallyConstant.isOpen_fiber a⟩
    let T' (a : Λ) : c.P.Etale :=
      Scheme.Etale.mk ((U a).ι ≫ Limits.pullback.snd W.hom c.π)
    let T (a : Λ) : V.Etale :=
      (MorphismProperty.Over.map ⊤ c.etale).obj (T' a)
    let ι (a : Λ) : T a ⟶ W :=
      MorphismProperty.Over.homMk ((U a).ι ≫ Limits.pullback.fst W.hom c.π)
        (by simp [T, T', Category.assoc, Limits.pullback.condition])
    apply V.smallEtaleTopology.superset_covering _
      ((Scheme.ofArrows_mem_smallEtaleTopology_iff ι).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨a⟩
      refine ⟨a, ?_⟩
      apply (diagonalEvaluationOver_bijective c Λ _ (T' a)).1
      apply LocallyConstant.ext
      intro x
      let graph := c.diagonalSection (T' a)
      change a = s.val (c.sectionRestriction (ι a) (graph x))
      have hp : graph ≫ c.sectionRestriction (ι a) = (U a).ι := by
        apply Limits.pullback.hom_ext <;>
          simp only [Functor.id_obj, Functor.const_obj_obj, diagonalSection,
            MorphismProperty.Over.mk_hom, sectionRestriction,
            MorphismProperty.Over.homMk_hom, Over.homMk_left, Category.assoc,
            Limits.limit.lift_π, Limits.PullbackCone.mk_π_app,
            Limits.limit.lift_π_assoc, Limits.cospan_left, Category.comp_id,
            T', graph, ι]
        exact Category.id_comp _
      rw [← Scheme.Hom.comp_apply, hp]
      exact x.property.symm
    · apply Set.eq_univ_of_forall
      intro w
      obtain ⟨x, hx⟩ := Surjective.surj (f := Limits.pullback.fst W.hom c.π) w
      exact Set.mem_iUnion.2 ⟨s.val x, ⟨⟨x, rfl⟩, hx⟩⟩
  let : Presheaf.IsLocallyInjective V.smallEtaleTopology η := hηinj
  let : Presheaf.IsLocallySurjective V.smallEtaleTopology η := hηsurj
  have hη : V.smallEtaleTopology.W η := V.smallEtaleTopology.W_of_isLocallyBijective η
  have : IsIso ((presheafToSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map η) :=
    (V.smallEtaleTopology.W_iff η).mp hη
  exact ⟨(asIso ((presheafToSheaf V.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)).map η)).symm⟩

/-- The associated sheaf of a representation becomes its constant value upstairs,
and the trivial coefficient representation gives the constant coefficient sheaf. -/
theorem associatedModuleFunctorOver_comparisons (Λ : Type (u + 1)) [CommRing Λ] :
    let C := ModuleCat.{u + 1} Λ
    let T := c.associatedModuleFunctorOver Λ
    Nonempty (T ⋙ Etale.upperStar C c.π ≅
      forget₂ (Rep.{u + 1} Λ P) C ⋙ constantSheaf c.P.smallEtaleTopology C) ∧
      Nonempty (T.obj (Rep.trivial Λ P Λ) ≅
        (constantSheaf V.smallEtaleTopology C).obj (ModuleCat.of Λ Λ)) := by
  let C := ModuleCat.{u + 1} Λ
  let F := c.equivariantModulePresheafFunctorOver Λ
  let T := c.associatedModuleFunctorOver Λ
  obtain ⟨d⟩ := presheaf_diagonal c Λ
  constructor
  · let R := Etale.localizationRestriction C c.π c.etale
    let K := forget₂ (Rep.{u + 1} Λ P) C ⋙ constantSheaf c.P.smallEtaleTopology C
    have h : T ⋙ R ≅ K :=
      (Functor.isoWhiskerLeft F
        ((MorphismProperty.Over.map ⊤ c.etale).pushforwardContinuousSheafificationCompatibility
          C (c.P.smallGrothendieckTopology @Etale)
            (V.smallGrothendieckTopology @Etale)).symm) ≪≫
      Functor.isoWhiskerRight d (presheafToSheaf c.P.smallEtaleTopology C) ≪≫
      Functor.isoWhiskerLeft K (sheafificationNatIso c.P.smallEtaleTopology C).symm
    exact ⟨Functor.isoWhiskerLeft T
      (Etale.upperStarIsoLocalizationRestriction C c.π c.etale) ≪≫ h⟩
  · exact trivial_comparison c Λ

end AlgebraicGeometry.Scheme.GaloisCover
