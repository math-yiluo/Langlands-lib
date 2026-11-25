/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebraColimit
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.AffineOverLimitInclusion

/-!
# Existence of inverse limits with affine transition morphisms

Source: Stacks Project, Limits, Lemmas 01YX and 01YW
(blueprint: lem-weil-pbc-limit-affine-transition).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem hasLimit_affineOver
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    (S : Scheme.{u})
    (F : Jᵒᵖ ⥤ ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom)) :
    HasLimit F := by
  classical
  obtain ⟨_, E, _⟩ := affine_morphism_relative_spec S
  let G := F.rightOp ⋙ E.functor
  let P : ObjectProperty S.CommAlgebraSheaf := fun A ↦ A.toModule.IsQuasicoherent
  obtain ⟨c, ⟨hc⟩, hqc, _⟩ := Scheme.quasiCoherentAlgebra_colimit S J
    (G ⋙ P.ι) (fun j ↦ (G.obj j).property)
  let : HasColimit (G ⋙ P.ι) := ⟨⟨c, hc⟩⟩
  let : CreatesColimit G P.ι := createsColimitFullSubcategoryInclusion' G hc hqc
  let : HasColimit G := hasColimit_of_created G P.ι
  let : HasColimit F.rightOp := Adjunction.hasColimit_of_comp_equivalence F.rightOp E.functor
  exact hasLimit_of_hasColimit_rightOp F

set_option backward.isDefEq.respectTransparency false in
/-- Core existence of the limit cone for a cofiltered diagram with affine transitions.

The proof constructs the relative spectrum of the filtered colimit of the pushforward
structure algebras along one stage.  On every affine open of that stage, the resulting
cone is the spectrum of a filtered colimit of rings, hence is limiting; compatible local
factorizations glue uniquely.  This is the construction in Stacks, Limits, Lemma 01YX.
(blueprint: lem-weil-pbc-limit-affine-transition-core). -/
theorem exists_limit_affine_transition_core
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] :
    ∃ c : Cone D, Nonempty (IsLimit c) := by
  classical
  let i₀ : I := Classical.choice inferInstance
  let J := {j : I // i₀ ≤ j}
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirected J (· ≤ ·) := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  let t : J ⥤ I := (show Monotone (fun j : J ↦ j.val) from fun _ _ h ↦ h).functor
  let : t.op.Initial := Functor.initial_of_exists_of_isCofiltered t.op
    (fun i ↦ by
      obtain ⟨j, h₀, hi⟩ := exists_ge_ge i₀ i.unop
      exact ⟨op ⟨j, h₀⟩, ⟨(homOfLE hi).op⟩⟩)
    (fun {_ _} f g ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)
  let S := D.obj (op i₀)
  let F : Jᵒᵖ ⥤ ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom) :=
    { obj := fun j ↦ ⟨Over.mk (D.map (homOfLE j.unop.property).op), by
        change IsAffineHom (D.map (homOfLE j.unop.property).op)
        infer_instance⟩
      map := fun {j k} f ↦ ⟨Over.homMk (D.map (t.op.map f)) (by
        change D.map (t.op.map f) ≫ D.map (homOfLE k.unop.property).op =
          D.map (homOfLE j.unop.property).op
        rw [← D.map_comp]
        congr 1)⟩
      map_id := by
        intro j
        apply InducedCategory.hom_ext
        apply Over.OverMorphism.ext
        change D.map (t.op.map (𝟙 j)) = 𝟙 _
        rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      map_comp := by
        intro j k l f g
        apply InducedCategory.hom_ext
        apply Over.OverMorphism.ext
        change D.map (t.op.map (f ≫ g)) = D.map (t.op.map f) ≫ D.map (t.op.map g)
        rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] }
  let : HasLimit F := hasLimit_affineOver S F
  let V := (ObjectProperty.ι (fun Y : Over S ↦ IsAffineHom Y.hom)) ⋙ Over.forget S
  let : IsConnected Jᵒᵖ := IsCofiltered.isConnected Jᵒᵖ
  have h : IsLimit (V.mapCone (limit.cone F)) :=
    isLimitOfPreserves (Over.forget S)
      (isLimit_affineOver_inclusion S F (limit.cone F) (limit.isLimit F)).some
  have heq : F ⋙ V = t.op ⋙ D := by
    rfl
  let : HasLimit (t.op ⋙ D) := heq ▸ HasLimit.mk ⟨V.mapCone (limit.cone F), h⟩
  let : HasLimit D := Functor.Initial.hasLimit_of_comp t.op
  exact ⟨limit.cone D, ⟨limit.isLimit D⟩⟩

/-- The affine-stage comparison for a limiting cone.

When every stage is affine, the cone with vertex the spectrum of the filtered colimit of
global sections is limiting by the affine-scheme limit theorem.  Uniqueness of limits then
gives the displayed isomorphism and its compatibility with every projection.  This is
Stacks, Limits, Lemma 01YW (blueprint: lem-weil-pbc-limit-affine-transition-affine-comparison).
-/
theorem limit_affine_transition_affine_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c)
    (ha : ∀ i : Iᵒᵖ, IsAffine (D.obj i)) :
    ∃ e : c.pt ≅ Spec (colimit (D.op ⋙ Scheme.Γ)),
      ∀ i : Iᵒᵖ, e.hom ≫ Spec.map (colimit.ι (D.op ⋙ Scheme.Γ) (op i)) =
        c.π.app i ≫ (ΓSpec.adjunction.unit.app (D.obj i)) := by
  let (i : Iᵒᵖ) : IsAffine (D.obj i) := ha i
  let : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let (i : Iᵒᵖᵒᵖ) : IsAffine (D.op.obj i).unop := ha i.unop
  let hΓ := isColimitOfPreserves Scheme.Γ hc.op
  let eΓ := hΓ.coconePointUniqueUpToIso (colimit.isColimit (D.op ⋙ Scheme.Γ))
  refine ⟨c.pt.isoSpec ≪≫ Scheme.Spec.mapIso eΓ.symm.op, ?_⟩
  intro i
  change c.pt.isoSpec.hom ≫ Spec.map eΓ.inv ≫
    Spec.map (colimit.ι (D.op ⋙ Scheme.Γ) (op i)) = _
  rw [← Spec.map_comp]
  have hι := hΓ.comp_coconePointUniqueUpToIso_inv
    (colimit.isColimit (D.op ⋙ Scheme.Γ)) (op i)
  change colimit.ι (D.op ⋙ Scheme.Γ) (op i) ≫ eΓ.inv = (c.π.app i).appTop at hι
  rw [hι]
  exact Scheme.isoSpec_hom_naturality (X := c.pt) (Y := D.obj i) (c.π.app i)

/-- An inverse system over a directed set with affine transition morphisms has a limit,
its projections are affine, and inverse images of arbitrary opens of any stage are limits
of the corresponding inverse images. For affine stages the limit is the spectrum of the
colimit of their global sections.

Source: Stacks Project, Limits, Lemmas 01YX and 01YW
(blueprint: lem-weil-pbc-limit-affine-transition). -/
theorem exists_limit_affine_transition
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] :
    ∃ c : Cone D, Nonempty (IsLimit c) ∧
      (∀ i : Iᵒᵖ, IsAffineHom (c.π.app i)) ∧
      (∀ (i : Iᵒᵖ) (U : (D.obj i).Opens),
        Nonempty (IsLimit (opensCone D c i U)) ∧
          ∀ {j k : Over i} (f : j ⟶ k), IsAffineHom ((opensDiagram D i U).map f)) ∧
      ((∀ i : Iᵒᵖ, IsAffine (D.obj i)) →
        ∃ e : c.pt ≅ Spec (colimit (D.op ⋙ Scheme.Γ)),
          ∀ i : Iᵒᵖ, e.hom ≫ Spec.map (colimit.ι (D.op ⋙ Scheme.Γ) (op i)) =
            c.π.app i ≫ (ΓSpec.adjunction.unit.app (D.obj i))) := by
  obtain ⟨c, ⟨hc⟩⟩ := exists_limit_affine_transition_core D
  refine ⟨c, ⟨hc⟩, ?_, ?_, ?_⟩
  · intro i
    exact isAffineHom_π_app D c hc i
  · intro i U
    refine ⟨⟨isLimitOpensCone D c hc i U⟩, ?_⟩
    intro j k f
    infer_instance
  · intro ha
    exact limit_affine_transition_affine_comparison D c hc ha

end AlgebraicGeometry
