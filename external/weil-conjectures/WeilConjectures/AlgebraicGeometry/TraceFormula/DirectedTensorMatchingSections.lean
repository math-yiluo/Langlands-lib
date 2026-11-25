/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TraceFormula.DirectedTensorMatching
public import WeilConjectures.Topology.TraceFormula.DirectedSheafMatching
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer
import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit

/-! # Sections of the directed tensor matching module

Source: Stacks Project, Sheaves, Tags 00AL, 00AM and 04TN; Constructions, Tag 01LI.
(blueprint: lem-trf-directed-tensor-matching-chart-is-iso)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

attribute [local irreducible] tensorPullback tensorPullbackSectionAdjunction
  tensorPullbackSectionComp

/-- The normalized unit is bijective on sections over an open in an open immersion's image. -/
theorem tensorMatching_unit_bijective {A B : Scheme.{u}} (f : A ⟶ B)
    [IsOpenImmersion f] (M : B.Modules) (V : B.Opens) (hV : V ≤ f.opensRange) :
    Function.Bijective (((tensorPullbackSectionAdjunction f).unit.app M).app V) := by
  rw [← (pullbackPushforwardAdjunction f).unit_leftAdjointUniq_hom_app
    (tensorPullbackSectionAdjunction f) M, Hom.comp_app, pushforward_map_app]
  exact (ConcreteCategory.bijective_of_isIso
    ((((pullbackPushforwardAdjunction f).leftAdjointUniq
      (tensorPullbackSectionAdjunction f)).hom.app M).app (f ⁻¹ᵁ V))).comp
        (bijective_pullbackUnit_app_of_isOpenImmersion f M hV)

/-- The functor forgetting a scheme module's linear structure to its sheaf of sets. -/
def tensorMatchingUnderlyingSheaf (X : Scheme.{u}) :
    X.Modules ⥤ TopCat.Sheaf (Type u) X :=
  SheafOfModules.toSheaf X.ringCatSheaf ⋙
    sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u})

variable {X : Scheme.{u}} (𝒰 : X.OpenCover.{u}) [Category.{v} 𝒰.I₀]
  [𝒰.LocallyDirected]
  (M : ∀ i : 𝒰.I₀, (𝒰.X i).Modules)
  (t : ∀ {i j : 𝒰.I₀} (f : i ⟶ j), (tensorPullback (𝒰.trans f)).obj (M j) ≅ M i)

/-- The sheaf of sets underlying a pushed-forward chart module. -/
def tensorMatchingSheaf (i : 𝒰.I₀) : TopCat.Sheaf (Type u) X :=
  (tensorMatchingUnderlyingSheaf X).obj ((pushforward (𝒰.f i)).obj (M i))

/-- Transition of the underlying sheaves of sections. -/
def tensorMatchingSheafMap {i j : 𝒰.I₀} (f : i ⟶ j) :
    tensorMatchingSheaf 𝒰 M j ⟶ tensorMatchingSheaf 𝒰 M i :=
  (tensorMatchingUnderlyingSheaf X).map
    (tensorMatchingTransition (𝒰.trans f) (𝒰.f j) (𝒰.f i) (𝒰.trans_map f)
      (M j) (M i) (t f).hom)

/-- Refinement members have smaller open images. -/
theorem tensorMatching_image_le {i j : 𝒰.I₀} (f : i ⟶ j) :
    (𝒰.f i).opensRange ≤ (𝒰.f j).opensRange := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨𝒰.trans f y, ?_⟩
  rw [← Scheme.Hom.comp_apply, 𝒰.trans_map]

/-- The common lower members cover each intersection of open images. -/
theorem tensorMatching_image_directed (i j : 𝒰.I₀) (x : X)
    (hi : x ∈ (𝒰.f i).opensRange) (hj : x ∈ (𝒰.f j).opensRange) :
    ∃ (k : 𝒰.I₀), Nonempty (k ⟶ i) ∧ Nonempty (k ⟶ j) ∧ x ∈ (𝒰.f k).opensRange := by
  obtain ⟨xi, rfl⟩ := hi
  obtain ⟨xj, hxj⟩ := hj
  obtain ⟨k, p, q, y, hy, _⟩ := 𝒰.exists_of_f_eq_f xi xj hxj.symm
  refine ⟨k, ⟨p⟩, ⟨q⟩, y, ?_⟩
  rw [← 𝒰.trans_map p, Scheme.Hom.comp_apply, hy]

omit [Category.{v} 𝒰.I₀] [𝒰.LocallyDirected] in
/-- A pushforward chart sheaf is determined by its sections on the chart's image. -/
theorem tensorMatching_support (i : 𝒰.I₀) (V : X.Opens) :
    Function.Bijective ((tensorMatchingSheaf 𝒰 M i).restrictSection
      (inf_le_left : V ⊓ (𝒰.f i).opensRange ≤ V)) := by
  have he : 𝒰.f i ⁻¹ᵁ (V ⊓ (𝒰.f i).opensRange) = 𝒰.f i ⁻¹ᵁ V := by
    ext x
    simp
  let a : 𝒰.f i ⁻¹ᵁ (V ⊓ (𝒰.f i).opensRange) ⟶ 𝒰.f i ⁻¹ᵁ V :=
    homOfLE ((𝒰.f i).preimage_mono inf_le_left)
  have : IsIso a := ⟨homOfLE (by rw [he]), Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  change Function.Bijective ((M i).presheaf.map a.op)
  exact ConcreteCategory.bijective_of_isIso _

/-- The adjoint transition is bijective on sections over the smaller chart's image. -/
theorem tensorMatching_local_bijective {i j : 𝒰.I₀} (f : i ⟶ j)
    (V : X.Opens) (hV : V ≤ (𝒰.f i).opensRange) :
    Function.Bijective ((tensorMatchingSheafMap 𝒰 M t f).hom.app (op V)) := by
  have hopen : IsOpenImmersion (𝒰.trans f) := 𝒰.property_trans f
  have hV' : 𝒰.f j ⁻¹ᵁ V ≤ (𝒰.trans f).opensRange := by
    intro y hy
    obtain ⟨z, hz⟩ := hV hy
    refine ⟨z, (𝒰.f j).isOpenEmbedding.injective ?_⟩
    simpa only [← Scheme.Hom.comp_apply, 𝒰.trans_map] using hz
  have hunit : IsIso (((tensorPullbackSectionAdjunction (𝒰.trans f)).unit.app (M j)).app
      (𝒰.f j ⁻¹ᵁ V)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (tensorMatching_unit_bijective (𝒰.trans f) (M j) _ hV')
  change Function.Bijective ((tensorMatchingTransition (𝒰.trans f) (𝒰.f j) (𝒰.f i)
    (𝒰.trans_map f) (M j) (M i) (t f).hom).app V)
  dsimp only [tensorMatchingTransition]
  rw [Hom.comp_app, Hom.comp_app, pushforward_map_app, Adjunction.homEquiv_unit,
    Hom.comp_app]
  exact ConcreteCategory.bijective_of_isIso _

/-- The normalized tensor cocycle becomes the adjoint pushforward cocycle. -/
private theorem tensorMatchingTransition_cocycle
    (ht : ∀ {i j k : 𝒰.I₀} (f : i ⟶ j) (g : j ⟶ k),
      t (f ≫ g) =
        eqToIso (congrArg (fun a ↦ (tensorPullback a).obj (M k)) (𝒰.trans_comp f g)) ≪≫
          (tensorPullbackSectionComp (𝒰.trans f) (𝒰.trans g)).app (M k) ≪≫
          (tensorPullback (𝒰.trans f)).mapIso (t g) ≪≫ t f)
    {i j k : 𝒰.I₀} (f : i ⟶ j) (g : j ⟶ k) :
      tensorMatchingTransition (𝒰.trans (f ≫ g)) (𝒰.f k) (𝒰.f i)
        (𝒰.trans_map (f ≫ g)) (M k) (M i) (t (f ≫ g)).hom =
      tensorMatchingTransition (𝒰.trans g) (𝒰.f k) (𝒰.f j) (𝒰.trans_map g)
        (M k) (M j) (t g).hom ≫
      tensorMatchingTransition (𝒰.trans f) (𝒰.f j) (𝒰.f i) (𝒰.trans_map f)
        (M j) (M i) (t f).hom := by
  exact tensorMatchingTransition_comp_of_iso (𝒰.trans f) (𝒰.trans g) (𝒰.f k)
    (𝒰.trans (f ≫ g)) (𝒰.f j) (𝒰.f i) (𝒰.trans_comp f g)
    (𝒰.trans_map g) (𝒰.trans_map f) (𝒰.trans_map (f ≫ g))
    (M k) (M j) (M i) (t g) (t f) (t (f ≫ g)) (ht f g)

/-- The tensor cocycle induces the ordinary composition law on pushed-forward sections. -/
theorem tensorMatching_sheafMap_comp
    (ht : ∀ {i j k : 𝒰.I₀} (f : i ⟶ j) (g : j ⟶ k),
      t (f ≫ g) =
        eqToIso (congrArg (fun a ↦ (tensorPullback a).obj (M k)) (𝒰.trans_comp f g)) ≪≫
          (tensorPullbackSectionComp (𝒰.trans f) (𝒰.trans g)).app (M k) ≪≫
          (tensorPullback (𝒰.trans f)).mapIso (t g) ≪≫ t f)
    {i j k : 𝒰.I₀} (f : i ⟶ j) (g : j ⟶ k) :
    tensorMatchingSheafMap 𝒰 M t (f ≫ g) =
      tensorMatchingSheafMap 𝒰 M t g ≫ tensorMatchingSheafMap 𝒰 M t f := by
  exact (congrArg (tensorMatchingUnderlyingSheaf X).map
    (tensorMatchingTransition_cocycle 𝒰 M t ht f g)).trans
      ((tensorMatchingUnderlyingSheaf X).map_comp _ _)

/-- Evaluation of a module sheaf at an open as a type; it preserves limits. -/
def tensorMatchingEvaluation (V : X.Opens) : X.Modules ⥤ Type u :=
  toPresheaf X ⋙ (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V) ⋙
    CategoryTheory.forget AddCommGrpCat.{u}

instance tensorMatchingEvaluation_preservesLimits (V : X.Opens) :
    PreservesLimitsOfSize.{u, u} (tensorMatchingEvaluation V) := by
  let E := (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let G := CategoryTheory.forget AddCommGrpCat.{u}
  let : PreservesLimitsOfSize.{u, u} (E ⋙ G) := comp_preservesLimits E G
  exact comp_preservesLimits (toPresheaf X) (E ⋙ G)

/-- The sections of the actual matching module are the matching families of local sections. -/
def tensorMatchingSectionsEquiv (V : X.Opens) :
    Γ(tensorMatchingModule 𝒰 M t, V) ≃
      ((tensorMatchingDiagram 𝒰 M t).map (tensorMatchingEvaluation V)).sections :=
  (Multifork.IsLimit.sectionsEquiv
    (Multifork.isLimitMapOfPreserves (Multiequalizer.multifork (tensorMatchingDiagram 𝒰 M t))
      (tensorMatchingEvaluation V) (limit.isLimit _))).symm

/-- The multiequalizer relations are exactly the directed matching equations. -/
theorem tensorMatchingSections_matching [Quiver.IsThin 𝒰.I₀] (V : X.Opens)
    (s : ((tensorMatchingDiagram 𝒰 M t).map (tensorMatchingEvaluation V)).sections) :
    TopCat.Sheaf.IsMatching (tensorMatchingSheaf 𝒰 M) (tensorMatchingSheafMap 𝒰 M t)
      V s.val := by
  intro i j f
  let a : TensorMatchingIndex 𝒰 := ⟨(i, j), ⟨f⟩⟩
  have h := s.property a
  change s.val i = (tensorMatchingSheafMap 𝒰 M t a.property.some).hom.app (op V) (s.val j)
    at h
  have hf : a.property.some = f := Subsingleton.elim _ _
  rw [hf] at h
  exact h.symm

/-- Local directedness makes the matching projection bijective over a chart's image. -/
theorem tensorMatchingProjection_bijective [Quiver.IsThin 𝒰.I₀]
    (ht : ∀ {i j k : 𝒰.I₀} (f : i ⟶ j) (g : j ⟶ k),
      t (f ≫ g) =
        eqToIso (congrArg (fun a ↦ (tensorPullback a).obj (M k)) (𝒰.trans_comp f g)) ≪≫
          (tensorPullbackSectionComp (𝒰.trans f) (𝒰.trans g)).app (M k) ≪≫
          (tensorPullback (𝒰.trans f)).mapIso (t g) ≪≫ t f)
    (i : 𝒰.I₀) (V : X.Opens) (hi : V ≤ (𝒰.f i).opensRange) :
    Function.Bijective ((tensorMatchingProjection 𝒰 M t i).app V) := by
  let e := tensorMatchingSectionsEquiv 𝒰 M t V
  constructor
  · intro a b hab
    apply e.injective
    apply MulticospanIndex.sections.ext
    apply TopCat.Sheaf.matching_ext (fun j ↦ (𝒰.f j).opensRange)
      (fun f ↦ tensorMatching_image_le 𝒰 f) (tensorMatching_image_directed 𝒰)
      (tensorMatchingSheaf 𝒰 M) (tensorMatchingSheafMap 𝒰 M t)
      (tensorMatching_local_bijective 𝒰 M t) (tensorMatching_support 𝒰 M)
      i V hi (e a).val (e b).val
      (tensorMatchingSections_matching 𝒰 M t V (e a))
      (tensorMatchingSections_matching 𝒰 M t V (e b))
    exact hab
  · intro x
    obtain ⟨s, hs, _⟩ := TopCat.Sheaf.existsUnique_matching
      (fun j ↦ (𝒰.f j).opensRange)
      (fun f ↦ tensorMatching_image_le 𝒰 f) (tensorMatching_image_directed 𝒰)
      (tensorMatchingSheaf 𝒰 M) (tensorMatchingSheafMap 𝒰 M t)
      (tensorMatching_sheafMap_comp 𝒰 M t ht)
      (tensorMatching_local_bijective 𝒰 M t) (tensorMatching_support 𝒰 M) i V hi x
    let d : ((tensorMatchingDiagram 𝒰 M t).map (tensorMatchingEvaluation V)).sections :=
      ⟨s, fun a ↦ (hs.1 a.property.some).symm⟩
    refine ⟨e.symm d, ?_⟩
    have h := congrArg (fun z ↦ z.val i) (e.apply_symm_apply d)
    exact h.trans hs.2

/-- Each canonical chart map of the matching module is an isomorphism. -/
theorem tensorMatchingChart_isIso [Quiver.IsThin 𝒰.I₀]
    (ht : ∀ {i j k : 𝒰.I₀} (f : i ⟶ j) (g : j ⟶ k),
      t (f ≫ g) =
        eqToIso (congrArg (fun a ↦ (tensorPullback a).obj (M k)) (𝒰.trans_comp f g)) ≪≫
          (tensorPullbackSectionComp (𝒰.trans f) (𝒰.trans g)).app (M k) ≪≫
          (tensorPullback (𝒰.trans f)).mapIso (t g) ≪≫ t f)
    (i : 𝒰.I₀) : IsIso (tensorMatchingChart 𝒰 M t i) := by
  apply Hom.isIso_iff_isIso_app.mpr
  intro O
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  let V : X.Opens := 𝒰.f i ''ᵁ O
  have hV : V ≤ (𝒰.f i).opensRange := (𝒰.f i).image_le_opensRange O
  have hunit := tensorMatching_unit_bijective (𝒰.f i) (tensorMatchingModule 𝒰 M t) V hV
  have hp := tensorMatchingProjection_bijective 𝒰 M t ht i V hV
  have hm := ((tensorPullbackSectionAdjunction (𝒰.f i)).homEquiv _ _).apply_symm_apply
    (tensorMatchingProjection 𝒰 M t i)
  rw [Adjunction.homEquiv_unit] at hm
  have hc := congrArg (fun a ↦ a.app V) hm
  rw [Hom.comp_app, pushforward_map_app] at hc
  have hb : Function.Bijective ((tensorMatchingChart 𝒰 M t i).app (𝒰.f i ⁻¹ᵁ V)) := by
    apply (Function.Bijective.of_comp_iff _ hunit).mp
    change Function.Bijective (((tensorPullbackSectionAdjunction (𝒰.f i)).unit.app
      (tensorMatchingModule 𝒰 M t)).app V ≫
        (tensorMatchingChart 𝒰 M t i).app (𝒰.f i ⁻¹ᵁ V))
    exact hc ▸ hp
  have he : 𝒰.f i ⁻¹ᵁ V = O := (𝒰.f i).preimage_image_eq O
  rw [he] at hb
  exact hb

/-- The canonical chart isomorphism of the explicitly constructed matching module. -/
@[irreducible]
def tensorMatchingChartIso [Quiver.IsThin 𝒰.I₀]
    (ht : ∀ {i j k : 𝒰.I₀} (f : i ⟶ j) (g : j ⟶ k),
      t (f ≫ g) =
        eqToIso (congrArg (fun a ↦ (tensorPullback a).obj (M k)) (𝒰.trans_comp f g)) ≪≫
          (tensorPullbackSectionComp (𝒰.trans f) (𝒰.trans g)).app (M k) ≪≫
          (tensorPullback (𝒰.trans f)).mapIso (t g) ≪≫ t f)
    (i : 𝒰.I₀) : (tensorPullback (𝒰.f i)).obj (tensorMatchingModule 𝒰 M t) ≅ M i := by
  have := tensorMatchingChart_isIso 𝒰 M t ht i
  exact ⟨tensorMatchingChart 𝒰 M t i, inv (tensorMatchingChart 𝒰 M t i),
    IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩

/-- The hom map of the canonical chart is the original projection adjoint. -/
@[simp]
theorem tensorMatchingChartIso_hom [Quiver.IsThin 𝒰.I₀]
    (ht : ∀ {i j k : 𝒰.I₀} (f : i ⟶ j) (g : j ⟶ k),
      t (f ≫ g) =
        eqToIso (congrArg (fun a ↦ (tensorPullback a).obj (M k)) (𝒰.trans_comp f g)) ≪≫
          (tensorPullbackSectionComp (𝒰.trans f) (𝒰.trans g)).app (M k) ≪≫
          (tensorPullback (𝒰.trans f)).mapIso (t g) ≪≫ t f)
    (i : 𝒰.I₀) : (tensorMatchingChartIso 𝒰 M t ht i).hom = tensorMatchingChart 𝒰 M t i := by
  unfold tensorMatchingChartIso
  rfl

/-- The canonical chart isomorphisms satisfy the specified normalized descent equation. -/
theorem tensorMatchingChartIso_condition [Quiver.IsThin 𝒰.I₀]
    (ht : ∀ {i j k : 𝒰.I₀} (f : i ⟶ j) (g : j ⟶ k),
      t (f ≫ g) =
        eqToIso (congrArg (fun a ↦ (tensorPullback a).obj (M k)) (𝒰.trans_comp f g)) ≪≫
          (tensorPullbackSectionComp (𝒰.trans f) (𝒰.trans g)).app (M k) ≪≫
          (tensorPullback (𝒰.trans f)).mapIso (t g) ≪≫ t f)
    {i j : 𝒰.I₀} (f : i ⟶ j) :
    eqToIso (congrArg (fun a ↦ (tensorPullback a).obj (tensorMatchingModule 𝒰 M t))
      (𝒰.trans_map f).symm) ≪≫
      (tensorPullbackSectionComp (𝒰.trans f) (𝒰.f j)).app (tensorMatchingModule 𝒰 M t) ≪≫
      (tensorPullback (𝒰.trans f)).mapIso (tensorMatchingChartIso 𝒰 M t ht j) ≪≫ t f =
        tensorMatchingChartIso 𝒰 M t ht i := by
  exact tensorMatching_iso_four_eq_of_hom
    (eqToIso (congrArg (fun a ↦ (tensorPullback a).obj (tensorMatchingModule 𝒰 M t))
      (𝒰.trans_map f).symm))
    ((tensorPullbackSectionComp (𝒰.trans f) (𝒰.f j)).app (tensorMatchingModule 𝒰 M t))
    ((tensorPullback (𝒰.trans f)).mapIso (tensorMatchingChartIso 𝒰 M t ht j))
    (t f) (tensorMatchingChartIso 𝒰 M t ht i)
    (eqToHom (congrArg (fun a ↦ (tensorPullback a).obj (tensorMatchingModule 𝒰 M t))
      (𝒰.trans_map f).symm))
    ((tensorPullbackSectionComp (𝒰.trans f) (𝒰.f j)).hom.app (tensorMatchingModule 𝒰 M t))
    ((tensorPullback (𝒰.trans f)).map (tensorMatchingChart 𝒰 M t j))
    (tensorMatchingChart 𝒰 M t i) (eqToIso.hom _) (Iso.app_hom _ _)
    (tensorMatching_mapIso_hom (tensorPullback (𝒰.trans f))
      (tensorMatchingChartIso 𝒰 M t ht j) (tensorMatchingChart 𝒰 M t j)
      (tensorMatchingChartIso_hom 𝒰 M t ht j))
    (tensorMatchingChartIso_hom 𝒰 M t ht i) (by
      -- Replay the mate calculation: specializing the nested chart-equation theorem
      -- here causes the kernel to expand the tensor construction unnecessarily.
      apply ((tensorPullbackSectionAdjunction (𝒰.f i)).homEquiv _ _).injective
      rw [tensorMatchingTransition_mate (𝒰.trans f) (𝒰.f j) (𝒰.f i) (𝒰.trans_map f)]
      simp only [tensorMatchingChart, Equiv.apply_symm_apply]
      exact tensorMatchingProjection_condition 𝒰 M t f)

end

end AlgebraicGeometry.Scheme.Modules
