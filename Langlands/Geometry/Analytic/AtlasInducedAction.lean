import Langlands.Geometry.Analytic.AtlasDisjointUnionTransport
import Langlands.Geometry.Analytic.AtlasHomeomorph
import Langlands.Geometry.Analytic.GeneralizedAffinoid.InducedAction

/-! # Induced actions on arbitrary supplied affinoid atlases -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AtlasInducedAction

open CategoryTheory Topology
open PresentedAffinoidAlgebra.InducedAction

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] (H : Subgroup G)
  (X : Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) H)

/-- The source action restricted to its original nonempty charts. -/
abbrev localAction (h : H) : X.V.nonemptyPresentation ⟶ X.V.nonemptyPresentation :=
  (X.ρ h).nonemptyMap

@[simp]
theorem localAction_one : localAction H X 1 = 𝟙 X.V.nonemptyPresentation := by
  simp only [localAction, map_one, End.one_def,
    AffinoidAtlasPresentation.Hom.nonemptyMap_id]

/-- The geometric action composes in categorical order. -/
theorem localAction_mul (h k : H) :
    localAction H X (h * k) = localAction H X k ≫ localAction H X h := by
  unfold localAction
  rw [map_mul, End.mul_def, AffinoidAtlasPresentation.Hom.nonemptyMap_comp]

/-- Each coset carries the same original nonempty-chart presentation. -/
abbrev component (_c : G ⧸ H) : AffinoidAtlasPresentation.{u, max z v, max z w} K :=
  X.V.nonemptyPresentation

theorem component_hasNonemptyCharts (c : G ⧸ H) :
    (component H X c).atlas.HasNonemptyCharts :=
  X.V.atlas.nonemptySubatlas_hasNonemptyCharts

/-- Actual coset copies with all the original nonempty, possibly overlapping charts. -/
def copies : AffinoidAtlasPresentation.{u, max z v, max z w} K :=
  AtlasDisjointUnion.presentation (component H X) (component_hasNonemptyCharts H X)

/-- The full bounded inclusion of an entire copy of the source. -/
def copy (c : G ⧸ H) : X.V.nonemptyPresentation ⟶ copies H X :=
  AtlasDisjointUnion.inclusion (component H X) (component_hasNonemptyCharts H X) c

/-- Translation on coset tags with the actual correction action on each source copy. -/
def copiesActionMap (g : G) : copies H X ⟶ copies H X :=
  AtlasDisjointUnion.map (component H X) (component_hasNonemptyCharts H X)
    (component H X) (component_hasNonemptyCharts H X)
    (fun c => g • c) (fun c => localAction H X (correction H g c))

@[simp]
theorem copy_action (g : G) (c : G ⧸ H) :
    copy H X c ≫ copiesActionMap H X g =
      localAction H X (correction H g c) ≫ copy H X (g • c) :=
  AtlasDisjointUnion.inclusion_map _ _ _ _ _ _ c

@[simp]
theorem copiesActionMap_one : copiesActionMap H X 1 = 𝟙 (copies H X) := by
  apply AtlasDisjointUnion.hom_ext (component H X) (component_hasNonemptyCharts H X)
  intro c
  change copy H X c ≫ copiesActionMap H X 1 = copy H X c ≫ 𝟙 _
  simp only [copy_action, correction_one, localAction_one, one_smul,
    Category.id_comp, Category.comp_id]

/-- This equality retains the complete chosen arrows and bounded pullbacks. -/
theorem copiesActionMap_mul (g k : G) :
    copiesActionMap H X (g * k) = copiesActionMap H X k ≫ copiesActionMap H X g := by
  apply AtlasDisjointUnion.hom_ext (component H X) (component_hasNonemptyCharts H X)
  intro c
  change copy H X c ≫ copiesActionMap H X (g * k) =
    copy H X c ≫ (copiesActionMap H X k ≫ copiesActionMap H X g)
  rw [copy_action, ← Category.assoc, copy_action, Category.assoc, copy_action,
    correction_mul, localAction_mul, Category.assoc, mul_smul]

/-- The group acts through full bounded morphisms of the constructed coset atlas. -/
def copiesAction : Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) G where
  V := copies H X
  ρ :=
    { toFun := copiesActionMap H X
      map_one' := copiesActionMap_one H X
      map_mul' := copiesActionMap_mul H X }

/-- Inverses come from the proved group action, including its full chart data. -/
def copiesAutomorphisms : G →* Aut (copies H X) := (copiesAction H X).ρAut

@[simp]
theorem copiesActionMap_baseMap (g : G) (c : G ⧸ H) (x : X.V.space) :
    (copiesActionMap H X g).baseMap ⟨c, x⟩ =
      ⟨g • c, (X.ρ (correction H g c)).baseMap x⟩ := rfl

@[simp]
theorem copiesActionMap_indexMap (g : G) (c : G ⧸ H)
    (i : X.V.nonemptyPresentation.atlas.Index) :
    (copiesActionMap H X g).indexMap ⟨c, i⟩ =
      ⟨g • c, (localAction H X (correction H g c)).indexMap i⟩ := rfl

/-- The original action's bounded algebra map, with only the coset tag added. -/
@[simp]
theorem copiesActionMap_pullback (g : G) (c : G ⧸ H)
    (i : X.V.nonemptyPresentation.atlas.Index) :
    (copiesActionMap H X g).pullback ⟨c, i⟩ =
      (X.ρ (correction H g c)).pullback i.val :=
  AtlasDisjointUnion.map_pullback (component H X) (component_hasNonemptyCharts H X)
    (component H X) (component_hasNonemptyCharts H X)
    (fun c => g • c) (fun c => localAction H X (correction H g c)) c i

/-- The actual source space equipped with its categorical subgroup action. -/
def LocalSpace := X.V.space

instance : TopologicalSpace (LocalSpace H X) :=
  inferInstanceAs (TopologicalSpace X.V.space)

instance : MulAction H (LocalSpace H X) where
  smul h x := (X.ρ h).baseMap x
  one_smul x := by
    change (X.ρ 1).baseMap x = x
    have he : X.ρ 1 = 𝟙 X.V := X.ρ.map_one
    rw [he]
    rfl
  mul_smul h k x := by
    change (X.ρ (h * k)).baseMap x = (X.ρ h).baseMap ((X.ρ k).baseMap x)
    have he : X.ρ (h * k) = X.ρ k ≫ X.ρ h := X.ρ.map_mul h k
    rw [he]
    rfl

@[simp]
theorem local_smul (h : H) (x : LocalSpace H X) :
    h • x = (X.ρ h).baseMap x := rfl

section Quotient

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [ContinuousSMul H (LocalSpace H X)] (hH : IsOpen (H : Set G))

/-- The balanced quotient for the constructed action on the actual source space. -/
abbrev Space := TopologicalInduction.Space H (LocalSpace H X)

/-- This homeomorphism uses actual coset copies, with the source topology unchanged. -/
def copiesHomeomorph : (copies H X).space ≃ₜ Space H X :=
  TopologicalInduction.cosetCopiesHomeomorph H (X := LocalSpace H X) hH

@[simp]
theorem copiesHomeomorph_apply (c : G ⧸ H) (x : LocalSpace H X) :
    copiesHomeomorph H X hH ⟨c, x⟩ = TopologicalInduction.mk H c.out x := rfl

/-- Transport the entire overlapping coset atlas to the actual balanced quotient. -/
def presentation : AffinoidAtlasPresentation.{u, max z v, max z w} K :=
  (copies H X).transport (copiesHomeomorph H X hH)

/-- The actual bounded isomorphism keeps the original algebras and chart indices. -/
def copiesIso : copies H X ≅ presentation H X hH :=
  (copies H X).transportIso (copiesHomeomorph H X hH)

/-- Conjugate the complete bounded action through the constructed isomorphism. -/
def actionMap (g : G) : presentation H X hH ⟶ presentation H X hH :=
  (copiesIso H X hH).inv ≫ copiesActionMap H X g ≫ (copiesIso H X hH).hom

@[simp]
theorem actionMap_one : actionMap H X hH 1 = 𝟙 (presentation H X hH) := by
  simp only [actionMap, copiesActionMap_one, Category.id_comp, Iso.inv_hom_id]

theorem actionMap_mul (g k : G) :
    actionMap H X hH (g * k) = actionMap H X hH k ≫ actionMap H X hH g := by
  simp only [actionMap, copiesActionMap_mul, Category.assoc, Iso.hom_inv_id_assoc]

/-- A full bounded atlas action on the actual quotient, for any supplied source atlas. -/
def action : Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) G where
  V := presentation H X hH
  ρ :=
    { toFun := actionMap H X hH
      map_one' := actionMap_one H X hH
      map_mul' := actionMap_mul H X hH }

/-- The transport isomorphism intertwines the complete action arrows. -/
theorem copiesIso_equivariant (g : G) :
    copiesActionMap H X g ≫ (copiesIso H X hH).hom =
      (copiesIso H X hH).hom ≫ actionMap H X hH g := by
  simp only [actionMap, Iso.hom_inv_id_assoc]

/-- Transport is an equivariant isomorphism of the constructed atlas actions. -/
def equivariantCopiesIso : copiesAction H X ≅ action H X hH :=
  Action.mkIso (copiesIso H X hH) (copiesIso_equivariant H X hH)

/-- The quotient maps are actual bounded atlas automorphisms. -/
def automorphisms : G →* Aut (presentation H X hH) := (action H X hH).ρAut

/-- In coset coordinates the bounded action realizes the actual quotient action. -/
theorem copiesActionMap_realization (g : G) (p : (copies H X).space) :
    g • copiesHomeomorph H X hH p =
      copiesHomeomorph H X hH ((copiesActionMap H X g).baseMap p) := by
  rcases p with ⟨c, x⟩
  change G ⧸ H at c
  change LocalSpace H X at x
  exact TopologicalInduction.smul_cosetCopiesHomeomorph H (X := LocalSpace H X)
    hH g c (g • c) (correction H g c) (correction_spec H g c) x

/-- The transported bounded arrow is precisely left translation on the quotient. -/
@[simp]
theorem actionMap_baseMap (g : G) (x : Space H X) :
    (actionMap H X hH g).baseMap x = g • x := by
  obtain ⟨p, rfl⟩ := (copiesHomeomorph H X hH).surjective x
  change copiesHomeomorph H X hH ((copiesActionMap H X g).baseMap
    ((copiesHomeomorph H X hH).symm (copiesHomeomorph H X hH p))) = _
  rw [Homeomorph.symm_apply_apply]
  exact (copiesActionMap_realization H X hH g p).symm

/-- Only underlying joint continuity is asserted here. -/
theorem continuous_action :
    Continuous (fun p : G × Space H X => (actionMap H X hH p.1).baseMap p.2) := by
  change Continuous (fun p : G × Space H X =>
    (show Space H X from (actionMap H X hH p.1).baseMap p.2))
  simpa only [actionMap_baseMap] using
    (continuous_smul : Continuous (fun p : G × Space H X => p.1 • p.2))

/-- Continuous realization retains exactly the constructed categorical action. -/
def continuousAction : ContAction TopCat.{max z v} G :=
  ⟨(AffinoidAtlasPresentation.spaceFunctor.mapAction G).obj (action H X hH),
    (Action.isContinuous_def _).mpr (continuous_action H X hH)⟩

@[simp]
theorem presentation_algebra (c : G ⧸ H)
    (i : X.V.nonemptyPresentation.atlas.Index) :
    (presentation H X hH).atlas.algebra ⟨c, i⟩ = X.V.atlas.algebra i.val := rfl

@[simp]
theorem presentation_chart (c : G ⧸ H)
    (i : X.V.nonemptyPresentation.atlas.Index) (x : BanachSpectrum (X.V.atlas.algebra i.val)) :
    (presentation H X hH).atlas.chart ⟨c, i⟩ x =
      TopologicalInduction.mk H c.out (show LocalSpace H X from X.V.atlas.chart i.val x) := rfl

@[simp]
theorem actionMap_indexMap (g : G) (c : G ⧸ H)
    (i : X.V.nonemptyPresentation.atlas.Index) :
    (actionMap H X hH g).indexMap ⟨c, i⟩ =
      ⟨g • c, (localAction H X (correction H g c)).indexMap i⟩ := rfl

/-- The identity pullbacks of atlas transport cancel as actual bounded maps. -/
@[simp]
theorem actionMap_pullback (g : G) (c : G ⧸ H)
    (i : X.V.nonemptyPresentation.atlas.Index) :
    (actionMap H X hH g).pullback ⟨c, i⟩ =
      (X.ρ (correction H g c)).pullback i.val := by
  change (BoundedAlgHom.id K _).comp
    ((copiesActionMap H X g).pullback ⟨c, i⟩ |>.comp (BoundedAlgHom.id K _)) = _
  rw [BoundedAlgHom.id_comp, BoundedAlgHom.comp_id, copiesActionMap_pullback]

/-- Within each coset, all original chart containments are preserved and reflected. -/
theorem presentation_chart_subset_iff (c : G ⧸ H)
    (i j : X.V.nonemptyPresentation.atlas.Index) :
    Set.range ((presentation H X hH).atlas.chart ⟨c, i⟩) ⊆
        Set.range ((presentation H X hH).atlas.chart ⟨c, j⟩) ↔
      Set.range (X.V.atlas.chart i.val) ⊆ Set.range (X.V.atlas.chart j.val) := by
  constructor
  · intro h
    exact (AtlasDisjointUnion.chart_subset_iff (fun _ : G ⧸ H =>
      X.V.nonemptyPresentation.atlas) c i j).mp
        ((copies H X).atlas.chart_subset_of_transportSubset (copiesHomeomorph H X hH)
          ⟨c, i⟩ ⟨c, j⟩ h)
  · intro h
    exact (copies H X).atlas.transportChart_subset (copiesHomeomorph H X hH)
      ⟨c, i⟩ ⟨c, j⟩ ((AtlasDisjointUnion.chart_subset_iff
        (fun _ : G ⧸ H => X.V.nonemptyPresentation.atlas) c i j).mpr h)

/-- The bounded restriction is the source restriction, even for distinct nested charts. -/
@[simp]
theorem presentation_restriction_same (c : G ⧸ H)
    (i j : X.V.nonemptyPresentation.atlas.Index)
    (h : Set.range ((presentation H X hH).atlas.chart ⟨c, i⟩) ⊆
      Set.range ((presentation H X hH).atlas.chart ⟨c, j⟩)) :
    (presentation H X hH).atlas.restriction ⟨c, i⟩ ⟨c, j⟩ h =
      X.V.atlas.restriction i.val j.val
        ((presentation_chart_subset_iff H X hH c i j).mp h) := rfl

end Quotient

end Langlands.Analytic.AtlasInducedAction
