import Langlands.Sheaf.Equivariant.Site
import Langlands.Topology.GroupAction.InducedCharts
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-! # Spatial induction of equivariant sheaves along an open subgroup -/

noncomputable section

universe u v a b

namespace Langlands.Sheaf.Equivariant.SpatialInduction

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Topology
open Langlands.TopologicalInduction

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (hH : IsOpen (H : Set G))
  (X : Type u) [TopologicalSpace X] [MulAction H X] [ContinuousSMul H X]

/-- The actual image of an open subset in the unit chart of the balanced quotient. -/
def unitOpen (U : ActionOpens H X) : ActionOpens G (Space H X) :=
  ⟨⟨unit H '' U.openSet, isOpenMap_unit hH _ U.openSet.isOpen⟩⟩

@[simp]
theorem mem_unitOpen (U : ActionOpens H X) (x : X) :
    unit H x ∈ (unitOpen H hH X U).openSet ↔ x ∈ U.openSet := by
  constructor
  · rintro ⟨y, hy, e⟩
    exact unit_injective e ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The unit-chart transport functor retains subgroup labels and actual open images. -/
def unitFunctor : ActionOpens H X ⥤ ActionOpens G (Space H X) where
  obj := unitOpen H hH X
  map {U V} f :=
    { label := f.label
      mapsTo := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨f.label • x, f.mapsTo x hx, unit_subgroup_smul f.label x⟩ }
  map_id _ := ActionOpens.Hom.ext rfl
  map_comp _ _ := ActionOpens.Hom.ext rfl

@[simp]
theorem unitFunctor_map_label {U V : ActionOpens H X} (f : U ⟶ V) :
    ((unitFunctor H hH X).map f).label = (f.label : G) := rfl

instance unitFunctor_faithful : (unitFunctor H hH X).Faithful where
  map_injective {_U _V _f _g} e := ActionOpens.Hom.ext (Subtype.ext
    (congrArg ActionOpens.Hom.label e))

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
    [ContinuousSMul H X] in
/-- A group element taking a point of the unit chart into the unit chart lies in `H`. -/
theorem mem_subgroup_of_smul_unit_eq (g : G) (x y : X)
    (e : g • unit H x = unit H y) : g ∈ H := by
  have he := congrArg (component H) e
  rw [smul_unit] at he
  change (g : G ⧸ H) = ((1 : G) : G ⧸ H) at he
  simpa using QuotientGroup.eq.mp he.symm

/-- A labelled arrow between unit-chart opens lifts whenever its label lies in `H`. -/
def liftArrow {U V : ActionOpens H X}
    (f : (unitFunctor H hH X).obj U ⟶ (unitFunctor H hH X).obj V)
    (hf : f.label ∈ H) : U ⟶ V where
  label := ⟨f.label, hf⟩
  mapsTo x hx := by
    apply (mem_unitOpen H hH X V _).mp
    rw [unit_subgroup_smul]
    exact f.mapsTo _ ((mem_unitOpen H hH X U x).mpr hx)

@[simp]
theorem unitFunctor_map_liftArrow {U V : ActionOpens H X}
    (f : (unitFunctor H hH X).obj U ⟶ (unitFunctor H hH X).obj V)
    (hf : f.label ∈ H) :
    (unitFunctor H hH X).map (liftArrow H hH X f hf) = f :=
  ActionOpens.Hom.ext rfl

/-- Nonempty source opens force the label of a unit-chart arrow into the subgroup. -/
theorem label_mem_of_mem {U V : ActionOpens H X}
    (f : (unitFunctor H hH X).obj U ⟶ (unitFunctor H hH X).obj V)
    {x : X} (hx : x ∈ U.openSet) : f.label ∈ H := by
  obtain ⟨y, _, he⟩ := f.mapsTo (unit H x) ((mem_unitOpen H hH X U x).mpr hx)
  exact mem_subgroup_of_smul_unit_eq H X f.label x y he.symm

/-- Failure of fullness on empty opens disappears locally for the transport topology. -/
instance unitFunctor_locallyFull :
    (unitFunctor H hH X).IsLocallyFull (transportTopology G (Space H X)) where
  functorPushforward_imageSieve_mem {U V} f := by
    rw [mem_transportTopology_iff_exists_smul]
    rintro z ⟨x, hx, rfl⟩
    have hf := label_mem_of_mem H hH X f hx
    refine ⟨(unitFunctor H hH X).obj U, 𝟙 _, ?_, unit H x,
      (mem_unitOpen H hH X U x).mpr hx, one_smul G _⟩
    refine ⟨U, 𝟙 _, 𝟙 _, ?_, ?_⟩
    · exact ⟨liftArrow H hH X f hf, by
        simp only [CategoryTheory.Functor.map_id, Category.id_comp,
          unitFunctor_map_liftArrow]⟩
    · simp

/-- Pull an open of the induced space back along an actual translated chart. -/
def chartPreimage (g : G) (U : ActionOpens G (Space H X)) : ActionOpens H X :=
  ⟨⟨chart H g ⁻¹' U.openSet, U.openSet.isOpen.preimage (continuous_chart H g)⟩⟩

/-- Translating the unit-chart image of a chart preimage lands in the original open. -/
def chartArrow (g : G) (U : ActionOpens G (Space H X)) :
    (unitFunctor H hH X).obj (chartPreimage H X g U) ⟶ U where
  label := g
  mapsTo := by
    rintro _ ⟨x, hx, rfl⟩
    change chart H g x ∈ U.openSet at hx
    simpa only [← chart_eq_smul_unit] using hx

/-- Translated unit charts cover every open of the actual balanced quotient. -/
instance unitFunctor_coverDense :
    (unitFunctor H hH X).IsCoverDense (transportTopology G (Space H X)) where
  is_cover U := by
    rw [mem_transportTopology_iff_exists_smul]
    intro z hz
    obtain ⟨⟨g, x⟩, rfl⟩ := Quotient.exists_rep z
    let V := chartPreimage H X g U
    let f := chartArrow H hH X g U
    exact ⟨(unitFunctor H hH X).obj V, f,
      Presieve.in_coverByImage _ f, unit H x, ⟨x, hz, rfl⟩, smul_unit g x⟩

/-- The unit-chart functor preserves and reflects the actual transport covers. -/
theorem unitFunctor_pushforward_mem_iff {U : ActionOpens H X} {S : Sieve U} :
    S.functorPushforward (unitFunctor H hH X) ∈
        transportTopology G (Space H X) ((unitFunctor H hH X).obj U) ↔
      S ∈ transportTopology H X U := by
  rw [mem_transportTopology_iff_exists_smul, mem_transportTopology_iff_exists_smul]
  constructor
  · intro hS x hx
    obtain ⟨V, f, ⟨W, i, k, hi, hfac⟩, v, hv, he⟩ :=
      hS (unit H x) ((mem_unitOpen H hH X U x).mpr hx)
    obtain ⟨y, hy, hey⟩ := k.mapsTo v hv
    refine ⟨W, i, hi, y, hy, unit_injective (H := H) ?_⟩
    calc
      unit H (i.label • y) = (i.label : G) • unit H y := unit_subgroup_smul _ _
      _ = (i.label : G) • (k.label • v) := by rw [hey]
      _ = (k ≫ (unitFunctor H hH X).map i).label • v := (mul_smul _ _ _).symm
      _ = f.label • v := by rw [hfac]
      _ = unit H x := he
  · intro hS z hz
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨V, f, hf, v, hv, he⟩ := hS x hx
    refine ⟨(unitFunctor H hH X).obj V, (unitFunctor H hH X).map f,
      ⟨V, f, 𝟙 _, hf, by simp⟩, unit H v,
      (mem_unitOpen H hH X V v).mpr hv, ?_⟩
    change (f.label : G) • unit H v = unit H x
    rw [← unit_subgroup_smul, he]

/-- The unit chart is a dense subsite for equivariant ordinary-open sheaves. -/
instance unitFunctor_denseSubsite :
    (unitFunctor H hH X).IsDenseSubsite (transportTopology H X)
      (transportTopology G (Space H X)) where
  functorPushforward_mem_iff := unitFunctor_pushforward_mem_iff H hH X

variable (A : Type a) [Category.{b} A]

/-- Restriction to the unit chart, retaining the actual subgroup-labelled arrows. -/
def restrict : TopologicalSheaf G (Space H X) A ⥤ TopologicalSheaf H X A :=
  ((sheafEquivalence G (Space H X) A).functor ⋙
    (unitFunctor H hH X).sheafPushforwardContinuous A
      (transportTopology H X) (transportTopology G (Space H X))) ⋙
    (sheafEquivalence H X A).inverse

instance restrict_full : (restrict H hH X A).Full := by
  dsimp [restrict]
  infer_instance

instance restrict_faithful : (restrict H hH X A).Faithful := by
  dsimp [restrict]
  infer_instance

@[simp]
theorem restrict_obj_obj (F : TopologicalSheaf G (Space H X) A) :
    ((restrict H hH X A).obj F).obj = (unitFunctor H hH X).op ⋙ F.obj := rfl

@[simp]
theorem restrict_obj_obj_obj (F : TopologicalSheaf G (Space H X) A)
    (U : ActionOpens H X) :
    ((restrict H hH X A).obj F).obj.obj (op U) =
      F.obj.obj (op (unitOpen H hH X U)) := rfl

@[simp]
theorem restrict_obj_obj_map (F : TopologicalSheaf G (Space H X) A)
    {U V : ActionOpens H X} (f : U ⟶ V) :
    ((restrict H hH X A).obj F).obj.map f.op =
      F.obj.map ((unitFunctor H hH X).map f).op := rfl

@[simp]
theorem restrict_map_hom_app {F F' : TopologicalSheaf G (Space H X) A}
    (f : F ⟶ F') (U : ActionOpens H X) :
    ((restrict H hH X A).map f).hom.app (op U) =
      f.hom.app (op (unitOpen H hH X U)) := rfl

section Limits

variable [∀ U : (ActionOpens G (Space H X))ᵒᵖ,
  HasLimitsOfShape (StructuredArrow U (unitFunctor H hH X).op) A]

/-- Spatial induction is the actual right Kan extension from the unit-chart subsite. -/
def induce : TopologicalSheaf H X A ⥤ TopologicalSheaf G (Space H X) A :=
  (sheafEquivalence H X A).functor ⋙
    ((unitFunctor H hH X).sheafPushforwardCocontinuous A
      (transportTopology H X) (transportTopology G (Space H X)) ⋙
      (sheafEquivalence G (Space H X) A).inverse)

@[simp]
theorem induce_obj_obj (F : TopologicalSheaf H X A) :
    ((induce H hH X A).obj F).obj =
      (unitFunctor H hH X).op.ran.obj F.obj := rfl

@[simp]
theorem induce_map_hom {F F' : TopologicalSheaf H X A} (f : F ⟶ F') :
    ((induce H hH X A).map f).hom =
      (unitFunctor H hH X).op.ran.map f.hom := rfl

/-- The full spatial equivariant sheaf equivalence, with restriction as forward functor. -/
def restrictionEquivalence :
    TopologicalSheaf G (Space H X) A ≌ TopologicalSheaf H X A :=
  ((sheafEquivalence G (Space H X) A).trans
    ((unitFunctor H hH X).sheafAdjunctionCocontinuous A
      (transportTopology H X) (transportTopology G (Space H X))).toEquivalence).trans
    (sheafEquivalence H X A).symm

@[simp]
theorem restrictionEquivalence_functor :
    (restrictionEquivalence H hH X A).functor = restrict H hH X A := rfl

@[simp]
theorem restrictionEquivalence_inverse :
    (restrictionEquivalence H hH X A).inverse = induce H hH X A := rfl

instance restrict_isEquivalence : (restrict H hH X A).IsEquivalence :=
  (restrictionEquivalence H hH X A).isEquivalence_functor

instance induce_isEquivalence : (induce H hH X A).IsEquivalence :=
  (restrictionEquivalence H hH X A).isEquivalence_inverse

/-- Restricting a spatially induced sheaf recovers the entire original equivariant sheaf. -/
def restrictInduceIso :
    induce H hH X A ⋙ restrict H hH X A ≅ 𝟭 (TopologicalSheaf H X A) :=
  (restrictionEquivalence H hH X A).counitIso

/-- Inducing the unit-chart restriction recovers the entire ambient equivariant sheaf. -/
def induceRestrictIso :
    restrict H hH X A ⋙ induce H hH X A ≅
      𝟭 (TopologicalSheaf G (Space H X) A) :=
  (restrictionEquivalence H hH X A).unitIso.symm

end Limits

end Langlands.Sheaf.Equivariant.SpatialInduction
