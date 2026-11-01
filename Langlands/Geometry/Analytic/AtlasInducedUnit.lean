import Langlands.Geometry.Analytic.AtlasInducedFunctor
import Langlands.Geometry.Analytic.GeneralizedAffinoid.InducedFamilyExtension

/-! # The normalized unit for induced arbitrary atlas actions -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AtlasInducedAction

open CategoryTheory Topology
open PresentedAffinoidAlgebra.InducedAction

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] (H : Subgroup G)

/-- The original categorical subgroup action restricted to its surviving charts. -/
abbrev normalizedAction
    (X : Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) H) :=
  (AffinoidAtlasPresentation.nonemptyActionFunctor H).obj X

variable (X : Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) H)

/-- Correct the chosen identity-coset representative before entering that copy. -/
def unitMap : X.V.nonemptyPresentation ⟶ copies H X :=
  localAction H X (identityRepresentative H)⁻¹ ≫ copy H X (identityCoset H)

/-- The complete unit arrow intertwines the actual subgroup action. -/
theorem unitMap_equivariant (h : H) :
    localAction H X h ≫ unitMap H X =
      unitMap H X ≫ copiesActionMap H X (h : G) := by
  unfold unitMap
  rw [Category.assoc, copy_action, identityCoset_smul]
  simp only [← Category.assoc, ← localAction_mul]
  rw [correction_identityCoset]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- The source of the unit is the same-space normalized action. -/
def unitEquivariantMap : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj
      (copiesAction H X) where
  hom := unitMap H X
  comm := unitMap_equivariant H X

/-- Translating the normalized unit recovers every complete copy inclusion. -/
theorem unitMap_action (c : G ⧸ H) :
    unitMap H X ≫ copiesActionMap H X c.out = copy H X c := by
  rw [unitMap, Category.assoc, copy_action, out_smul_identityCoset,
    correction_out_identityCoset, ← Category.assoc, ← localAction_mul,
    mul_inv_cancel, localAction_one, Category.id_comp]

@[simp]
theorem unitMap_baseMap (x : X.V.space) :
    (unitMap H X).baseMap x =
      ⟨identityCoset H, (X.ρ (identityRepresentative H)⁻¹).baseMap x⟩ := rfl

@[simp]
theorem unitMap_indexMap (i : X.V.nonemptyPresentation.atlas.Index) :
    (unitMap H X).indexMap i =
      ⟨identityCoset H, (localAction H X (identityRepresentative H)⁻¹).indexMap i⟩ := rfl

/-- The actual pullback is the inverse representative's original bounded pullback. -/
@[simp]
theorem unitMap_pullback (i : X.V.nonemptyPresentation.atlas.Index) :
    (unitMap H X).pullback i = (X.ρ (identityRepresentative H)⁻¹).pullback i.val :=
  BoundedAlgHom.comp_id _

variable {X} {Y : Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) H}

/-- Naturality compares the full chosen maps, including their algebra data. -/
theorem unitMap_naturality (f : X ⟶ Y) :
    localMap H f ≫ unitMap H Y = unitMap H X ≫ copiesMap H f := by
  unfold unitMap
  rw [Category.assoc, copy_map]
  calc
    _ = (localMap H f ≫ localAction H Y (identityRepresentative H)⁻¹) ≫
        copy H Y (identityCoset H) := (Category.assoc _ _ _).symm
    _ = (localAction H X (identityRepresentative H)⁻¹ ≫ localMap H f) ≫
        copy H Y (identityCoset H) :=
      congrArg (fun q => q ≫ copy H Y (identityCoset H))
        (localMap_equivariant H f (identityRepresentative H)⁻¹).symm
    _ = _ := Category.assoc _ _ _

/-- The natural unit begins at nonempty-chart restriction, without an assumed inverse. -/
def unitNat : AffinoidAtlasPresentation.nonemptyActionFunctor H ⟶
    copiesFunctor (K := K) H ⋙
      Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype where
  app X := unitEquivariantMap H X
  naturality _ _ f := Action.Hom.ext (unitMap_naturality H f)

section Quotient

variable [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Action (AffinoidAtlasPresentation.{u, max z v, max z w} K) H)
  [ContinuousSMul H (LocalSpace H X)] (hH : IsOpen (H : Set G))

/-- The constructed bounded unit into the actual balanced-quotient presentation. -/
def quotientUnitMap : X.V.nonemptyPresentation ⟶ presentation H X hH :=
  unitMap H X ≫ (copiesIso H X hH).hom

/-- Transport retains full subgroup equivariance. -/
theorem quotientUnitMap_equivariant (h : H) :
    localAction H X h ≫ quotientUnitMap H X hH =
      quotientUnitMap H X hH ≫ actionMap H X hH (h : G) := by
  rw [quotientUnitMap, ← Category.assoc, unitMap_equivariant,
    Category.assoc, copiesIso_equivariant, ← Category.assoc]

/-- The unit on the quotient is an actual equivariant bounded arrow. -/
def quotientUnitEquivariantMap : normalizedAction H X ⟶
    (Action.res (AffinoidAtlasPresentation.{u, max z v, max z w} K) H.subtype).obj
      (action H X hH) where
  hom := quotientUnitMap H X hH
  comm := quotientUnitMap_equivariant H X hH

/-- Balancing removes the arbitrary chosen representative: the point map is [1,x]. -/
@[simp]
theorem quotientUnitMap_baseMap (x : LocalSpace H X) :
    (quotientUnitMap H X hH).baseMap x = TopologicalInduction.unit H x := by
  change TopologicalInduction.mk H (identityRepresentative H : G)
    ((identityRepresentative H)⁻¹ • x) = TopologicalInduction.mk H 1 x
  simpa using (TopologicalInduction.mk_subgroup_smul
    (H := H) (identityRepresentative H)⁻¹ (1 : G) x)

end Quotient

end Langlands.Analytic.AtlasInducedAction
