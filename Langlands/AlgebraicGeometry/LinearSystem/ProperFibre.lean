import Langlands.AlgebraicGeometry.LinearSystem.RelativeMorphism
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.Geometry
import Langlands.AlgebraicGeometry.ProperFibreFiniteSpreading

/-! # Finiteness of relative linear systems near a proper fibre -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits AlgebraicGeometry
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.LinearSystem

variable {X S : Scheme.{u}} {L : LineBundle X} {n : ℕ}
  {σ : Fin (n + 1) → GlobalSections L.obj}

/-- The actual map between fibres induced by a relative linear system. -/
def relativeFibreLinearSystemMap (p : X ⟶ S)
    (hσ : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (σ i)) (s : S) :
    (relativeLinearSystemMap p hσ ≫ RelativeProjectiveSpace.toBase S n).fiber s ⟶
      (RelativeProjectiveSpace.toBase S n).fiber s :=
  baseFibreMap (relativeLinearSystemMap p hσ) (RelativeProjectiveSpace.toBase S n) s

/-- The induced fibre map is affine if each fibre section generation open is affine. -/
lemma isAffineHom_relativeFibreLinearSystemMap (p : X ⟶ S)
    (hσ : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (σ i)) (s : S)
    (hA : ∀ i, IsAffineOpen (p.fiberι s ⁻¹ᵁ trivializationOpen L.obj (σ i))) :
    IsAffineHom (relativeFibreLinearSystemMap p hσ s) := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro y
  have hy : (RelativeProjectiveSpace.toBase S n).fiberι s y ∈
      (⨆ i, RelativeProjectiveSpace.coordinateOpen S n i) := by
    rw [RelativeProjectiveSpace.iSup_coordinateOpen]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  refine ⟨(RelativeProjectiveSpace.toBase S n).fiberι s ⁻¹ᵁ
    RelativeProjectiveSpace.coordinateOpen S n i, hi,
    RelativeProjectiveSpace.isAffineOpen_fiber_coordinateOpen S n s i, ?_⟩
  change IsAffineOpen (baseFibreMap (relativeLinearSystemMap p hσ)
    (RelativeProjectiveSpace.toBase S n) s ⁻¹ᵁ
      ((RelativeProjectiveSpace.toBase S n).fiberι s ⁻¹ᵁ
        RelativeProjectiveSpace.coordinateOpen S n i))
  rw [← Scheme.Hom.comp_preimage, baseFibreMap_fiberι, Scheme.Hom.comp_preimage,
    relativeLinearSystemMap_preimage, relativeLinearSystemMap_toBase]
  exact hA i

/-- Properness of the source family makes this affine fibre map finite. -/
lemma isFinite_relativeFibreLinearSystemMap (p : X ⟶ S) [IsProper p]
    (hσ : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (σ i)) (s : S)
    (hA : ∀ i, IsAffineOpen (p.fiberι s ⁻¹ᵁ trivializationOpen L.obj (σ i))) :
    IsFinite (relativeFibreLinearSystemMap p hσ s) := by
  have : IsAffineHom (relativeFibreLinearSystemMap p hσ s) :=
    isAffineHom_relativeFibreLinearSystemMap p hσ s hA
  have : IsProper (relativeLinearSystemMap p hσ ≫ RelativeProjectiveSpace.toBase S n) := by
    simpa only [relativeLinearSystemMap_toBase] using inferInstanceAs (IsProper p)
  have : IsProper (relativeLinearSystemMap p hσ) :=
    .of_comp _ (RelativeProjectiveSpace.toBase S n)
  have : IsProper ((RelativeProjectiveSpace.toBase S n).fiberToSpecResidueField s) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField]
    infer_instance
  have : IsProper (baseFibreMap (relativeLinearSystemMap p hσ)
      (RelativeProjectiveSpace.toBase S n) s) := by
    have he : baseFibreMap (relativeLinearSystemMap p hσ)
        (RelativeProjectiveSpace.toBase S n) s ≫
        (RelativeProjectiveSpace.toBase S n).fiberToSpecResidueField s =
        (relativeLinearSystemMap p hσ ≫ RelativeProjectiveSpace.toBase S n).fiberToSpecResidueField s := by
      simp [baseFibreMap, Scheme.Hom.fiberToSpecResidueField]
    have : IsProper (baseFibreMap (relativeLinearSystemMap p hσ)
        (RelativeProjectiveSpace.toBase S n) s ≫
        (RelativeProjectiveSpace.toBase S n).fiberToSpecResidueField s) := by
      rw [he]
      dsimp [Scheme.Hom.fiberToSpecResidueField]
      infer_instance
    exact .of_comp _ ((RelativeProjectiveSpace.toBase S n).fiberToSpecResidueField s)
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨this, inferInstance⟩

/-- A generating linear system with affine section opens on a proper fibre
is finite over an affine neighbourhood of the base point. -/
lemma exists_isFinite_relativeLinearSystemMap_restrict (p : X ⟶ S) [IsProper p]
    (hσ : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (σ i)) (s : S)
    (hA : ∀ i, IsAffineOpen (p.fiberι s ⁻¹ᵁ trivializationOpen L.obj (σ i))) :
    ∃ V : S.Opens, s ∈ V ∧ IsAffineOpen V ∧
      IsFinite (relativeLinearSystemMap p hσ ∣_
        (RelativeProjectiveSpace.toBase S n ⁻¹ᵁ V)) := by
  have : IsProper (relativeLinearSystemMap p hσ ≫ RelativeProjectiveSpace.toBase S n) := by
    simpa only [relativeLinearSystemMap_toBase] using inferInstanceAs (IsProper p)
  have : IsFinite (baseFibreMap (relativeLinearSystemMap p hσ)
      (RelativeProjectiveSpace.toBase S n) s) :=
    isFinite_relativeFibreLinearSystemMap p hσ s hA
  exact exists_isFinite_morphismRestrict_of_finite_baseFibreMap
    (relativeLinearSystemMap p hσ) (RelativeProjectiveSpace.toBase S n) s

end Langlands.AlgebraicGeometry.LinearSystem
