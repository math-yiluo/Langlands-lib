import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingBaseChange
import Langlands.AlgebraicGeometry.FlatEquivalenceRelation.Classifier
import Langlands.AlgebraicGeometry.Picard.LinearSystemFibres

/-! # The closed coordinate normalization locus for the ambient frame marks -/

noncomputable section

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

namespace FrameHilbert

variable {S T : Scheme.{u}} {m : ℕ} {R : Type v}

local notation "L" => RelativeProjectiveSpace.integralTwistOne m
local notation "coord" => Langlands.AlgebraicGeometry.twistOneCoordinate (ULift ℤ) m

/-- The basis and unit equations written on the marked maps to integral projective space. -/
def NormalizedMarks (ρ : Fin (m + 2) → R)
    (σ : R → (S ⟶ ProjectiveSpace (ULift.{u} ℤ) m)) : Prop :=
  (∀ j k : Fin (m + 1), k ≠ j → VanishesAlong L (σ (ρ j.castSucc)) (coord k)) ∧
    ∀ i k : Fin (m + 1),
      pullbackSection (σ (ρ (Fin.last (m + 1)))) (L).obj (coord i) =
        pullbackSection (σ (ρ (Fin.last (m + 1)))) (L).obj (coord k)

open SectionZeroIdeal (zeroIdeal)

/-- The ideal sheaf imposing the basis zeros and the equal coordinates of the last point. -/
def normalizationIdeal (ρ : Fin (m + 2) → R)
    (σ : R → (S ⟶ ProjectiveSpace (ULift.{u} ℤ) m)) : S.IdealSheafData :=
  (⨆ j : Fin (m + 1), ⨆ k : Fin (m + 1), ⨆ _ : k ≠ j,
    (zeroIdeal L (coord k)).comap (σ (ρ j.castSucc))) ⊔
  (⨆ i : Fin (m + 1), ⨆ k : Fin (m + 1),
    (zeroIdeal L (coord i - coord k)).comap (σ (ρ (Fin.last (m + 1)))))

private theorem sectionIdeal_le_ker_iff {X : Scheme.{u}} (B : LineBundle X)
    (s : GlobalSections B.obj) (q : S ⟶ X) (t : T ⟶ S) :
    (zeroIdeal B s).comap q ≤ t.ker ↔ VanishesAlong B (t ≫ q) s := by
  have hsec : SectionZeroIdeal.pullbackSection (t ≫ q) B s =
      pullbackSection (t ≫ q) B.obj s := by
    rw [pullbackSection_eq_sectionPullback, SectionZeroIdeal.pullbackSection]
    let M := (Scheme.Modules.pullback (t ≫ q)).obj B.obj
    change (M.presheaf.map (𝟙 (Opposite.op (⊤ : T.Opens)))) _ = _
    rw [M.presheaf.map_id]
    rfl
  rw [FlatEquivalenceRelation.comap_le_ker_iff, ← FlatEquivalenceRelation.comap_eq_bot_iff,
    SectionZeroIdeal.zeroIdeal_comap, hsec, VanishesAlong]
  constructor
  · intro h
    exact LinearSystemCechModule.eq_zero_of_zeroIdeal_eq_bot _ h
  · intro h
    rw [h, SectionZeroIdeal.zeroIdeal_zero]

private theorem vanishesAlong_sub_iff {X : Scheme.{u}} (B : LineBundle X)
    (q : T ⟶ X) (s₁ s₂ : GlobalSections B.obj) :
    VanishesAlong B q (s₁ - s₂) ↔
      pullbackSection q B.obj s₁ = pullbackSection q B.obj s₂ := by
  change (LinearSystem.pullbackSectionAddHom B.obj q) (s₁ - s₂) = 0 ↔ _
  rw [map_sub, sub_eq_zero]
  rfl

/-- The closed normalization locus represents the actual frame equations on arbitrary tests. -/
theorem factorsThrough_normalization_iff (ρ : Fin (m + 2) → R)
    (σ : R → (S ⟶ ProjectiveSpace (ULift.{u} ℤ) m)) (t : T ⟶ S) :
    (∃ t' : T ⟶ (normalizationIdeal ρ σ).subscheme,
      t' ≫ (normalizationIdeal ρ σ).subschemeι = t) ↔
      NormalizedMarks ρ (fun r => t ≫ σ r) := by
  rw [← FlatEquivalenceRelation.ker_le_ker_iff_exists, Scheme.IdealSheafData.ker_subschemeι]
  simp only [normalizationIdeal, sup_le_iff, iSup_le_iff, NormalizedMarks]
  refine and_congr (forall_congr' fun j => forall_congr' fun k => forall_congr' fun _ => ?_)
    (forall_congr' fun i => forall_congr' fun k => ?_)
  · exact sectionIdeal_le_ker_iff L (coord k) _ t
  · exact (sectionIdeal_le_ker_iff L (coord i - coord k) _ t).trans
      (vanishesAlong_sub_iff L _ _ _)

end FrameHilbert

open FrameHilbert

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n m : ℕ}
  {a : Datum P S g d n} {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m}
  {I : (RelativeProjectiveSpace S m).IdealSheafData}
  {σ : (Fin (2 * g) → ZMod n) → (S ⟶ ProjectiveSpace (ULift.{u} ℤ) m)}
  {ρ : Fin (m + 2) → Fin (2 * g) → ZMod n}

/-- When the embedding realizes the marks, the normalization equations are precisely
its relative basis and unit equations. -/
theorem Datum.Realizes.normalizedMarks_iff (h : a.Realizes ψ I σ) :
    NormalizedMarks ρ σ ↔
      (∀ j k : Fin (m + 1), k ≠ j →
        VanishesAlong (RelativeProjectiveSpace.twistOne S m)
          (a.torsionPoint (ρ j.castSucc) ≫ ψ)
          (RelativeProjectiveSpace.twistOneCoordinate S m k)) ∧
      ∀ i k : Fin (m + 1),
        pullbackSection (a.torsionPoint (ρ (Fin.last (m + 1))) ≫ ψ)
            (RelativeProjectiveSpace.twistOne S m).obj
            (RelativeProjectiveSpace.twistOneCoordinate S m i) =
          pullbackSection (a.torsionPoint (ρ (Fin.last (m + 1))) ≫ ψ)
            (RelativeProjectiveSpace.twistOne S m).obj
            (RelativeProjectiveSpace.twistOneCoordinate S m k) := by
  unfold NormalizedMarks RelativeProjectiveSpace.twistOne RelativeProjectiveSpace.twistOneCoordinate
  refine and_congr (forall_congr' fun j => forall_congr' fun k => forall_congr' fun _ => ?_)
    (forall_congr' fun i => forall_congr' fun k => ?_)
  · have hcomp := vanishesAlong_pullback_iff
      (a.torsionPoint (ρ j.castSucc) ≫ ψ) (RelativeProjectiveSpace.toIntegral S m)
      (RelativeProjectiveSpace.integralTwistOne m)
      (Langlands.AlgebraicGeometry.twistOneCoordinate (ULift.{u} ℤ) m k)
    rw [Category.assoc, h.2] at hcomp
    exact hcomp.symm
  · have hcomp := pullbackSection_pullback_eq_iff (RelativeProjectiveSpace.toIntegral S m)
      (a.torsionPoint (ρ (Fin.last (m + 1))) ≫ ψ)
      (Langlands.AlgebraicGeometry.twistOneCoordinate (ULift.{u} ℤ) m i)
      (Langlands.AlgebraicGeometry.twistOneCoordinate (ULift.{u} ℤ) m k)
    rw [Category.assoc, h.2] at hcomp
    exact hcomp.symm

/-- The marked maps of a frame embedding satisfy the ambient normalization equations. -/
theorem Datum.IsFrameEmbedding.normalizedMarks (h : a.IsFrameEmbedding ρ ψ)
    (hr : a.Realizes ψ I σ) : NormalizedMarks ρ σ :=
  hr.normalizedMarks_iff.mpr ⟨h.basis, h.unit⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel
