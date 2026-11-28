import Langlands.AbelianScheme.ArtinianChartFamily
import Langlands.AlgebraicGeometry.Deformation.TransitionCoboundary
import Langlands.AlgebraicGeometry.Deformation.GroupTargetDifference

/-! # Constant charts of an abelian scheme as a chart family, and corrected lifts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.ArtinianConstantCharts.Setting

open Langlands.AlgebraicGeometry.TwistedOpenGluing
open Langlands.AlgebraicGeometry.Deformation
open Langlands.AlgebraicGeometry.Deformation.AffineOpenQuotientSections
open Langlands.AlgebraicGeometry.Deformation.ElementaryMorphismLifts
open Langlands.AlgebraicGeometry.Deformation.TransitionObstruction
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

variable {R' R : Type u} [CommRing R'] [CommRing R] [IsLocalRing R'] (S : Setting R' R)
  (B : AbelianScheme (Spec (CommRingCat.of R)))

/-- The constant abelian scheme over `R'` as a model of `B`: its base change to `R` and the
special fibre inside it. -/
abbrev modelB : S.Model where
  Y := (S.C B).X
  YS := S.CS B
  q := pullback.fst _ _
  pS := pullback.snd _ _
  isPullback_q := IsPullback.of_hasPullback _ _
  E := (S.A₀ B).X.left
  iE := S.τ B
  pE := (S.A₀ B).X.hom
  isPullback_iE := S.isPullback_τ B

instance isAffineHom_fst_sσ : IsAffineHom (pullback.fst (S.A₀ B).X.hom S.sσ) :=
  MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance

theorem isAffineOpen_V (U : B.X.left.Opens) (hU : IsAffineOpen U) : IsAffineOpen (S.V B U) :=
  (S.isAffineOpen_W B U hU).preimage _

theorem τ_preimage_VT_le (U : B.X.left.Opens) : S.τ B ⁻¹ᵁ S.VT B U ≤ S.W B U := by
  intro x hx
  have hx' : S.ρ B (S.τ B x) ∈ S.W B U := hx
  rwa [← Scheme.Hom.comp_apply, S.τ_ρ] at hx'

namespace Charts

variable {S B} (K : S.Charts B)

/-- The charts of `B` as a chart family of the constant model. -/
abbrev chartFamily : ChartFamily (S.modelB B) B.X (S.jB B) where
  L := K.J
  V i := S.V B (K.U i)
  affine i := S.isAffineOpen_V B _ (K.affine i)
  κ := K.κ
  κ_base := K.κ_base
  fibre i := by
    change (S.τ B).resLE (S.VT B (K.U i)) (S.τ B ⁻¹ᵁ S.VT B (K.U i)) le_rfl ≫ K.κ i =
      (S.τ B ⁻¹ᵁ S.VT B (K.U i)).ι ≫ S.jB B
    rw [← Scheme.Hom.map_resLE (S.τ B) (S.W_le_τ_preimage B (K.U i))
      (S.τ_preimage_VT_le B (K.U i)), Category.assoc, K.κ_fibre, Scheme.homOfLE_ι_assoc]

variable [IsArtinianRing R] [IsLocalRing R]

theorem chartFamily_θS (i j : K.J) : K.chartFamily.θS i j = K.θS i j := rfl

end Charts

section Corrected

/-- The constant abelian scheme as a target of lifts. -/
abbrev target : Target R' := Target.ofGroup (S.C B).toGrp

theorem ker_le_maximalIdeal [Nontrivial R] : RingHom.ker S.φ ≤ maximalIdeal R' :=
  IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top S.φ)

variable {S B} [IsArtinianRing R'] [IsArtinianRing R] [IsLocalRing R] (K : S.Charts B)
  [Fact (maximalIdeal R' * RingHom.ker S.φ = ⊥)]
  (b : (S.target B).Coordinates (RingHom.ker S.φ)) (F : Reduction (S.C B).X (maximalIdeal R'))
  (D : K.chartFamily.Lifts)

/-- If the obstruction of lifted transition maps of the charts, which are the inclusions on the
diagonal, is a Čech coboundary, then corrected lifts satisfy the cocycle condition. -/
theorem Charts.nonempty_liftedTransitions
    (hself : ∀ l, D.θ l l = (K.chartFamily.V l ⊓ K.chartFamily.V l).ι)
    (y : Fin b.cotangentRank × Fin b.idealRank →
      cochain F.obj.hom (D.family.cover F) (unitModule F.obj.left) 1)
    (hy : ∀ j, dCochain F.obj.hom (D.family.cover F) (unitModule F.obj.left) 1 (y j) =
      (D.family.cocycle b F D.agrees (𝟙 (S.C B).X) j :
        cochain F.obj.hom (D.family.cover F) (unitModule F.obj.left) 2)) :
    Nonempty K.LiftedTransitions := by
  have hI := S.ker_le_maximalIdeal
  let E := D.family.exactFamily hI b F y
  exact ⟨{
    θ := E.θ
    pointwise := E.pointwise
    self := D.family.exactFamily_self hI b F D.agrees y hy hself
    cocycle := D.family.exactFamily_comp hI b F D.agrees y hy
    overBase := E.overBase
    reduces := fun i j ↦
      ((S.modelB B).resTo_eq_of_agreeMod (D.family.affine₂ i j)
        (Scheme.Hom.preimage_inf _).symm
        (D.family.agree_corrected b F (D.family.pairValues b F y) i j)).symm.trans
        (D.reduces i j) }⟩

end Corrected

end Langlands.AbelianScheme.ArtinianConstantCharts.Setting
