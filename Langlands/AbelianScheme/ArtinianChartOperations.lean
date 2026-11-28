import Langlands.AbelianScheme.ArtinianChartFamily
import Langlands.AlgebraicGeometry.ProductOpenCharts
import Langlands.AlgebraicGeometry.Deformation.ElementaryReductionProducts

/-! # Sums, conjugates and squares of chart families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open MonoidalCategory CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.ArtinianConstantCharts.Setting

open Langlands.AlgebraicGeometry.TwistedOpenGluing
open Langlands.AlgebraicGeometry.Deformation.AffineOpenQuotientSections

variable {R' R : Type u} [CommRing R'] [CommRing R] [IsLocalRing R'] {S : Setting R' R}
  {M : S.Model} {X : Over (Spec (CommRingCat.of R))} {e : M.E ⟶ X.left}

namespace ChartFamily

section Sum

variable (K₁ K₂ : ChartFamily M X e)

/-- The union of two chart families. -/
abbrev sum : ChartFamily M X e where
  L := K₁.L ⊕ K₂.L
  V := Sum.elim K₁.V K₂.V
  affine
    | .inl l => K₁.affine l
    | .inr l => K₂.affine l
  κ
    | .inl l => K₁.κ l
    | .inr l => K₂.κ l
  isOpenImmersion
    | .inl l => K₁.isOpenImmersion l
    | .inr l => K₂.isOpenImmersion l
  κ_base
    | .inl l => K₁.κ_base l
    | .inr l => K₂.κ_base l
  fibre
    | .inl l => K₁.fibre l
    | .inr l => K₂.fibre l

variable [IsArtinianRing R] [IsLocalRing R]

theorem sum_θS_inl (l m : K₁.L) : (K₁.sum K₂).θS (.inl l) (.inl m) = K₁.θS l m := rfl

theorem sum_θS_inr (l m : K₂.L) : (K₁.sum K₂).θS (.inr l) (.inr m) = K₂.θS l m := rfl

/-- A chosen lift of the transition from one chart of a union to another. -/
def sumLift₂ [IsArtinianRing R'] [IsSeparated M.Y.hom] [Smooth M.Y.hom] (l m : (K₁.sum K₂).L) :
    ((K₁.sum K₂).V l ⊓ (K₁.sum K₂).V m).toScheme ⟶ M.Y.left :=
  Classical.choose ((K₁.sum K₂).exists_lift₂ l m)

theorem sumLift₂_spec [IsArtinianRing R'] [IsSeparated M.Y.hom] [Smooth M.Y.hom]
    (l m : (K₁.sum K₂).L) :
    K₁.sumLift₂ K₂ l m ≫ M.Y.hom = ((K₁.sum K₂).V l ⊓ (K₁.sum K₂).V m).ι ≫ M.Y.hom ∧
      (K₁.sum K₂).res₂ l m ≫ K₁.sumLift₂ K₂ l m = (K₁.sum K₂).θS l m ≫ M.q :=
  Classical.choose_spec ((K₁.sum K₂).exists_lift₂ l m)

variable {K₁ K₂}

/-- Lifts on two chart families, extended to their union by chosen lifts across the two
families. -/
def Lifts.sum [IsArtinianRing R'] [IsSeparated M.Y.hom] [Smooth M.Y.hom]
    (D₁ : K₁.Lifts) (D₂ : K₂.Lifts) : (K₁.sum K₂).Lifts where
  θ l m := match l, m with
    | .inl l, .inl m => D₁.θ l m
    | .inr l, .inr m => D₂.θ l m
    | .inl l, .inr m => K₁.sumLift₂ K₂ (.inl l) (.inr m)
    | .inr l, .inl m => K₁.sumLift₂ K₂ (.inr l) (.inl m)
  overBase l m := match l, m with
    | .inl l, .inl m => D₁.overBase l m
    | .inr l, .inr m => D₂.overBase l m
    | .inl l, .inr m => (K₁.sumLift₂_spec K₂ (.inl l) (.inr m)).1
    | .inr l, .inl m => (K₁.sumLift₂_spec K₂ (.inr l) (.inl m)).1
  reduces l m := match l, m with
    | .inl l, .inl m => D₁.reduces l m
    | .inr l, .inr m => D₂.reduces l m
    | .inl l, .inr m => (K₁.sumLift₂_spec K₂ (.inl l) (.inr m)).2
    | .inr l, .inl m => (K₁.sumLift₂_spec K₂ (.inr l) (.inl m)).2

theorem Lifts.sum_θ_inl [IsArtinianRing R'] [IsSeparated M.Y.hom] [Smooth M.Y.hom]
    (D₁ : K₁.Lifts) (D₂ : K₂.Lifts) (l m : K₁.L) : (D₁.sum D₂).θ (.inl l) (.inl m) = D₁.θ l m :=
  rfl

theorem Lifts.sum_θ_inr [IsArtinianRing R'] [IsSeparated M.Y.hom] [Smooth M.Y.hom]
    (D₁ : K₁.Lifts) (D₂ : K₂.Lifts) (l m : K₂.L) : (D₁.sum D₂).θ (.inr l) (.inr m) = D₂.θ l m :=
  rfl

end Sum

end ChartFamily

section Conj

variable (M X e)

/-- Compatible automorphisms of a model, its base change, its residue fibre and the charted
scheme. -/
structure Model.Aut where
  αY : M.Y ≅ M.Y
  αS : M.YS ≅ M.YS
  αE : M.E ≅ M.E
  αX : X ≅ X
  hS : αS.hom ≫ M.q = M.q ≫ αY.hom.left
  hpS : αS.hom ≫ M.pS = M.pS
  hE : αE.hom ≫ M.iE = M.iE ≫ αS.hom
  hX : αE.hom ≫ e = e ≫ αX.hom.left

attribute [reassoc] Model.Aut.hS Model.Aut.hpS Model.Aut.hE Model.Aut.hX

variable {M X e} (a : M.Aut X e)

namespace Model.Aut

theorem hS_inv : a.αS.inv ≫ M.q = M.q ≫ a.αY.inv.left := by
  rw [Iso.inv_comp_eq, ← Category.assoc, a.hS, Category.assoc, ← Over.comp_left, Iso.hom_inv_id,
    Over.id_left, Category.comp_id]

theorem VT_preimage (U : M.Y.left.Opens) :
    M.VT (a.αY.hom.left ⁻¹ᵁ U) = a.αS.hom ⁻¹ᵁ M.VT U := by
  ext x
  change a.αY.hom.left (M.q x) ∈ U ↔ M.q (a.αS.hom x) ∈ U
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, a.hS]

theorem VT_preimage_inf (U U' : M.Y.left.Opens) :
    M.VT (a.αY.hom.left ⁻¹ᵁ U) ⊓ M.VT (a.αY.hom.left ⁻¹ᵁ U') ≤
      a.αS.hom ⁻¹ᵁ (M.VT U ⊓ M.VT U') := by
  rw [a.VT_preimage, a.VT_preimage]
  rfl

end Model.Aut

namespace ChartFamily

variable (K : ChartFamily M X e)

/-- The base change of the automorphism on the base change of an open. -/
abbrev conjRes (U : M.Y.left.Opens) :
    (M.VT (a.αY.hom.left ⁻¹ᵁ U)).toScheme ⟶ (M.VT U).toScheme :=
  a.αS.hom.resLE (M.VT U) (M.VT (a.αY.hom.left ⁻¹ᵁ U)) (a.VT_preimage U).le

/-- The base change of the automorphism on the base change of a double overlap. -/
abbrev conjRes₂ (U U' : M.Y.left.Opens) :
    (M.VT (a.αY.hom.left ⁻¹ᵁ U) ⊓ M.VT (a.αY.hom.left ⁻¹ᵁ U')).toScheme ⟶
      (M.VT U ⊓ M.VT U').toScheme :=
  a.αS.hom.resLE (M.VT U ⊓ M.VT U') _ (a.VT_preimage_inf U U')

/-- A chart family conjugated by compatible automorphisms. -/
abbrev conj : ChartFamily M X e where
  L := K.L
  V l := a.αY.hom.left ⁻¹ᵁ K.V l
  affine l := (K.affine l).preimage _
  κ l := conjRes a (K.V l) ≫ K.κ l ≫ a.αX.inv.left
  isOpenImmersion l := by
    unfold conjRes Scheme.Hom.resLE
    infer_instance
  κ_base l := by
    rw [Category.assoc, Category.assoc, Over.w a.αX.inv, K.κ_base, conjRes,
      Scheme.Hom.resLE_comp_ι_assoc, a.hpS]
  fibre l := by
    have h := K.κ_comp_of_fibre l
      (M.iE.resLE (M.VT (a.αY.hom.left ⁻¹ᵁ K.V l)) (M.iE ⁻¹ᵁ M.VT (a.αY.hom.left ⁻¹ᵁ K.V l))
        le_rfl ≫ conjRes a (K.V l))
      ((M.iE ⁻¹ᵁ M.VT (a.αY.hom.left ⁻¹ᵁ K.V l)).ι ≫ a.αE.hom) (by
        rw [Category.assoc, conjRes, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc,
          Category.assoc, a.hE])
    rw [← Category.assoc, ← Category.assoc, h, Category.assoc, Category.assoc, a.hX_assoc,
      ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.comp_id]

theorem conj_V (l : K.L) : (K.conj a).V l = a.αY.hom.left ⁻¹ᵁ K.V l := rfl

theorem conj_κ (l : K.L) : (K.conj a).κ l = conjRes a (K.V l) ≫ K.κ l ≫ a.αX.inv.left := rfl

variable [IsArtinianRing R] [IsLocalRing R]

theorem conj_lift (l m : K.L) :
    (K.conj a).lift l m ≫ conjRes a (K.V l) = conjRes₂ a (K.V l) (K.V m) ≫ K.lift l m := by
  have e₁ := (K.conj a).lift_κ l m
  rw [conj_κ, conj_κ] at e₁
  rw [← cancel_mono (K.κ l ≫ a.αX.inv.left)]
  simp only [Category.assoc]
  have h : M.YS.homOfLE (inf_le_right :
        M.VT (a.αY.hom.left ⁻¹ᵁ K.V l) ⊓ M.VT (a.αY.hom.left ⁻¹ᵁ K.V m) ≤ _) ≫
        conjRes a (K.V m) = conjRes₂ a (K.V l) (K.V m) ≫ M.YS.homOfLE inf_le_right := by
    rw [conjRes, conjRes₂, Scheme.Hom.map_resLE, Scheme.Hom.resLE_map]
  rw [e₁, lift_κ_assoc]
  exact (reassoc_of% h) _

/-- The transition maps of a conjugated chart family are the conjugated transition maps. -/
theorem conj_θS (l m : K.L) :
    (K.conj a).θS l m ≫ a.αS.hom = conjRes₂ a (K.V l) (K.V m) ≫ K.θS l m := by
  have e₁ : (M.VT (a.αY.hom.left ⁻¹ᵁ K.V l)).ι ≫ a.αS.hom =
      conjRes a (K.V l) ≫ (M.VT (K.V l)).ι := (Scheme.Hom.resLE_comp_ι _ _).symm
  change (K.conj a).lift l m ≫ (M.VT (a.αY.hom.left ⁻¹ᵁ K.V l)).ι ≫ a.αS.hom = _
  rw [e₁, ← Category.assoc, conj_lift, Category.assoc]
  rfl

theorem conj_θS_q (l m : K.L) :
    (K.conj a).θS l m ≫ M.q = conjRes₂ a (K.V l) (K.V m) ≫ K.θS l m ≫ M.q ≫ a.αY.inv.left := by
  have e₂ : (K.conj a).θS l m ≫ M.q = ((K.conj a).θS l m ≫ a.αS.hom) ≫ a.αS.inv ≫ M.q := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [e₂, conj_θS, a.hS_inv, Category.assoc]

/-- The automorphism on a double overlap of the model. -/
abbrev conjY₂ (U U' : M.Y.left.Opens) :
    (a.αY.hom.left ⁻¹ᵁ U ⊓ a.αY.hom.left ⁻¹ᵁ U').toScheme ⟶ (U ⊓ U').toScheme :=
  a.αY.hom.left.resLE (U ⊓ U') (a.αY.hom.left ⁻¹ᵁ U ⊓ a.αY.hom.left ⁻¹ᵁ U') le_rfl

omit [IsArtinianRing R] [IsLocalRing R] in
theorem conj_res₂ (l m : K.L) :
    (K.conj a).res₂ l m ≫ conjY₂ a (K.V l) (K.V m) =
      conjRes₂ a (K.V l) (K.V m) ≫ K.res₂ l m := by
  rw [← cancel_mono (K.V l ⊓ K.V m).ι]
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, a.hS]

/-- Conjugated lifts of transition maps. -/
def Lifts.conj (D : K.Lifts) : (K.conj a).Lifts where
  θ l m := conjY₂ a (K.V l) (K.V m) ≫ D.θ l m ≫ a.αY.inv.left
  overBase l m := by
    rw [Category.assoc, Category.assoc, Over.w a.αY.inv, D.overBase,
      Scheme.Hom.resLE_comp_ι_assoc, Over.w a.αY.hom]
  reduces l m := by
    rw [← Category.assoc, conj_res₂, Category.assoc, D.reduces_assoc, conj_θS_q]

theorem Lifts.conj_θ (D : K.Lifts) (l m : K.L) :
    (D.conj a).θ l m = conjY₂ a (K.V l) (K.V m) ≫ D.θ l m ≫ a.αY.inv.left := rfl

end ChartFamily

end Conj

end Langlands.AbelianScheme.ArtinianConstantCharts.Setting
