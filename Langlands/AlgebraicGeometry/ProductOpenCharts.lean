import Mathlib.AlgebraicGeometry.PullbackCarrier
import Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity.ProductCover

/-! # Products of open charts of schemes over a common base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ProductOpenCharts

open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity (prodOpen)

variable {T X₁ X₂ Z₁ Z₂ : Scheme.{u}} {p₁ : X₁ ⟶ T} {p₂ : X₂ ⟶ T} (U₁ : X₁.Opens) (U₂ : X₂.Opens)

/-- The open of a fibre product lying over an open of each factor. -/
abbrev pOpen : (pullback p₁ p₂).Opens := prodOpen (pullback.fst p₁ p₂) (pullback.snd p₁ p₂) U₁ U₂

/-- The fibre product of two opens, mapped into the fibre product. -/
def incl : pullback (U₁.ι ≫ p₁) (U₂.ι ≫ p₂) ⟶ pullback p₁ p₂ :=
  pullback.map _ _ _ _ U₁.ι U₂.ι (𝟙 T) (by simp) (by simp)

instance : IsOpenImmersion (incl (p₁ := p₁) (p₂ := p₂) U₁ U₂) := by
  unfold incl
  infer_instance

@[reassoc (attr := simp)]
theorem incl_fst : incl (p₁ := p₁) (p₂ := p₂) U₁ U₂ ≫ pullback.fst p₁ p₂ =
    pullback.fst (U₁.ι ≫ p₁) (U₂.ι ≫ p₂) ≫ U₁.ι := by
  simp [incl]

@[reassoc (attr := simp)]
theorem incl_snd : incl (p₁ := p₁) (p₂ := p₂) U₁ U₂ ≫ pullback.snd p₁ p₂ =
    pullback.snd (U₁.ι ≫ p₁) (U₂.ι ≫ p₂) ≫ U₂.ι := by
  simp [incl]

theorem range_incl :
    Set.range (incl (p₁ := p₁) (p₂ := p₂) U₁ U₂) = (pOpen (p₁ := p₁) (p₂ := p₂) U₁ U₂ : Set _) := by
  rw [incl, Scheme.Pullback.range_map, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  rfl

/-- The open of the fibre product over two opens is the fibre product of the opens. -/
def prodIso : (pOpen (p₁ := p₁) (p₂ := p₂) U₁ U₂).toScheme ≅ pullback (U₁.ι ≫ p₁) (U₂.ι ≫ p₂) :=
  IsOpenImmersion.isoOfRangeEq (pOpen U₁ U₂).ι (incl U₁ U₂) (by
    rw [Scheme.Opens.range_ι, range_incl])

@[reassoc (attr := simp)]
theorem prodIso_hom_incl :
    (prodIso (p₁ := p₁) (p₂ := p₂) U₁ U₂).hom ≫ incl U₁ U₂ = (pOpen U₁ U₂).ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
theorem prodIso_hom_fst :
    (prodIso (p₁ := p₁) (p₂ := p₂) U₁ U₂).hom ≫ pullback.fst (U₁.ι ≫ p₁) (U₂.ι ≫ p₂) =
      (pullback.fst p₁ p₂).resLE U₁ (pOpen U₁ U₂) inf_le_left := by
  rw [← cancel_mono U₁.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← incl_fst,
    prodIso_hom_incl_assoc]

@[reassoc (attr := simp)]
theorem prodIso_hom_snd :
    (prodIso (p₁ := p₁) (p₂ := p₂) U₁ U₂).hom ≫ pullback.snd (U₁.ι ≫ p₁) (U₂.ι ≫ p₂) =
      (pullback.snd p₁ p₂).resLE U₂ (pOpen U₁ U₂) inf_le_right := by
  rw [← cancel_mono U₂.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← incl_snd,
    prodIso_hom_incl_assoc]

variable {z₁ : Z₁ ⟶ T} {z₂ : Z₂ ⟶ T} {U₁ U₂} (κ₁ : U₁.toScheme ⟶ Z₁) (κ₂ : U₂.toScheme ⟶ Z₂)
  (h₁ : κ₁ ≫ z₁ = U₁.ι ≫ p₁) (h₂ : κ₂ ≫ z₂ = U₂.ι ≫ p₂)

/-- The product of two charts over the base. -/
def prodChart : (pOpen (p₁ := p₁) (p₂ := p₂) U₁ U₂).toScheme ⟶ pullback z₁ z₂ :=
  (prodIso U₁ U₂).hom ≫ pullback.map _ _ _ _ κ₁ κ₂ (𝟙 T) (by simp [h₁]) (by simp [h₂])

instance [IsOpenImmersion κ₁] [IsOpenImmersion κ₂] : IsOpenImmersion (prodChart κ₁ κ₂ h₁ h₂) := by
  unfold prodChart
  infer_instance

@[reassoc (attr := simp)]
theorem prodChart_fst : prodChart κ₁ κ₂ h₁ h₂ ≫ pullback.fst z₁ z₂ =
    (pullback.fst p₁ p₂).resLE U₁ (pOpen U₁ U₂) inf_le_left ≫ κ₁ := by
  simp [prodChart]

@[reassoc (attr := simp)]
theorem prodChart_snd : prodChart κ₁ κ₂ h₁ h₂ ≫ pullback.snd z₁ z₂ =
    (pullback.snd p₁ p₂).resLE U₂ (pOpen U₁ U₂) inf_le_right ≫ κ₂ := by
  simp [prodChart]

end Langlands.AlgebraicGeometry.ProductOpenCharts
