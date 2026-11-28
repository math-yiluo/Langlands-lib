import Langlands.AbelianScheme.ArtinianChartProducts
import Langlands.AbelianScheme.ArtinianAbelianCharts

/-! # Charts of the square of an abelian scheme by product charts and sheared product charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.ArtinianConstantCharts.Setting

open Langlands.AlgebraicGeometry.GroupSchemeShear
open Langlands.AlgebraicGeometry.Deformation.AffineOpenQuotientSections.Reduction (productMap)

variable {R' R : Type u} [CommRing R'] [CommRing R] [IsLocalRing R'] (S : Setting R' R)
  (B : AbelianScheme (Spec (CommRingCat.of R)))

/-- The base change of the constant group scheme to the thinner ring. -/
abbrev CSGrp : Grp (Over (Spec (CommRingCat.of R))) :=
  (Over.pullback S.t).mapGrp.obj (S.C B).toGrp

/-- The projection of the reduced constant scheme to the special fibre is multiplicative. -/
theorem isMulMap_ρ : IsMulMap (G := (S.CSGrp B).X) (H := (S.A₀ B).X) (S.t ≫ S.sσ) (S.ρ B)
    (S.isPullback_ρ B).w :=
  (isMulMap_pullback_fst S.t (S.C B).toGrp).comp (isMulMap_pullback_fst S.sσ (S.A₀ B).toGrp)

/-- The constant section of the reduced constant scheme is multiplicative. -/
theorem isMulMap_τ : IsMulMap (G := (S.A₀ B).X) (H := (S.CSGrp B).X) S.c (S.τ B) (S.τ_snd B) := by
  unfold IsMulMap
  apply (S.isPullback_ρ B).hom_ext
  · have h := S.isMulMap_ρ B
    unfold IsMulMap at h
    rw [Category.assoc, τ_ρ, Category.comp_id, Category.assoc, h, ← Category.assoc,
      productMap_comp]
    have e : productMap (Y' := (S.A₀ B).X) (Z' := (S.A₀ B).X) (Y := (S.A₀ B).X)
        (Z := (S.A₀ B).X) (S.τ B ≫ S.ρ B) (S.τ B ≫ S.ρ B) (S.c ≫ S.t ≫ S.sσ)
        (by rw [Category.assoc, (S.isPullback_ρ B).w, τ_snd_assoc])
        (by rw [Category.assoc, (S.isPullback_ρ B).w, τ_snd_assoc]) = 𝟙 _ := by
      apply productMap_ext <;> simp
    rw [e, Category.id_comp]
  · rw [Category.assoc, τ_snd, Category.assoc]
    change _ = _ ≫ μ[(S.CSGrp B).X].left ≫ (S.CSGrp B).X.hom
    rw [Over.w μ[(S.CSGrp B).X], Over.w_assoc μ[(S.A₀ B).X]]
    exact (productMap_hom _ _ _ _ _).symm

theorem jB_over : S.jB B ≫ B.X.hom = (S.modelB B).pE ≫ S.c := pullback.condition

/-- The square of the constant model. -/
abbrev modelB₂ : S.Model := (S.modelB B).prod (S.modelB B)

/-- The square of the inclusion of the special fibre. -/
abbrev jB₂ : (S.modelB₂ B).E ⟶ (B.X ⊗ B.X).left :=
  ChartFamily.prodE (S.jB_over B) (S.jB_over B)

/-- The shear automorphisms of the squares of the constant scheme, its reduction, its special
fibre and the abelian scheme. -/
def shearAut : (S.modelB₂ B).Aut (B.X ⊗ B.X) (S.jB₂ B) where
  αY := shear (S.C B).X
  αS := (Over.forget _).mapIso (shear (S.CSGrp B).X)
  αE := (Over.forget _).mapIso (shear (S.A₀ B).X)
  αX := shear B.X
  hS := ((isMulMap_pullback_fst S.t (S.C B).toGrp).shear_hom).symm
  hpS := Over.w (shear (S.CSGrp B).X).hom
  hE := ((S.isMulMap_τ B).shear_hom).symm
  hX := ((isMulMap_pullback_fst S.c B.toGrp).shear_hom).symm

instance smooth_modelB₂ : Smooth (S.modelB₂ B).Y.hom := by
  change Smooth (pullback.fst (S.C B).X.hom (S.C B).X.hom ≫ (S.C B).X.hom)
  infer_instance

instance isSeparated_modelB₂ : IsSeparated (S.modelB₂ B).Y.hom := by
  change IsSeparated (pullback.fst (S.C B).X.hom (S.C B).X.hom ≫ (S.C B).X.hom)
  infer_instance

namespace Charts

variable {S B} (K : S.Charts B)

/-- The product charts of the square. -/
abbrev prodFamily : ChartFamily (S.modelB₂ B) (B.X ⊗ B.X) (S.jB₂ B) :=
  K.chartFamily.prod K.chartFamily (S.jB_over B) (S.jB_over B)

/-- The product charts together with the sheared product charts of the square. -/
abbrev squareFamily : ChartFamily (S.modelB₂ B) (B.X ⊗ B.X) (S.jB₂ B) :=
  K.prodFamily.sum (K.prodFamily.conj (S.shearAut B))

variable [IsArtinianRing R] [IsLocalRing R] [IsArtinianRing R'] (D : K.chartFamily.Lifts)

/-- Products of lifts on the product charts. -/
abbrev prodLifts : K.prodFamily.Lifts := D.prod (S.jB_over B) (S.jB_over B) D

/-- Lifts on the charts of the square: products of lifts on the product charts, their shears
on the sheared product charts. -/
abbrev squareLifts : K.squareFamily.Lifts :=
  (K.prodLifts D).sum ((K.prodLifts D).conj (S.shearAut B))

end Charts

end Langlands.AbelianScheme.ArtinianConstantCharts.Setting
