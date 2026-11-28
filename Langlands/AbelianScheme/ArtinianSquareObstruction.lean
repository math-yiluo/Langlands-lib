import Langlands.AbelianScheme.ArtinianSquareCharts
import Langlands.AlgebraicGeometry.Deformation.TransitionObstructionComap

/-! # The obstruction on the square of an abelian scheme through the first projection -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.ArtinianConstantCharts.Setting

open Langlands.AlgebraicGeometry.GroupSchemeShear
open Langlands.AlgebraicGeometry.Deformation
open Langlands.AlgebraicGeometry.Deformation.AffineOpenQuotientSections
open Langlands.AlgebraicGeometry.Deformation.ElementaryMorphismLifts
open Langlands.AlgebraicGeometry.Deformation.TransitionObstruction

variable {R' R : Type u} [CommRing R'] [CommRing R] [IsLocalRing R'] {S : Setting R' R}
  {B : AbelianScheme (Spec (CommRingCat.of R))} [IsArtinianRing R'] [IsArtinianRing R]
  [IsLocalRing R] (K : S.Charts B)

namespace Charts

variable (D : K.chartFamily.Lifts)

theorem squareV_inl_le_fst (a : K.J × K.J) :
    (K.squareLifts D).family.V (.inl a) ≤
      (fst (S.C B).X (S.C B).X).left ⁻¹ᵁ D.family.V a.1 :=
  fun _ hx ↦ hx.1

theorem squareV_inl_le_snd (a : K.J × K.J) :
    (K.squareLifts D).family.V (.inl a) ≤
      (snd (S.C B).X (S.C B).X).left ⁻¹ᵁ D.family.V a.2 :=
  fun _ hx ↦ hx.2

theorem prodV_le_fst (a : K.J × K.J) :
    (K.prodLifts D).family.V a ≤ (fst (S.C B).X (S.C B).X).left ⁻¹ᵁ D.family.V a.1 :=
  fun _ hx ↦ hx.1

theorem prodV_le_snd (a : K.J × K.J) :
    (K.prodLifts D).family.V a ≤ (snd (S.C B).X (S.C B).X).left ⁻¹ᵁ D.family.V a.2 :=
  fun _ hx ↦ hx.2

theorem squareV_inr_le (a : K.J × K.J) :
    (K.squareLifts D).family.V (.inr a) ≤
      (shear (S.C B).X).hom.left ⁻¹ᵁ (K.prodLifts D).family.V a :=
  le_rfl

theorem squareθ_inl_fst (a c : K.J × K.J) :
    (K.squareLifts D).family.θ (.inl a) (.inl c) ≫ (fst (S.C B).X (S.C B).X).left =
      (fst (S.C B).X (S.C B).X).left.resLE _ _
          (Family.le_preimage₂ _ _ _ (K.squareV_inl_le_fst D a) (K.squareV_inl_le_fst D c)) ≫
        D.family.θ a.1 c.1 :=
  ChartFamily.Lifts.prod_θ_fst (S.jB_over B) (S.jB_over B) D D a c

theorem prodθ_fst (a c : K.J × K.J) :
    (K.prodLifts D).family.θ a c ≫ (fst (S.C B).X (S.C B).X).left =
      (fst (S.C B).X (S.C B).X).left.resLE _ _
          (Family.le_preimage₂ _ _ _ (K.prodV_le_fst D a) (K.prodV_le_fst D c)) ≫
        D.family.θ a.1 c.1 :=
  ChartFamily.Lifts.prod_θ_fst (S.jB_over B) (S.jB_over B) D D a c

theorem prodθ_snd (a c : K.J × K.J) :
    (K.prodLifts D).family.θ a c ≫ (snd (S.C B).X (S.C B).X).left =
      (snd (S.C B).X (S.C B).X).left.resLE _ _
          (Family.le_preimage₂ _ _ _ (K.prodV_le_snd D a) (K.prodV_le_snd D c)) ≫
        D.family.θ a.2 c.2 :=
  ChartFamily.Lifts.prod_θ_snd (S.jB_over B) (S.jB_over B) D D a c

theorem squareθ_inr (a c : K.J × K.J) :
    (K.squareLifts D).family.θ (.inr a) (.inr c) ≫ (shear (S.C B).X).hom.left =
      (shear (S.C B).X).hom.left.resLE _ _
          (Family.le_preimage₂ _ _ _ (K.squareV_inr_le D a) (K.squareV_inr_le D c)) ≫
        (K.prodLifts D).family.θ a c := by
  change (ChartFamily.conjY₂ (S.shearAut B) _ _ ≫ (K.prodLifts D).θ a c ≫
    (shear (S.C B).X).inv.left) ≫ (shear (S.C B).X).hom.left = _
  rw [Category.assoc, Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  rfl

variable [Fact (maximalIdeal R' * RingHom.ker S.φ = ⊥)]
  (b : (S.target B).Coordinates (RingHom.ker S.φ)) (F : Reduction (S.C B).X (maximalIdeal R'))

/-- On triple overlaps of product charts, the obstruction of the square through the first
projection is the pullback of the obstruction of the abelian scheme along the first
projection. -/
theorem obstruction_inl (a c e : K.J × K.J)
    (j : Fin b.cotangentRank × Fin b.idealRank) :
    (K.squareLifts D).family.obstruction b (F.fibreProduct F) (K.squareLifts D).agrees
        (fst (S.C B).X (S.C B).X) (.inl a) (.inl c) (.inl e) j =
      (((F.fibreProduct F).map F (fst (S.C B).X (S.C B).X)).left.appLE _ _
        (Family.preimage_le_comap F (F.fibreProduct F) (Family.le_preimage₃ _ _ _
          (K.squareV_inl_le_fst D a) (K.squareV_inl_le_fst D c)
          (K.squareV_inl_le_fst D e)))).hom
        (D.family.obstruction b F D.agrees (𝟙 _) a.1 c.1 e.1 j) :=
  Family.obstruction_comap b F (F.fibreProduct F) (hl := K.squareV_inl_le_fst D a)
    (hm := K.squareV_inl_le_fst D c) (hn := K.squareV_inl_le_fst D e) D.agrees
    (K.squareLifts D).agrees (𝟙 _) _ (Category.comp_id _).symm (K.squareθ_inl_fst D a c) (K.squareθ_inl_fst D c e)
    (K.squareθ_inl_fst D a e) j

theorem prodObstruction_fst (a c e : K.J × K.J)
    (j : Fin b.cotangentRank × Fin b.idealRank) :
    (K.prodLifts D).family.obstruction b (F.fibreProduct F) (K.prodLifts D).agrees
        (fst (S.C B).X (S.C B).X) a c e j =
      (((F.fibreProduct F).map F (fst (S.C B).X (S.C B).X)).left.appLE _ _
        (Family.preimage_le_comap F (F.fibreProduct F) (Family.le_preimage₃ _ _ _
          (K.prodV_le_fst D a) (K.prodV_le_fst D c) (K.prodV_le_fst D e)))).hom
        (D.family.obstruction b F D.agrees (𝟙 _) a.1 c.1 e.1 j) :=
  Family.obstruction_comap b F (F.fibreProduct F) (hl := K.prodV_le_fst D a)
    (hm := K.prodV_le_fst D c) (hn := K.prodV_le_fst D e) D.agrees (K.prodLifts D).agrees (𝟙 _) _
    (Category.comp_id _).symm (K.prodθ_fst D a c) (K.prodθ_fst D c e) (K.prodθ_fst D a e) j

theorem prodObstruction_snd (a c e : K.J × K.J)
    (j : Fin b.cotangentRank × Fin b.idealRank) :
    (K.prodLifts D).family.obstruction b (F.fibreProduct F) (K.prodLifts D).agrees
        (snd (S.C B).X (S.C B).X) a c e j =
      (((F.fibreProduct F).map F (snd (S.C B).X (S.C B).X)).left.appLE _ _
        (Family.preimage_le_comap F (F.fibreProduct F) (Family.le_preimage₃ _ _ _
          (K.prodV_le_snd D a) (K.prodV_le_snd D c) (K.prodV_le_snd D e)))).hom
        (D.family.obstruction b F D.agrees (𝟙 _) a.2 c.2 e.2 j) :=
  Family.obstruction_comap b F (F.fibreProduct F) (hl := K.prodV_le_snd D a)
    (hm := K.prodV_le_snd D c) (hn := K.prodV_le_snd D e) D.agrees (K.prodLifts D).agrees (𝟙 _) _
    (Category.comp_id _).symm (K.prodθ_snd D a c) (K.prodθ_snd D c e) (K.prodθ_snd D a e) j

/-- On triple overlaps of sheared product charts, the obstruction of the square through the
first projection is the pullback, along the shear, of the difference of the obstructions of
the product charts through the two projections. -/
theorem obstruction_inr (a c e : K.J × K.J)
    (j : Fin b.cotangentRank × Fin b.idealRank) :
    (K.squareLifts D).family.obstruction b (F.fibreProduct F) (K.squareLifts D).agrees
        (fst (S.C B).X (S.C B).X) (.inr a) (.inr c) (.inr e) j =
      (((F.fibreProduct F).map (F.fibreProduct F) (shear (S.C B).X).hom).left.appLE _ _
        (Family.preimage_le_comap (F.fibreProduct F) (F.fibreProduct F)
          (Family.le_preimage₃ _ _ _ (K.squareV_inr_le D a) (K.squareV_inr_le D c)
          (K.squareV_inr_le D e)))).hom
        ((K.prodLifts D).family.obstruction b (F.fibreProduct F) (K.prodLifts D).agrees
            (fst (S.C B).X (S.C B).X) a c e j -
          (K.prodLifts D).family.obstruction b (F.fibreProduct F) (K.prodLifts D).agrees
            (snd (S.C B).X (S.C B).X) a c e j) := by
  rw [← Family.obstruction_mul_inv (S.C B).toGrp b]
  refine Family.obstruction_comap b (F.fibreProduct F) (F.fibreProduct F)
    (hl := K.squareV_inr_le D a) (hm := K.squareV_inr_le D c) (hn := K.squareV_inr_le D e)
    (K.prodLifts D).agrees (K.squareLifts D).agrees _ _ ?_ (K.squareθ_inr D a c)
    (K.squareθ_inr D c e) (K.squareθ_inr D a e) j
  rw [← div_eq_mul_inv, ← shear_inv_fst, Iso.hom_inv_id_assoc]

end Charts

end Langlands.AbelianScheme.ArtinianConstantCharts.Setting
