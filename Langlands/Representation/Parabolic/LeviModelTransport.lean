import Langlands.Group.GL.ParabolicQuotientTopology
import Langlands.Representation.Smooth.FiniteLengthGrothendieckTransport

/-! Actual smooth and exact-K0 transports between the three GL Levi models. -/

noncomputable section

open CategoryTheory

namespace Langlands.Parabolic

universe uF uV

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Transport a smooth product-Levi action to its actual matrix subgroup. -/
def productToEmbeddedLevi :
    SmoothRep.{0, uF, uV} ℂ (B.Levi F) ⥤
      SmoothRep.{0, uF, uV} ℂ (B.leviSubgroup F) :=
  SmoothRep.pullbackFunctor (B.leviEquivContinuous F).symm

/-- Transport a smooth product-Levi action to the actual parabolic quotient. -/
def productToQuotientLevi :
    SmoothRep.{0, uF, uV} ℂ (B.Levi F) ⥤
      SmoothRep.{0, uF, uV} ℂ (B.parabolic F ⧸ B.unipotentRadical F) :=
  SmoothRep.pullbackFunctor (B.parabolicQuotientLeviContinuous F)

/-- Transport a smooth embedded-Levi action to the actual parabolic quotient. -/
def embeddedToQuotientLevi :
    SmoothRep.{0, uF, uV} ℂ (B.leviSubgroup F) ⥤
      SmoothRep.{0, uF, uV} ℂ (B.parabolic F ⧸ B.unipotentRadical F) :=
  SmoothRep.pullbackFunctor (B.parabolicQuotientEmbeddedLeviContinuous F)

@[simp] theorem productToEmbeddedLevi_obj_apply
    (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F))
    (m : B.leviSubgroup F) (v : A) :
    ((productToEmbeddedLevi B).obj A).representation m v =
      A.representation (B.leviProjection F (B.leviAsParabolic F m)) v := rfl

@[simp] theorem productToQuotientLevi_obj_mk
    (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F))
    (g : B.parabolic F) (v : A) :
    ((productToQuotientLevi B).obj A).representation (QuotientGroup.mk g) v =
      A.representation (B.leviProjection F g) v := rfl

@[simp] theorem embeddedToQuotientLevi_obj_mk
    (A : SmoothRep.{0, uF, uV} ℂ (B.leviSubgroup F))
    (g : B.parabolic F) (v : A) :
    ((embeddedToQuotientLevi B).obj A).representation (QuotientGroup.mk g) v =
      A.representation (B.leviEquiv F (B.leviProjection F g)) v := rfl

@[simp] theorem productToEmbeddedLevi_map_toLinearMap
    {A C : SmoothRep.{0, uF, uV} ℂ (B.Levi F)} (f : A ⟶ C) :
    (SmoothRep.hom ((productToEmbeddedLevi B).map f)).toLinearMap =
      (SmoothRep.hom f).toLinearMap := rfl

@[simp] theorem productToQuotientLevi_map_toLinearMap
    {A C : SmoothRep.{0, uF, uV} ℂ (B.Levi F)} (f : A ⟶ C) :
    (SmoothRep.hom ((productToQuotientLevi B).map f)).toLinearMap =
      (SmoothRep.hom f).toLinearMap := rfl

@[simp] theorem embeddedToQuotientLevi_map_toLinearMap
    {A C : SmoothRep.{0, uF, uV} ℂ (B.leviSubgroup F)} (f : A ⟶ C) :
    (SmoothRep.hom ((embeddedToQuotientLevi B).map f)).toLinearMap =
      (SmoothRep.hom f).toLinearMap := rfl

/-- The product and embedded models have equivalent full exact finite-length K0. -/
def embeddedLeviK0Equiv :
    SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, uV} ℂ (B.Levi F) ≃ₗ[ℤ]
      SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, uV} ℂ (B.leviSubgroup F) :=
  SmoothRep.FiniteLengthGrothendieckGroup.pullbackEquiv (B.leviEquivContinuous F).symm

/-- The product and quotient models have equivalent full exact finite-length K0. -/
def quotientLeviK0Equiv :
    SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, uV} ℂ (B.Levi F) ≃ₗ[ℤ]
      SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, uV} ℂ
        (B.parabolic F ⧸ B.unipotentRadical F) :=
  SmoothRep.FiniteLengthGrothendieckGroup.pullbackEquiv
    (B.parabolicQuotientLeviContinuous F)

/-- Exact-K0 transport from the embedded model to the quotient model. -/
def embeddedToQuotientLeviK0Equiv :
    SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, uV} ℂ (B.leviSubgroup F) ≃ₗ[ℤ]
      SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, uV} ℂ
        (B.parabolic F ⧸ B.unipotentRadical F) :=
  SmoothRep.FiniteLengthGrothendieckGroup.pullbackEquiv
    (B.parabolicQuotientEmbeddedLeviContinuous F)

theorem embeddedLeviK0Equiv_ofRepresentation
    (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F)) (hA : A.HasFiniteLength)
    (hOut : ((productToEmbeddedLevi B).obj A).HasFiniteLength) :
    embeddedLeviK0Equiv B (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
        ((productToEmbeddedLevi B).obj A) hOut :=
  SmoothRep.FiniteLengthGrothendieckGroup.pullback_ofRepresentation _ _ _ _

theorem quotientLeviK0Equiv_ofRepresentation
    (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F)) (hA : A.HasFiniteLength)
    (hOut : ((productToQuotientLevi B).obj A).HasFiniteLength) :
    quotientLeviK0Equiv B (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
        ((productToQuotientLevi B).obj A) hOut :=
  SmoothRep.FiniteLengthGrothendieckGroup.pullback_ofRepresentation _ _ _ _

theorem embeddedToQuotientLeviK0Equiv_ofRepresentation
    (A : SmoothRep.{0, uF, uV} ℂ (B.leviSubgroup F)) (hA : A.HasFiniteLength)
    (hOut : ((embeddedToQuotientLevi B).obj A).HasFiniteLength) :
    embeddedToQuotientLeviK0Equiv B
        (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation
        ((embeddedToQuotientLevi B).obj A) hOut :=
  SmoothRep.FiniteLengthGrothendieckGroup.pullback_ofRepresentation _ _ _ _

/-- Direct quotient transport equals transport through the actual embedded Levi. -/
theorem embeddedToQuotientLeviK0Equiv_comp :
    (embeddedToQuotientLeviK0Equiv.{uF, uV} (F := F) B).toLinearMap.comp
        (embeddedLeviK0Equiv B).toLinearMap =
      (quotientLeviK0Equiv B).toLinearMap := by
  rw [embeddedToQuotientLeviK0Equiv, embeddedLeviK0Equiv, quotientLeviK0Equiv]
  simp only [SmoothRep.FiniteLengthGrothendieckGroup.pullbackEquiv_toLinearMap]
  rw [← SmoothRep.FiniteLengthGrothendieckGroup.pullback_trans]
  congr 1
  apply ContinuousMulEquiv.ext
  intro q
  exact (B.leviEquivContinuous F).symm_apply_apply
    (B.parabolicQuotientLeviContinuous F q)

end Langlands.Parabolic
