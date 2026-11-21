import Langlands.Geometry.FormalGroup.OrderActionCentralScalars
import Langlands.Geometry.FormalGroup.SplitOrderFormalSummand
import Langlands.Geometry.FormalGroup.SplitOrderSpecialTangent

/-! # Central scalars and special tangent characters of the actual division image -/

noncomputable section

universe u v w c k r

namespace Langlands.FormalGroup.ModuleLaw.OrderAction.DivisionImage

variable {O : Type u} [CommRing O]
variable {B : Type v} [Ring B] [Algebra O B]
variable {R : Type w} [CommRing R] [Algebra O R]
variable {C : Type c} [CommRing C] [Algebra C B] [Algebra C R]
variable {K : Type k} [CommRing K]
variable {L : Type r} [CommRing L]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {E : OrderAction (Bᵐᵒᵖ × B) M} (A : E.DivisionImage N)

/-- Structural action on the summand gives the structural tangent action on its formal law. -/
theorem structuralCentralTangent
    (h : E.HasStructuralDivisionTangent (algebraMap C B) (algebraMap C R))
    (a : C) (x : τ → R) :
    A.order.fiberTangent (RingHom.id R) (algebraMap C B a) x = algebraMap C R a • x := by
  let φ := RingHom.id R
  apply (A.tangentEquiv φ).injective
  rw [A.tangentEquiv_commutes, map_smul, h.action φ a]
  rfl

/-- The same division image with the formal module law over its central scalar ring. -/
def centralModule (h : E.HasStructuralDivisionTangent (algebraMap C B) (algebraMap C R)) :
    ModuleLaw C R τ := A.order.centralModule (A.structuralCentralTangent h)

/-- The induced division order action on the central formal module. -/
def centralOrder (h : E.HasStructuralDivisionTangent (algebraMap C B) (algebraMap C R)) :
    OrderAction B (A.centralModule h) := A.order.centralOrder (A.structuralCentralTangent h)

/-- The same character decomposition on the coordinate tangent of the actual image. -/
def tangentCharacterDecomposition {ι : L →+* B} {d : ℕ} {φ : R →+* K}
    (h : E.DivisionTangentCharacterDecomposition ι d φ) :
    A.order.TangentCharacterDecomposition ι d φ where
  characters := h.characters
  distinct := h.distinct
  coordinates := (A.tangentEquiv φ).trans h.coordinates
  diagonalizes a x i := by
    change h.coordinates (A.tangentEquiv φ (A.order.fiberTangent φ (ι a) x)) i = _
    rw [A.tangentEquiv_commutes, h.diagonalizes]
    rfl

/-- The geometry of each tangent representation survives the change of central scalars. -/
theorem centralOrder_hasGeometricTangentCharacters
    (hs : E.HasStructuralDivisionTangent (algebraMap C B) (algebraMap C R))
    {ι : L →+* B} {d : ℕ} (h : E.HasGeometricDivisionTangentCharacters.{u, v, w, k, r} ι d) :
    (A.centralOrder hs).HasGeometricTangentCharacters.{c, v, w, max w k, r} ι d := by
  intro κ _ _ φ
  obtain ⟨hκ⟩ := h κ φ
  let t := A.tangentCharacterDecomposition hκ
  exact ⟨⟨t.characters, t.distinct, t.coordinates, t.diagonalizes⟩⟩

end Langlands.FormalGroup.ModuleLaw.OrderAction.DivisionImage
