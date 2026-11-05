import Langlands.GroupScheme.Descent.ClosedSubgroupIdeals
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine coordinates for defining-ideal descent -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace AffineIdealDescent

/-- Pushforward of an ideal sheaf on affine schemes contracts its global ideal. -/
theorem ideal_map_top {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (I : X.IdealSheafData) (f : X ⟶ Y) :
    (I.map f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top X⟩).comap f.appTop.hom := by
  simpa using I.ideal_map_of_isAffineHom f ⟨⊤, isAffineOpen_top Y⟩

/-- On affine schemes, the ideal-sheaf adjunction is the ordinary ideal
extension/contraction adjunction on global sections. -/
theorem comap_le_iff_map_top_le {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) (J : X.IdealSheafData) :
    I.comap f ≤ J ↔
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom ≤
        J.ideal ⟨⊤, isAffineOpen_top X⟩ := by
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
  constructor
  · intro h
    apply Ideal.map_le_iff_le_comap.mpr
    simpa only [ideal_map_top] using h ⟨⊤, isAffineOpen_top Y⟩
  · intro h
    apply Scheme.IdealSheafData.le_of_isAffine
    rw [ideal_map_top]
    exact Ideal.map_le_iff_le_comap.mp h

/-- Pullback of an affine ideal sheaf extends its ideal on global sections. -/
theorem ofIdealTop_comap {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (I : Ideal Γ(Y, ⊤)) (f : X ⟶ Y) :
    (Scheme.IdealSheafData.ofIdealTop I).comap f =
      Scheme.IdealSheafData.ofIdealTop (I.map f.appTop.hom) := by
  apply le_antisymm
  · rw [comap_le_iff_map_top_le]
    simp
  · apply Scheme.IdealSheafData.le_of_isAffine
    have h := (comap_le_iff_map_top_le
      (Scheme.IdealSheafData.ofIdealTop I) f
      ((Scheme.IdealSheafData.ofIdealTop I).comap f)).mp le_rfl
    simpa using h

/-- Algebraic extension of a global ideal supplies actual ideal-sheaf descent. -/
def ofGlobalIdeal {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (I : X.IdealSheafData) (J : Ideal Γ(Y, ⊤))
    (h : J.map f.appTop.hom = I.ideal ⟨⊤, isAffineOpen_top X⟩) :
    DefiningIdealDescent f I where
  ideal := Scheme.IdealSheafData.ofIdealTop J
  eq_comap := by
    rw [ofIdealTop_comap, h]
    exact (Scheme.IdealSheafData.equivOfIsAffine (X := X)).symm_apply_apply I |>.symm

end AffineIdealDescent

end Langlands.GroupScheme
