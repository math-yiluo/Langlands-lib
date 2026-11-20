import Langlands.Geometry.FormalGroup.NilpotentAlgebraTwist
import Langlands.Geometry.FormalGroup.PolarizedFramedCoefficientChange

/-! # Coefficient twist of the polarized affine class functor -/

noncomputable section

universe w

namespace Langlands.FormalGroup.PolarizedFramedAffinePoint

open CategoryTheory ModuleLaw Langlands.Shimura

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {prime : ℕ} [Fact prime.Prime]
variable {W : Type} [CommRing W] [Algebra ℤ_[prime] W] {π : W}
variable {A : Type w} [Ring A] [Algebra ℤ_[prime] A] {star : AlgebraInvolution ℤ_[prime] A}
variable {frame frame' frame'' : PolarizedOrderModule A star (ResidueRing W π) (prime : ℤ_[prime])}
variable {T U V : Nilp.{0, 0} W π}

namespace CoefficientChange

private theorem ofHom_source_coordinates (j : T ⟶ U) :
    (ofHom frame j).sourceIso.orderIso.hom.val.toHom.toCoordinateMap = CoordinateMap.id :=
  CoordinateMap.id_comp _

private theorem comp_source_coordinates (c : CoefficientChange frame frame' T U)
    (d : CoefficientChange frame' frame'' U V) :
    (c.comp d).sourceIso.orderIso.hom.val.toHom.toCoordinateMap =
      d.sourceIso.orderIso.hom.val.toHom.toCoordinateMap.comp
        (c.sourceIso.orderIso.hom.val.toHom.toCoordinateMap.map d.reduced.toRingHom) :=
  CoordinateMap.comp_id _

variable (σ : W ≃ₐ[ℤ_[prime]] W) (hπ : σ π = π)

local notation "Tσ" => Nilp.twistObj σ hπ T

/-- Move a class for the extended frame to the original frame on the twisted test. -/
def twist (frame : PolarizedOrderModule A star (ResidueRing W π) (prime : ℤ_[prime]))
    (T : Nilp.{0, 0} W π) :
    CoefficientChange (frame.map (Nilp.twistResidueEquiv σ hπ).toAlgHom) frame T
      (Nilp.twistObj σ hπ T) where
  scalar := (Nilp.twistScalarEquiv σ hπ T).toAlgHom
  reduced := (Nilp.twistReducedEquiv σ hπ T).toAlgHom
  quotientSquare := Nilp.twistReducedEquiv_quotientO σ hπ T
  sourceIso := by
    let f := frameCoefficientMap prime π T
    let g := frameCoefficientMap prime π (Nilp.twistObj σ hπ T)
    let β := (Nilp.twistReducedEquiv σ hπ T).toAlgHom
    let σ₀ := (Nilp.twistResidueEquiv σ hπ).toAlgHom
    have h : β.comp (f.comp σ₀) = (AlgHom.id ℤ_[prime] _).comp g :=
      (Nilp.twistReducedEquiv_residueCoefficientMap σ hπ T).trans (AlgHom.id_comp g).symm
    exact ((frame.mapCompIso σ₀ f).map β).trans
      ((frame.mapSquareIso (f.comp σ₀) β g (AlgHom.id ℤ_[prime] _) h).trans
        (frame.map g).mapIdIso)

/-- The inverse square uses the inverse equivalences on the same two test rings. -/
def untwist (frame : PolarizedOrderModule A star (ResidueRing W π) (prime : ℤ_[prime]))
    (T : Nilp.{0, 0} W π) :
    CoefficientChange frame (frame.map (Nilp.twistResidueEquiv σ hπ).toAlgHom)
      (Nilp.twistObj σ hπ T) T where
  scalar := (Nilp.twistScalarEquiv σ hπ T).symm.toAlgHom
  reduced := (Nilp.twistReducedEquiv σ hπ T).symm.toAlgHom
  quotientSquare := by
    apply AlgHom.ext
    intro x
    let α := Nilp.twistScalarEquiv σ hπ T
    let β := Nilp.twistReducedEquiv σ hπ T
    change β.symm (Nilp.quotientO ℤ_[prime] (Nilp.twistObj σ hπ T) x) =
      Nilp.quotientO ℤ_[prime] T (α.symm x)
    apply β.symm_apply_eq.mpr
    have h := DFunLike.congr_fun (Nilp.twistReducedEquiv_quotientO σ hπ T) (α.symm x)
    change β (Nilp.quotientO ℤ_[prime] T (α.symm x)) =
      Nilp.quotientO ℤ_[prime] (Nilp.twistObj σ hπ T) (α (α.symm x)) at h
    rw [α.apply_symm_apply] at h
    exact h.symm
  sourceIso := by
    let f := frameCoefficientMap prime π T
    let g := frameCoefficientMap prime π (Nilp.twistObj σ hπ T)
    let β := Nilp.twistReducedEquiv σ hπ T
    let σ₀ := (Nilp.twistResidueEquiv σ hπ).toAlgHom
    have h : β.symm.toAlgHom.comp g = f.comp σ₀ := by
      apply AlgHom.ext
      intro x
      exact β.symm_apply_eq.mpr
        (DFunLike.congr_fun (Nilp.twistReducedEquiv_residueCoefficientMap σ hπ T) x).symm
    exact frame.mapSquareIso g β.symm.toAlgHom σ₀ f h

private theorem twist_source_coordinates :
    (twist σ hπ frame T).sourceIso.orderIso.hom.val.toHom.toCoordinateMap = CoordinateMap.id := by
  change (CoordinateMap.id.comp CoordinateMap.id).comp
    (CoordinateMap.id.map (Nilp.twistReducedEquiv σ hπ T).toRingHom) = CoordinateMap.id
  rw [CoordinateMap.map_id, CoordinateMap.id_comp, CoordinateMap.id_comp]

private theorem untwist_source_coordinates :
    (untwist σ hπ frame T).sourceIso.orderIso.hom.val.toHom.toCoordinateMap = CoordinateMap.id :=
  rfl

private theorem twist_natural (j : T ⟶ U) :
    (twist σ hπ frame T).comp (ofHom frame (Nilp.twistHom σ hπ j)) =
      (ofHom (frame.map (Nilp.twistResidueEquiv σ hπ).toAlgHom) j).comp
        (twist σ hπ frame U) := by
  apply eq_of_maps (Nilp.twistScalarEquiv_natural σ hπ j)
    (Nilp.twistReducedEquiv_natural σ hπ j)
  simp only [comp_source_coordinates, ofHom_source_coordinates, twist_source_coordinates,
    CoordinateMap.map_id]

private theorem twist_untwist :
    (twist σ hπ frame T).comp (untwist σ hπ frame T) =
      ofHom (frame.map (Nilp.twistResidueEquiv σ hπ).toAlgHom) (𝟙 T) := by
  apply eq_of_maps
  · exact (AlgHom.ext (Nilp.twistScalarEquiv σ hπ T).symm_apply_apply).trans
      (Nilp.scalarMap_id ℤ_[prime] T).symm
  · exact (AlgHom.ext (Nilp.twistReducedEquiv σ hπ T).symm_apply_apply).trans
      (Nilp.reducedScalarMap_id ℤ_[prime] T).symm
  · rw [comp_source_coordinates, twist_source_coordinates, untwist_source_coordinates,
      CoordinateMap.map_id, CoordinateMap.id_comp, ofHom_source_coordinates]

private theorem untwist_twist :
    (untwist σ hπ frame T).comp (twist σ hπ frame T) = ofHom frame (𝟙 Tσ) := by
  apply eq_of_maps
  · exact (AlgHom.ext (Nilp.twistScalarEquiv σ hπ T).apply_symm_apply).trans
      (Nilp.scalarMap_id ℤ_[prime] Tσ).symm
  · exact (AlgHom.ext (Nilp.twistReducedEquiv σ hπ T).apply_symm_apply).trans
      (Nilp.reducedScalarMap_id ℤ_[prime] Tσ).symm
  · rw [comp_source_coordinates, untwist_source_coordinates, twist_source_coordinates,
      CoordinateMap.map_id, CoordinateMap.id_comp, ofHom_source_coordinates]

end CoefficientChange

variable (σ : W ≃ₐ[ℤ_[prime]] W) (hπ : σ π = π)

/-- For an affine test, twisting the frame is equivalent to twisting the structural map. -/
def twistFrameEquiv (frame : PolarizedOrderModule A star (ResidueRing W π) (prime : ℤ_[prime]))
    (T : Nilp.{0, 0} W π) :
    IsomorphismClass (frame := frame.map (Nilp.twistResidueEquiv σ hπ).toAlgHom) (T := T) ≃
      IsomorphismClass (frame := frame) (T := Nilp.twistObj σ hπ T) where
  toFun q := q.mapCoefficients (CoefficientChange.twist σ hπ frame T)
  invFun q := q.mapCoefficients (CoefficientChange.untwist σ hπ frame T)
  left_inv q := by
    change (q.mapCoefficients (CoefficientChange.twist σ hπ frame T)).mapCoefficients
      (CoefficientChange.untwist σ hπ frame T) = q
    rw [IsomorphismClass.mapCoefficients_comp, CoefficientChange.twist_untwist,
      IsomorphismClass.mapCoefficients_ofHom, IsomorphismClass.baseChange_id]
  right_inv q := by
    change (q.mapCoefficients (CoefficientChange.untwist σ hπ frame T)).mapCoefficients
      (CoefficientChange.twist σ hπ frame T) = q
    rw [IsomorphismClass.mapCoefficients_comp, CoefficientChange.untwist_twist,
      IsomorphismClass.mapCoefficients_ofHom, IsomorphismClass.baseChange_id]

/-- The coefficient twist comparison is natural in affine Nilp tests. -/
def twistFrameNatIso (frame : PolarizedOrderModule A star (ResidueRing W π) (prime : ℤ_[prime])) :
    classFunctor (frame.map (Nilp.twistResidueEquiv σ hπ).toAlgHom) ≅
      Nilp.twistFunctor σ hπ ⋙ classFunctor frame :=
  NatIso.ofComponents (fun T => (twistFrameEquiv σ hπ frame T).toIso) (by
    intro T U j
    ext q
    change (q.baseChange j).mapCoefficients (CoefficientChange.twist σ hπ frame U) =
      (q.mapCoefficients (CoefficientChange.twist σ hπ frame T)).baseChange
        (Nilp.twistHom σ hπ j)
    rw [← IsomorphismClass.mapCoefficients_ofHom, ← IsomorphismClass.mapCoefficients_ofHom,
      IsomorphismClass.mapCoefficients_comp, IsomorphismClass.mapCoefficients_comp,
      CoefficientChange.twist_natural])

end Langlands.FormalGroup.PolarizedFramedAffinePoint
