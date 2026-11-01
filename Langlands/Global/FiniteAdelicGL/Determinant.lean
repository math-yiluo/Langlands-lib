import Langlands.Global.FiniteAdelicGL.LocalFactor

/-! # Determinants and the actual finite adelic factor maps -/

noncomputable section
universe uF
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

namespace FiniteAdelicGL

/-- The continuous determinant in the actual finite idele group. -/
def determinant : FiniteAdelicGL F n →ₜ* FiniteIdeles F where
  __ := Matrix.GeneralLinearGroup.det
  continuous_toFun := Matrix.GeneralLinearGroup.continuous_det

/-- Evaluation of the finite determinant is the determinant of the local matrix. -/
theorem determinant_localProjection (v : FinitePlace F) (g : FiniteAdelicGL F n) :
    Matrix.GeneralLinearGroup.det (localProjection F n v g) =
      Units.map (RestrictedProduct.evalRingHom (fun w : FinitePlace F =>
        FiniteCompletion F w) v).toMonoidHom (determinant F n g) :=
  Matrix.GeneralLinearGroup.map_det _ g

/-- At every finite place the determinant of a singleton matrix is the singleton determinant. -/
theorem determinant_localInclusion (v : FinitePlace F) (g : FiniteLocalGL F n v) :
    determinant F n (localInclusion F n v g) =
      Units.map (IsDedekindDomain.FiniteAdeleRing.ofAdicCompletion F v)
        (Matrix.GeneralLinearGroup.det g) := by
  apply Units.ext
  apply IsDedekindDomain.FiniteAdeleRing.ext
  intro w
  have hd := congrArg Units.val
    (determinant_localProjection F n w (localInclusion F n v g))
  by_cases hw : w = v
  · subst w
    rw [localProjection_localInclusion] at hd
    change (Matrix.GeneralLinearGroup.det g).val =
      (determinant F n (localInclusion F n v g)).val v at hd
    change (determinant F n (localInclusion F n v g)).val v =
      Pi.mulSingle v (Matrix.GeneralLinearGroup.det g).val v
    simpa only [Pi.mulSingle_eq_same] using hd.symm
  · rw [localProjection_localInclusion_of_ne F n v w hw, map_one] at hd
    change (1 : FiniteCompletion F w) =
      (determinant F n (localInclusion F n v g)).val w at hd
    change (determinant F n (localInclusion F n v g)).val w =
      Pi.mulSingle v (Matrix.GeneralLinearGroup.det g).val w
    simpa only [Pi.mulSingle_eq_of_ne hw] using hd.symm

end FiniteAdelicGL

namespace AdelicGL

/-- Inserting the finite matrix factor inserts its determinant as a finite idele. -/
theorem determinant_ofFinite (g : FiniteAdelicGL F n) :
    determinant F n (ofFinite F n g) =
      finiteIdelesInclusion F (FiniteAdelicGL.determinant F n g) := by
  apply Units.ext
  apply Prod.ext
  · change (RingHom.fst (InfiniteAdeles F) (FiniteAdeles F))
      (Matrix.det (ofFinite F n g).val) = 1
    rw [RingHom.map_det]
    change Matrix.det (1 : Matrix (Fin n) (Fin n) (InfiniteAdeles F)) = 1
    exact Matrix.det_one
  · change (RingHom.snd (InfiniteAdeles F) (FiniteAdeles F))
      (Matrix.det (ofFinite F n g).val) = Matrix.det g.val
    rw [RingHom.map_det]
    rfl

/-- Full adelic determinant commutes with the actual identity-supported local insertion. -/
theorem determinant_ofFinite_localInclusion (v : FinitePlace F)
    (g : FiniteLocalGL F n v) :
    determinant F n (ofFinite F n (FiniteAdelicGL.localInclusion F n v g)) =
      finiteIdeleInclusion F v (Matrix.GeneralLinearGroup.det g) := by
  rw [determinant_ofFinite, FiniteAdelicGL.determinant_localInclusion]
  apply Units.ext
  rfl

end AdelicGL
end Langlands.Global
