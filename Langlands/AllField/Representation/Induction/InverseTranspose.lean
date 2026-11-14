import Langlands.Representation.Induction.InverseTranspose
import Langlands.AllField.Representation.Induction.BlockFactors
import Langlands.AllField.Representation.Induction.OppositeParabolic
/-! Inverse-transpose transport of actual normalized block induction. -/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.AllField.Induction
open Langlands.Induction
open Langlands.AllField.Induction

universe uR uG uV


end Langlands.AllField.Induction

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV


end Langlands.AllField.GeneralLinear.BlockShape

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF
variable {F : Type uF} [Field F]
variable (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Transposition preserves the determinant, so inverse transpose inverts its normalized norm. -/
theorem determinantNorm_inverseTranspose (r : ℕ) (g : GeneralLinear r F) :
    T.determinantNorm r (GeneralLinear.inverseTranspose r F g) =
      (T.determinantNorm r g)⁻¹ := by
  have hd : GeneralLinear.determinant (GeneralLinear.inverseTranspose r F g) =
      (GeneralLinear.determinant g)⁻¹ := by
    rw [← map_inv]
    apply Units.ext
    exact Matrix.det_transpose _
  change T.normalizedAbsUnits _ = _
  rw [hd, map_inv]
  rfl

/-- Each determinant factor in the explicit upper modulus inverts, without changing block order. -/
theorem leviModulus_inverseTranspose (m : B.Levi F) :
    T.leviModulus B (fun i => GeneralLinear.inverseTranspose (B.size i) F (m i)) =
      (T.leviModulus B m)⁻¹ := by
  classical
  rw [T.leviModulus_apply, T.leviModulus_apply]
  simp only [T.determinantNorm_inverseTranspose, inv_pow, ← Finset.prod_inv_distrib,
    inv_div_inv, inv_div]

/-- The canonical positive square root respects the derived full-modulus inversion. -/
theorem leviHalfModulus_inverseTranspose (m : B.Levi F) :
    T.leviHalfModulus B (fun i => GeneralLinear.inverseTranspose (B.size i) F (m i)) =
      (T.leviHalfModulus B m)⁻¹ := by
  change (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
    ((Units.map NNReal.sqrtHom.toMonoidHom) (T.leviModulus B _)) = _
  rw [T.leviModulus_inverseTranspose, map_inv, map_inv]
  rfl

/-- The positive upper half modulus under inverse transpose is the opposite half modulus. -/
theorem parabolicHalfModulus_oppositeToUpperInverseTranspose
    (q : B.oppositeParabolic F) :
    T.parabolicHalfModulus B (B.oppositeToUpperInverseTranspose F q) =
      T.oppositeParabolicHalfModulus B q := by
  rw [parabolicHalfModulus_apply, oppositeParabolicHalfModulus_apply,
    ← T.leviHalfModulus_inverseTranspose]
  exact congrArg (T.leviHalfModulus B)
    (funext (B.leviProjection_oppositeToUpperInverseTranspose F q))

universe uV
variable {V : Fin B.length → Type uV}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- The actual normalized inducing actions agree on inverse-transposed lower elements. -/
theorem inverseTransposeProductInducing
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    (q : B.oppositeParabolic F) :
    twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F))
        (B.oppositeToUpperInverseTranspose F q) =
      twist (T.oppositeParabolicHalfModulus B)
        ((B.blockTensor (fun i => (σ i).comp
          (GeneralLinear.inverseTranspose (B.size i) F).toMonoidHom)).comp
            (B.oppositeLeviProjection F)) q := by
  apply LinearMap.ext
  intro v
  change (T.parabolicHalfModulus B (B.oppositeToUpperInverseTranspose F q) : ℂ) •
      B.blockTensor σ (B.leviProjection F
        (B.oppositeToUpperInverseTranspose F q)) v =
    (T.oppositeParabolicHalfModulus B q : ℂ) •
      B.blockTensor (fun i => (σ i).comp
        (GeneralLinear.inverseTranspose (B.size i) F).toMonoidHom)
          (B.oppositeLeviProjection F q) v
  rw [T.parabolicHalfModulus_oppositeToUpperInverseTranspose,
    B.blockTensor_leviProjection_inverseTranspose]

/-- Precomposition by inverse transpose transports normalized upper block induction
with pulled-back ambient action to normalized opposite induction of the pulled-back factors. -/
def inverseTransposeProductToOppositeEquiv
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation.Equiv
      ((T.normalizedProductInduced B σ).comp
        (GeneralLinear.inverseTranspose n F).toMonoidHom)
      (T.normalizedOppositeParabolicInduced B
        (B.blockTensor (fun i => (σ i).comp
          (GeneralLinear.inverseTranspose (B.size i) F).toMonoidHom))) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  exact Induction.precomposeSmoothInducedEquiv
    (GeneralLinear.inverseTransposeContinuous n F)
    (B.oppositeToUpperInverseTranspose F) (fun _ => rfl)
    (T.inverseTransposeProductInducing B σ)

@[simp] theorem inverseTransposeProductToOppositeEquiv_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F))))
    (x : GeneralLinear n F) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.oppositeParabolic F)
        (twist (T.oppositeParabolicHalfModulus B)
          ((B.blockTensor (fun i => (σ i).comp
            (GeneralLinear.inverseTranspose (B.size i) F).toMonoidHom)).comp
              (B.oppositeLeviProjection F)))
        (T.inverseTransposeProductToOppositeEquiv B σ f) x =
      Induction.eval (B.parabolic F)
        (twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F)))
        f (GeneralLinear.inverseTranspose n F x) := rfl

@[simp] theorem inverseTransposeProductToOppositeEquiv_symm_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    (h : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.oppositeParabolic F)
        (twist (T.oppositeParabolicHalfModulus B)
          ((B.blockTensor (fun i => (σ i).comp
            (GeneralLinear.inverseTranspose (B.size i) F).toMonoidHom)).comp
              (B.oppositeLeviProjection F))))
    (x : GeneralLinear n F) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.parabolic F)
        (twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F)))
        ((T.inverseTransposeProductToOppositeEquiv B σ).symm h) x =
      Induction.eval (B.oppositeParabolic F)
        (twist (T.oppositeParabolicHalfModulus B)
          ((B.blockTensor (fun i => (σ i).comp
            (GeneralLinear.inverseTranspose (B.size i) F).toMonoidHom)).comp
              (B.oppositeLeviProjection F)))
        h (GeneralLinear.inverseTranspose n F x) := rfl

section Stabilizers


end Stabilizers

end Langlands.LocalFieldData
