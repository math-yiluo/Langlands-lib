import Langlands.AllFieldBZ.Group.GL.ReverseBlocks
import Langlands.AllFieldBZ.Representation.Induction.BlockFactors
import Langlands.AllFieldBZ.Representation.Induction.OppositeParabolic
import Langlands.Representation.Induction.InverseTranspose

/-!
# All-field port of `Langlands.Representation.Induction.InverseTranspose`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Induction.InverseTranspose` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open scoped BigOperators
open scoped NNReal
namespace Langlands.AllFieldBZ.Induction
open Langlands.Induction
universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]
variable {P Q : Subgroup G} {σ : Representation R P V} {τ : Representation R Q V}

omit [IsTopologicalGroup G] in
private theorem _root_.Langlands.Induction.precompose_symm_subgroup (θ : G ≃ₜ* G) (e : Q ≃* P)
    (he : ∀ q : Q, (e q : G) = θ q) (p : P) :
    (e.symm p : G) = θ.symm p := by
  apply θ.injective
  rw [← he, e.apply_symm_apply, θ.apply_symm_apply]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem _root_.Langlands.Induction.precompose_symm_rep (e : Q ≃* P)
    (hστ : ∀ q : Q, σ (e q) = τ q) (p : P) : τ (e.symm p) = σ p := by
  rw [← hστ, e.apply_symm_apply]

end Langlands.AllFieldBZ.Induction
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
universe uF uV
variable {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n) (R : Type uF) [CommRing R]

variable {V : Fin B.length → Type uV}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

end Langlands.AllFieldBZ.GeneralLinear.BlockShape
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe uF
variable {F : LocalFieldPackage.{uF}}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Transposition preserves the determinant, so inverse transpose inverts its normalized norm. -/
theorem determinantNorm_inverseTranspose (r : ℕ) (g : GeneralLinear r F.Carrier) :
    T.determinantNorm r (GeneralLinear.inverseTranspose r F.Carrier g) =
      (T.determinantNorm r g)⁻¹ := by
  have hd : GeneralLinear.determinant (GeneralLinear.inverseTranspose r F.Carrier g) =
      (GeneralLinear.determinant g)⁻¹ := by
    rw [← map_inv]
    apply Units.ext
    exact Matrix.det_transpose _
  change T.normalizedAbsUnits _ = _
  rw [hd, map_inv]
  rfl

/-- Each determinant factor in the explicit upper modulus inverts, without changing block order. -/
theorem leviModulus_inverseTranspose (m : B.Levi F.Carrier) :
    T.leviModulus B (fun i => GeneralLinear.inverseTranspose (B.size i) F.Carrier (m i)) =
      (T.leviModulus B m)⁻¹ := by
  classical
  rw [T.leviModulus_apply, T.leviModulus_apply]
  simp only [T.determinantNorm_inverseTranspose, inv_pow, ← Finset.prod_inv_distrib,
    inv_div_inv, inv_div]

/-- The canonical positive square root respects the derived full-modulus inversion. -/
theorem leviHalfModulus_inverseTranspose (m : B.Levi F.Carrier) :
    T.leviHalfModulus B (fun i => GeneralLinear.inverseTranspose (B.size i) F.Carrier (m i)) =
      (T.leviHalfModulus B m)⁻¹ := by
  change (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
    ((Units.map NNReal.sqrtHom.toMonoidHom) (T.leviModulus B _)) = _
  rw [T.leviModulus_inverseTranspose, map_inv, map_inv]
  rfl

/-- The positive upper half modulus under inverse transpose is the opposite half modulus. -/
theorem parabolicHalfModulus_oppositeToUpperInverseTranspose
    (q : B.oppositeParabolic F.Carrier) :
    T.parabolicHalfModulus B (B.oppositeToUpperInverseTranspose F.Carrier q) =
      T.oppositeParabolicHalfModulus B q := by
  rw [parabolicHalfModulus_apply, oppositeParabolicHalfModulus_apply,
    ← T.leviHalfModulus_inverseTranspose]
  exact congrArg (T.leviHalfModulus B)
    (funext (B.leviProjection_oppositeToUpperInverseTranspose F.Carrier q))

universe uV
variable {V : Fin B.length → Type uV}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- The actual normalized inducing actions agree on inverse-transposed lower elements. -/
theorem inverseTransposeProductInducing
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (q : B.oppositeParabolic F.Carrier) :
    twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F.Carrier))
        (B.oppositeToUpperInverseTranspose F.Carrier q) =
      twist (T.oppositeParabolicHalfModulus B)
        ((B.blockTensor (fun i => (σ i).comp
          (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)).comp
            (B.oppositeLeviProjection F.Carrier)) q := by
  apply LinearMap.ext
  intro v
  change (T.parabolicHalfModulus B (B.oppositeToUpperInverseTranspose F.Carrier q) : ℂ) •
      B.blockTensor σ (B.leviProjection F.Carrier
        (B.oppositeToUpperInverseTranspose F.Carrier q)) v =
    (T.oppositeParabolicHalfModulus B q : ℂ) •
      B.blockTensor (fun i => (σ i).comp
        (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)
          (B.oppositeLeviProjection F.Carrier q) v
  rw [T.parabolicHalfModulus_oppositeToUpperInverseTranspose,
    B.blockTensor_leviProjection_inverseTranspose]

/-- Precomposition by inverse transpose transports normalized upper block induction
with pulled-back ambient action to normalized opposite induction of the pulled-back factors. -/
def inverseTransposeProductToOppositeEquiv
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation.Equiv
      ((T.normalizedProductInduced B σ).comp
        (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom)
      (T.normalizedOppositeParabolicInduced B
        (B.blockTensor (fun i => (σ i).comp
          (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom))) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  exact Induction.precomposeSmoothInducedEquiv
    (GeneralLinear.inverseTransposeContinuous n F.Carrier)
    (B.oppositeToUpperInverseTranspose F.Carrier) (fun _ => rfl)
    (T.inverseTransposeProductInducing B σ)

@[simp] theorem inverseTransposeProductToOppositeEquiv_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B)
          ((B.blockTensor σ).comp (B.leviProjection F.Carrier))))
    (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          ((B.blockTensor (fun i => (σ i).comp
            (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)).comp
              (B.oppositeLeviProjection F.Carrier)))
        (T.inverseTransposeProductToOppositeEquiv B σ f) x =
      Induction.eval (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))
        f (GeneralLinear.inverseTranspose n F.Carrier x) := rfl

@[simp] theorem inverseTransposeProductToOppositeEquiv_symm_eval
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (h : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          ((B.blockTensor (fun i => (σ i).comp
            (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)).comp
              (B.oppositeLeviProjection F.Carrier))))
    (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) ((B.blockTensor σ).comp (B.leviProjection F.Carrier)))
        ((T.inverseTransposeProductToOppositeEquiv B σ).symm h) x =
      Induction.eval (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          ((B.blockTensor (fun i => (σ i).comp
            (GeneralLinear.inverseTranspose (B.size i) F.Carrier).toMonoidHom)).comp
              (B.oppositeLeviProjection F.Carrier)))
        h (GeneralLinear.inverseTranspose n F.Carrier x) := rfl

section Stabilizers
variable (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))

end Stabilizers
end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
