import Langlands.Algebra.UniversalEnvelopingSymmetrization
import Langlands.Global.ArchimedeanEnvelopingDegreeConjugation

/-! # Actual equivariant archimedean enveloping symmetrization -/

noncomputable section
universe u
set_option autoImplicit false
open scoped TensorProduct

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

/-- The actual symmetric tensor power of the entire complexified Lie algebra. -/
abbrev LieSymmetricPower (d : ℕ) := Sym[ℂ]^d (ComplexLieAlgebra K n)

/-- Full-group adjoint conjugation applied to every symmetric tensor factor. -/
def lieSymmetricPowerConjugation (d : ℕ) (g : InfiniteAdelicGL K n) :
    LieSymmetricPower K n d ≃ₗ[ℂ] LieSymmetricPower K n d :=
  { Langlands.Algebra.SymmetricTensors.map (ι := Fin d)
      (complexLieConjugation K n g).toLinearMap with
    invFun := Langlands.Algebra.SymmetricTensors.map
      (complexLieConjugation K n g⁻¹).toLinearMap
    left_inv := by
      have h :
          (Langlands.Algebra.SymmetricTensors.map (ι := Fin d)
            (complexLieConjugation K n g⁻¹).toLinearMap).comp
            (Langlands.Algebra.SymmetricTensors.map
              (complexLieConjugation K n g).toLinearMap) = LinearMap.id := by
        apply Langlands.Algebra.SymmetricTensors.linearMap_ext
        intro x
        simp
      exact fun a => LinearMap.congr_fun h a
    right_inv := by
      have h :
          (Langlands.Algebra.SymmetricTensors.map (ι := Fin d)
            (complexLieConjugation K n g).toLinearMap).comp
            (Langlands.Algebra.SymmetricTensors.map
              (complexLieConjugation K n g⁻¹).toLinearMap) = LinearMap.id := by
        apply Langlands.Algebra.SymmetricTensors.linearMap_ext
        intro x
        simp
      exact fun a => LinearMap.congr_fun h a }

@[simp]
theorem lieSymmetricPowerConjugation_tprod (d : ℕ) (g : InfiniteAdelicGL K n)
    (x : Fin d → ComplexLieAlgebra K n) :
    lieSymmetricPowerConjugation K n d g (SymmetricPower.tprod ℂ x) =
      SymmetricPower.tprod ℂ (fun i => complexLieConjugation K n g (x i)) :=
  Langlands.Algebra.SymmetricTensors.map_tprod _ _

@[simp]
theorem lieSymmetricPowerConjugation_one (d : ℕ) :
    lieSymmetricPowerConjugation K n d 1 = LinearEquiv.refl ℂ _ := by
  apply LinearEquiv.toLinearMap_injective
  apply Langlands.Algebra.SymmetricTensors.linearMap_ext
  intro x
  simp

theorem lieSymmetricPowerConjugation_mul (d : ℕ) (g h : InfiniteAdelicGL K n) :
    lieSymmetricPowerConjugation K n d (g * h) =
      (lieSymmetricPowerConjugation K n d h).trans
        (lieSymmetricPowerConjugation K n d g) := by
  apply LinearEquiv.toLinearMap_injective
  apply Langlands.Algebra.SymmetricTensors.linearMap_ext
  intro x
  simp [complexLieConjugation_mul]

@[simp]
theorem lieSymmetricPowerConjugation_inv (d : ℕ) (g : InfiniteAdelicGL K n) :
    lieSymmetricPowerConjugation K n d g⁻¹ =
      (lieSymmetricPowerConjugation K n d g).symm := by
  apply LinearEquiv.ext
  intro a
  rfl

/-- The algebraic full-group representation on an actual symmetric tensor power. -/
def lieSymmetricPowerRepresentation (d : ℕ) :
    _root_.Representation ℂ (InfiniteAdelicGL K n) (LieSymmetricPower K n d) where
  toFun g := (lieSymmetricPowerConjugation K n d g).toLinearMap
  map_one' := by
    ext a : 1
    simp
  map_mul' g h := by
    ext a : 1
    exact LinearEquiv.congr_fun (lieSymmetricPowerConjugation_mul K n d g h) a

/-- Normalized symmetrization into the genuine archimedean enveloping algebra. -/
def envelopingSymmetrize (d : ℕ) :
    LieSymmetricPower K n d →ₗ[ℂ] EnvelopingAlgebra K n :=
  Langlands.Algebra.UniversalEnveloping.symmetrize ℂ (ComplexLieAlgebra K n) d

@[simp]
theorem envelopingSymmetrize_tprod {d : ℕ} (x : Fin d → ComplexLieAlgebra K n) :
    envelopingSymmetrize K n d (SymmetricPower.tprod ℂ x) =
      Langlands.Algebra.UniversalEnveloping.symmetricWord ℂ
        (ComplexLieAlgebra K n) d x :=
  Langlands.Algebra.UniversalEnveloping.symmetrize_tprod ℂ _ x

theorem envelopingSymmetrize_mem_degreeFiltration {d : ℕ}
    (a : LieSymmetricPower K n d) :
    envelopingSymmetrize K n d a ∈ envelopingDegreeFiltration K n d :=
  Langlands.Algebra.UniversalEnveloping.symmetrize_mem_degreeFiltration ℂ _ a

/-- Symmetrization with codomain restricted to the genuine degree piece. -/
def envelopingSymmetrizeDegree (d : ℕ) :
    LieSymmetricPower K n d →ₗ[ℂ] envelopingDegreeFiltration K n d :=
  (envelopingSymmetrize K n d).codRestrict _ (envelopingSymmetrize_mem_degreeFiltration K n)

@[simp]
theorem envelopingSymmetrizeDegree_coe {d : ℕ} (a : LieSymmetricPower K n d) :
    (envelopingSymmetrizeDegree K n d a : EnvelopingAlgebra K n) =
      envelopingSymmetrize K n d a := rfl

theorem envelopingSymmetrize_conjugation (d : ℕ) (g : InfiniteAdelicGL K n)
    (a : LieSymmetricPower K n d) :
    envelopingConjugation K n g (envelopingSymmetrize K n d a) =
      envelopingSymmetrize K n d (lieSymmetricPowerConjugation K n d g a) := by
  apply Langlands.Algebra.UniversalEnveloping.map_symmetrize ℂ
    (ComplexLieAlgebra K n) (envelopingConjugation K n g).toAlgHom
    (complexLieConjugation K n g).toLinearMap
  exact envelopingConjugation_generator K n g

theorem envelopingSymmetrizeDegree_conjugation (d : ℕ) (g : InfiniteAdelicGL K n)
    (a : LieSymmetricPower K n d) :
    envelopingDegreeConjugation K n d g (envelopingSymmetrizeDegree K n d a) =
      envelopingSymmetrizeDegree K n d (lieSymmetricPowerConjugation K n d g a) := by
  apply Subtype.ext
  exact envelopingSymmetrize_conjugation K n d g a

theorem envelopingSymmetrize_tprod_sub_orderedWord_mem {d : ℕ}
    (x : Fin d → ComplexLieAlgebra K n) :
    envelopingSymmetrize K n d (SymmetricPower.tprod ℂ x) -
        Langlands.Algebra.UniversalEnveloping.orderedWord ℂ
          (ComplexLieAlgebra K n) d x ∈ envelopingDegreeFiltration K n (d - 1) := by
  rw [envelopingSymmetrize_tprod]
  exact Langlands.Algebra.UniversalEnveloping.symmetricWord_sub_orderedWord_mem ℂ _ x

end Langlands.Global.ArchimedeanGL
