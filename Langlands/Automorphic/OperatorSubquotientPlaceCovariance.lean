import Langlands.Automorphic.OperatorSubquotientPlaceAction

/-! # Actual compact covariance of place actions on automorphic operator quotients -/

noncomputable section
universe uF

open scoped Classical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RK" => Matrix.unitaryGroup (Fin n) ℝ
local notation "CK" => Matrix.unitaryGroup (Fin n) ℂ

local instance quotientCovarianceRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance quotientCovarianceContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance quotientCovarianceSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance quotientCovarianceFormGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance quotientCovarianceStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance quotientCovarianceRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n)

private theorem realPlaceCompactRepresentation_eq (v : RP) (k : RK) :
    Q.realPlaceCompactRepresentation v k =
      Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.realPlaceFactor F n v k)) := rfl

private theorem complexPlaceCompactRepresentation_eq (v : CP) (k : CK) :
    Q.complexPlaceCompactRepresentation v k =
      Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n
        (ArchimedeanCompactFactors.complexPlaceFactor F n v k)) := rfl

/-- Conjugation by actual compact translation on all endomorphisms of the quotient. -/
def compactEndConjugation (k : standardInfiniteCompact F n) :
    Module.End ℂ Q.Space ≃ₐ[ℂ] Module.End ℂ Q.Space :=
  (Q.compactLinearEquiv k).conjAlgEquiv ℂ

@[simp] theorem compactEndConjugation_apply (k : standardInfiniteCompact F n)
    (A : Module.End ℂ Q.Space) (f : Q.Space) :
    Q.compactEndConjugation k A f =
      Q.compactRepresentation k (A (Q.compactRepresentation k⁻¹ f)) := rfl

/-- Conjugation fixes every finite adelic translation of the quotient. -/
theorem compactEndConjugation_finite (k : standardInfiniteCompact F n)
    (d : FiniteAdelicGL F n) :
    Q.compactEndConjugation k (Q.finiteRepresentation d) = Q.finiteRepresentation d := by
  apply LinearMap.ext
  intro f
  calc
    _ = Q.compactRepresentation k
        (Q.finiteRepresentation d (Q.compactRepresentation k⁻¹ f)) := rfl
    _ = Q.finiteRepresentation d
        (Q.compactRepresentation k (Q.compactRepresentation k⁻¹ f)) :=
      (Q.finiteRepresentation_compactRepresentation d k
        (Q.compactRepresentation k⁻¹ f)).symm
    _ = Q.finiteRepresentation d f :=
      congrArg (Q.finiteRepresentation d) ((Q.compactLinearEquiv k).apply_symm_apply f)

/-- On quotient enveloping operators, conjugation is the genuine global adjoint. -/
theorem compactEndConjugation_enveloping (k : standardInfiniteCompact F n)
    (a : EnvelopingAlgebra F n) :
    Q.compactEndConjugation k (Q.envelopingAction a) =
      Q.envelopingAction (envelopingConjugation F n k.val a) := by
  apply LinearMap.ext
  intro f
  calc
    _ = Q.compactRepresentation k
        (Q.envelopingAction a (Q.compactRepresentation k⁻¹ f)) := rfl
    _ = Q.envelopingAction (envelopingConjugation F n k.val a)
        (Q.compactRepresentation k (Q.compactRepresentation k⁻¹ f)) :=
      Q.compactRepresentation_envelopingAction k a (Q.compactRepresentation k⁻¹ f)
    _ = Q.envelopingAction (envelopingConjugation F n k.val a) f :=
      congrArg (Q.envelopingAction (envelopingConjugation F n k.val a))
        ((Q.compactLinearEquiv k).apply_symm_apply f)

/-- Actual orthogonal place translation conjugates quotient endomorphisms. -/
def realPlaceCompactEndConjugation (v : RP) (k : RK) :
    Module.End ℂ Q.Space ≃ₐ[ℂ] Module.End ℂ Q.Space :=
  Q.compactEndConjugation (realPlaceCompactInclusion F n v k)

def complexPlaceCompactEndConjugation (v : CP) (k : CK) :
    Module.End ℂ Q.Space ≃ₐ[ℂ] Module.End ℂ Q.Space :=
  Q.compactEndConjugation (complexPlaceCompactInclusion F n v k)

theorem realPlaceCompactEndConjugation_finite (v : RP) (k : RK)
    (d : FiniteAdelicGL F n) :
    Q.realPlaceCompactEndConjugation v k (Q.finiteRepresentation d) =
      Q.finiteRepresentation d :=
  Q.compactEndConjugation_finite (realPlaceCompactInclusion F n v k) d

theorem complexPlaceCompactEndConjugation_finite (v : CP) (k : CK)
    (d : FiniteAdelicGL F n) :
    Q.complexPlaceCompactEndConjugation v k (Q.finiteRepresentation d) =
      Q.finiteRepresentation d :=
  Q.compactEndConjugation_finite (complexPlaceCompactInclusion F n v k) d

/-- One-place compact translation is an automorphism of the finite quotient representation. -/
def realPlaceCompactFiniteEquivalence (v : RP) (k : RK) :
    Q.finiteRepresentation.Equiv Q.finiteRepresentation :=
  Q.compactFiniteEquivalence (realPlaceCompactInclusion F n v k)

def complexPlaceCompactFiniteEquivalence (v : CP) (k : CK) :
    Q.finiteRepresentation.Equiv Q.finiteRepresentation :=
  Q.compactFiniteEquivalence (complexPlaceCompactInclusion F n v k)

@[simp] theorem realPlaceCompactFiniteEquivalence_apply (v : RP) (k : RK) (f : Q.Space) :
    Q.realPlaceCompactFiniteEquivalence v k f = Q.realPlaceCompactRepresentation v k f := rfl

@[simp] theorem complexPlaceCompactFiniteEquivalence_apply (v : CP) (k : CK) (f : Q.Space) :
    Q.complexPlaceCompactFiniteEquivalence v k f =
      Q.complexPlaceCompactRepresentation v k f := rfl

/-- Conjugate the entire real-place quotient action by actual compact translation. -/
def realPlaceCompactConjugatedEnvelopingAction (v : RP) (k : RK) :
    RealPlaceEnvelopingAlgebra n →ₐ[ℂ] Module.End ℂ Q.Space :=
  (Q.realPlaceCompactEndConjugation v k).toAlgHom.comp (Q.realPlaceEnvelopingAction v)

def complexPlaceCompactConjugatedEnvelopingAction (v : CP) (k : CK) :
    ComplexPlaceEnvelopingAlgebra n →ₐ[ℂ] Module.End ℂ Q.Space :=
  (Q.complexPlaceCompactEndConjugation v k).toAlgHom.comp (Q.complexPlaceEnvelopingAction v)

/-- Full compact translation acts through the actual selected-place enveloping adjoint. -/
theorem compactRepresentation_realPlaceEnvelopingAction (p : ArchimedeanCompactFactors F n)
    (v : RP) (a : RealPlaceEnvelopingAlgebra n) (f : Q.Space) :
    Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (Q.realPlaceEnvelopingAction v a f) =
      Q.realPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℝ n (p.1 v) a)
        (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f) := by
  exact (Q.compactRepresentation_envelopingAction
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (realPlaceEnvelopingInclusion F n v a) f).trans
      (congrArg (fun b : EnvelopingAlgebra F n =>
        Q.envelopingAction b
          (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f))
        (envelopingConjugation_realInclusion F n p v a))

theorem compactRepresentation_complexPlaceEnvelopingAction (p : ArchimedeanCompactFactors F n)
    (v : CP) (a : ComplexPlaceEnvelopingAlgebra n) (f : Q.Space) :
    Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (Q.complexPlaceEnvelopingAction v a f) =
      Q.complexPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℂ n (p.2 v) a)
        (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f) := by
  exact (Q.compactRepresentation_envelopingAction
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (complexPlaceEnvelopingInclusion F n v a) f).trans
      (congrArg (fun b : EnvelopingAlgebra F n =>
        Q.envelopingAction b
          (Q.compactRepresentation (ArchimedeanCompactFactors.toStandardCompact F n p) f))
        (envelopingConjugation_complexInclusion F n p v a))

/-- The same full compact covariance as an equality of quotient endomorphisms. -/
theorem compactEndConjugation_realPlaceEnvelopingAction (p : ArchimedeanCompactFactors F n)
    (v : RP) (a : RealPlaceEnvelopingAlgebra n) :
    Q.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (Q.realPlaceEnvelopingAction v a) =
      Q.realPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℝ n (p.1 v) a) := by
  exact (Q.compactEndConjugation_enveloping
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (realPlaceEnvelopingInclusion F n v a)).trans
      (congrArg Q.envelopingAction (envelopingConjugation_realInclusion F n p v a))

theorem compactEndConjugation_complexPlaceEnvelopingAction (p : ArchimedeanCompactFactors F n)
    (v : CP) (a : ComplexPlaceEnvelopingAlgebra n) :
    Q.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n p)
        (Q.complexPlaceEnvelopingAction v a) =
      Q.complexPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℂ n (p.2 v) a) := by
  exact (Q.compactEndConjugation_enveloping
    (ArchimedeanCompactFactors.toStandardCompact F n p)
    (complexPlaceEnvelopingInclusion F n v a)).trans
      (congrArg Q.envelopingAction (envelopingConjugation_complexInclusion F n p v a))

/-- The two actual constructions of the conjugated real-place quotient action agree. -/
theorem realPlaceCompactConjugatedEnvelopingAction_eq (v : RP) (k : RK) :
    Q.realPlaceCompactConjugatedEnvelopingAction v k =
      (Q.realPlaceEnvelopingAction v).comp
        (unitaryMatrixEnvelopingConjugation ℝ n k).toAlgHom := by
  apply AlgHom.ext
  intro a
  change Q.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n
      (ArchimedeanCompactFactors.realPlaceFactor F n v k))
        (Q.realPlaceEnvelopingAction v a) =
      Q.realPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℝ n k a)
  simpa only [ArchimedeanCompactFactors.realPlaceFactor_fst, Pi.mulSingle_eq_same] using
    Q.compactEndConjugation_realPlaceEnvelopingAction
      (ArchimedeanCompactFactors.realPlaceFactor F n v k) v a

theorem complexPlaceCompactConjugatedEnvelopingAction_eq (v : CP) (k : CK) :
    Q.complexPlaceCompactConjugatedEnvelopingAction v k =
      (Q.complexPlaceEnvelopingAction v).comp
        (unitaryMatrixEnvelopingConjugation ℂ n k).toAlgHom := by
  apply AlgHom.ext
  intro a
  change Q.compactEndConjugation (ArchimedeanCompactFactors.toStandardCompact F n
      (ArchimedeanCompactFactors.complexPlaceFactor F n v k))
        (Q.complexPlaceEnvelopingAction v a) =
      Q.complexPlaceEnvelopingAction v (unitaryMatrixEnvelopingConjugation ℂ n k a)
  simpa only [ArchimedeanCompactFactors.complexPlaceFactor_snd, Pi.mulSingle_eq_same] using
    Q.compactEndConjugation_complexPlaceEnvelopingAction
      (ArchimedeanCompactFactors.complexPlaceFactor F n v k) v a

/-- Every real-place compact operator commutes with every complex-place enveloping operator. -/
theorem realPlaceCompactRepresentation_complexPlaceEnvelopingAction (v : RP) (w : CP) (k : RK)
    (a : ComplexPlaceEnvelopingAlgebra n) (f : Q.Space) :
    Q.realPlaceCompactRepresentation v k (Q.complexPlaceEnvelopingAction w a f) =
      Q.complexPlaceEnvelopingAction w a (Q.realPlaceCompactRepresentation v k f) := by
  simp only [realPlaceCompactRepresentation_eq]
  simpa only [ArchimedeanCompactFactors.realPlaceFactor_snd,
    unitaryMatrixEnvelopingConjugation_one, AlgEquiv.coe_refl, id_eq] using
    Q.compactRepresentation_complexPlaceEnvelopingAction
      (ArchimedeanCompactFactors.realPlaceFactor F n v k) w a f

theorem complexPlaceCompactRepresentation_realPlaceEnvelopingAction (v : CP) (w : RP) (k : CK)
    (a : RealPlaceEnvelopingAlgebra n) (f : Q.Space) :
    Q.complexPlaceCompactRepresentation v k (Q.realPlaceEnvelopingAction w a f) =
      Q.realPlaceEnvelopingAction w a (Q.complexPlaceCompactRepresentation v k f) := by
  simp only [complexPlaceCompactRepresentation_eq]
  simpa only [ArchimedeanCompactFactors.complexPlaceFactor_fst,
    unitaryMatrixEnvelopingConjugation_one, AlgEquiv.coe_refl, id_eq] using
    Q.compactRepresentation_realPlaceEnvelopingAction
      (ArchimedeanCompactFactors.complexPlaceFactor F n v k) w a f

/-- Distinct places of the same type also commute on every local algebra element. -/
theorem realPlaceCompactRepresentation_realPlaceEnvelopingAction_of_ne
    (v w : RP) (h : w ≠ v) (k : RK) (a : RealPlaceEnvelopingAlgebra n) (f : Q.Space) :
    Q.realPlaceCompactRepresentation v k (Q.realPlaceEnvelopingAction w a f) =
      Q.realPlaceEnvelopingAction w a (Q.realPlaceCompactRepresentation v k f) := by
  simp only [realPlaceCompactRepresentation_eq]
  simpa only [ArchimedeanCompactFactors.realPlaceFactor_fst, Pi.mulSingle_eq_of_ne h,
    unitaryMatrixEnvelopingConjugation_one, AlgEquiv.coe_refl, id_eq] using
    Q.compactRepresentation_realPlaceEnvelopingAction
      (ArchimedeanCompactFactors.realPlaceFactor F n v k) w a f

theorem complexPlaceCompactRepresentation_complexPlaceEnvelopingAction_of_ne
    (v w : CP) (h : w ≠ v) (k : CK) (a : ComplexPlaceEnvelopingAlgebra n) (f : Q.Space) :
    Q.complexPlaceCompactRepresentation v k (Q.complexPlaceEnvelopingAction w a f) =
      Q.complexPlaceEnvelopingAction w a (Q.complexPlaceCompactRepresentation v k f) := by
  simp only [complexPlaceCompactRepresentation_eq]
  simpa only [ArchimedeanCompactFactors.complexPlaceFactor_snd, Pi.mulSingle_eq_of_ne h,
    unitaryMatrixEnvelopingConjugation_one, AlgEquiv.coe_refl, id_eq] using
    Q.compactRepresentation_complexPlaceEnvelopingAction
      (ArchimedeanCompactFactors.complexPlaceFactor F n v k) w a f

end OperatorSubquotient
end Langlands.Automorphic
