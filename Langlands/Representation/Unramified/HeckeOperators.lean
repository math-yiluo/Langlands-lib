import Langlands.Representation.Unramified.PrincipalSeries
import Langlands.Representation.Hecke.DoubleCoset
import Langlands.Representation.Whittaker.Iwasawa
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Actual spherical Hecke operators for the standard diagonal double cosets -/

noncomputable section

namespace Langlands.Unramified

open Correspondence MeasureTheory MeasureTheory.Measure

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance heckeFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance heckeFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance heckeFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance heckeGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopology n
local instance heckeGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopologicalGroup n
local instance heckeGeneralLinearT2 (n : ℕ) : T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearT2Space n
local instance heckeGeneralLinearMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance heckeGeneralLinearBorel (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) :=
  ⟨rfl⟩

/-- The existing spherical subgroup, with its actual open topology. -/
def sphericalOpenSubgroup (r : ℕ) : OpenSubgroup (GeneralLinear (r + 1) F.Carrier) where
  toSubgroup := sphericalSubgroup F r
  isOpen' := by
    change IsOpen (Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r :
      Set (GeneralLinear (r + 1) F.Carrier))
    rw [← Conductor.levelSubgroup_zero]
    exact (Conductor.levelOpenSubgroup F.Carrier r 0).isOpen

@[simp] theorem sphericalOpenSubgroup_toSubgroup (r : ℕ) :
    (sphericalOpenSubgroup F r).toSubgroup = sphericalSubgroup F r := rfl

theorem sphericalOpenSubgroup_isCompact (r : ℕ) :
    IsCompact (sphericalOpenSubgroup F r : Set (GeneralLinear (r + 1) F.Carrier)) := by
  change IsCompact (Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer r :
    Set (GeneralLinear (r + 1) F.Carrier))
  rw [← Conductor.levelSubgroup_zero]
  exact Conductor.isCompact_levelOpenSubgroup F.Carrier r 0

/-- The genuine Haar measure giving the existing spherical subgroup mass one. -/
def sphericalHaar (r : ℕ) : Measure (GeneralLinear (r + 1) F.Carrier) :=
  RankinSelberg.normalizedCompactOpenHaar (sphericalOpenSubgroup F r)
    (sphericalOpenSubgroup_isCompact F r)

instance sphericalHaar_isHaar (r : ℕ) : (sphericalHaar F r).IsHaarMeasure :=
  RankinSelberg.normalizedCompactOpenHaar_isHaar _ _

@[simp] theorem sphericalHaar_self (r : ℕ) :
    sphericalHaar F r (sphericalOpenSubgroup F r : Set (GeneralLinear (r + 1) F.Carrier)) = 1 :=
  RankinSelberg.normalizedCompactOpenHaar_self _ _

@[simp] theorem sphericalHaar_real_self (r : ℕ) :
    (sphericalHaar F r).real (sphericalOpenSubgroup F r :
      Set (GeneralLinear (r + 1) F.Carrier)) = 1 := by
  simp [Measure.real]

/-- The standard diagonal element with `i` uniformizers and remaining entries one.
The index ranges from zero through the full positive rank. -/
def standardDiagonal (r : ℕ) (i : Fin (r + 2)) : GeneralLinear (r + 1) F.Carrier :=
  GeneralLinear.Iwasawa.diagonalUnits fun j : Fin (r + 1) =>
    if j.val < i.val then F.canonicalTopologicalData.uniformizerUnit else 1

@[simp] theorem standardDiagonal_val (r : ℕ) (i : Fin (r + 2)) :
    (standardDiagonal F r i : Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier) =
      Matrix.diagonal (fun j => if j.val < i.val then
        (F.canonicalTopologicalData.uniformizerUnit : F.Carrier) else 1) := by
  simp only [standardDiagonal, GeneralLinear.Iwasawa.diagonalUnits_val]
  congr 1
  funext j
  split <;> rfl

@[simp] theorem standardDiagonal_zero (r : ℕ) : standardDiagonal F r 0 = 1 := by
  unfold standardDiagonal
  simp only [Fin.val_zero, not_lt_zero, ite_false]
  exact map_one GeneralLinear.Iwasawa.diagonalUnits

/-- The actual spherical corner for the specified field and positive rank. -/
abbrev SphericalHeckeAlgebra (r : ℕ) :=
  Hecke.HeckeAlgebra.Corner (sphericalHaar F r) (sphericalOpenSubgroup F r)
    (sphericalOpenSubgroup_isCompact F r)

/-- The standard Hecke element is the characteristic function of the actual
standard diagonal double coset for the measure of spherical subgroup mass one. -/
def standardHeckeElement (r : ℕ) (i : Fin (r + 2)) : SphericalHeckeAlgebra F r :=
  Hecke.HeckeAlgebra.Corner.doubleCoset (sphericalOpenSubgroup F r)
    (sphericalOpenSubgroup_isCompact F r) (sphericalHaar F r) (standardDiagonal F r i)

@[simp] theorem standardHeckeElement_apply (r : ℕ) (i : Fin (r + 2))
    (g : GeneralLinear (r + 1) F.Carrier) :
    standardHeckeElement F r i g =
      (Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup F r)
        (standardDiagonal F r i)).indicator (fun _ => (1 : ℂ)) g := by
  exact Hecke.HeckeAlgebra.Corner.doubleCoset_apply_of_mass_one _ _ _
    (sphericalHaar_real_self F r) _ _

@[simp] theorem standardHeckeElement_zero (r : ℕ) : standardHeckeElement F r 0 = 1 := by
  simp [standardHeckeElement]

/-- The standard integrated operator on the original spherical fixed submodule. -/
def standardHeckeOperator {r : ℕ} (A : AutomorphicObject.{uF, uV} F r.succPNat)
    (i : Fin (r + 2)) : Module.End ℂ (fixedVectors A.obj.representation (sphericalSubgroup F r)) :=
  @Hecke.cornerAction (GeneralLinear (r + 1) F.Carrier) _
    (F.canonicalGeneralLinearTopology (r + 1))
    (F.canonicalGeneralLinearTopologicalGroup (r + 1)) _ _ _ _ _
    (sphericalHaar F r) _ A.obj.representation A.obj.isSmooth
    (sphericalOpenSubgroup F r) (sphericalOpenSubgroup_isCompact F r)
    (standardHeckeElement F r i)

@[simp] theorem standardHeckeOperator_zero {r : ℕ}
    (A : AutomorphicObject.{uF, uV} F r.succPNat) : standardHeckeOperator F A 0 = 1 := by
  unfold standardHeckeOperator
  rw [standardHeckeElement_zero, map_one]
  rfl

/-- The signed Euler coefficient, the algebraic elementary symmetric invariant. -/
def elementaryCoefficient {n : ℕ} (s : Eigenvalues n) (i : ℕ) : ℂ :=
  (-1 : ℂ) ^ i * (Eigenvalues.eulerPolynomial s).coeff i

@[simp] theorem elementaryCoefficient_zero {n : ℕ} (s : Eigenvalues n) :
    elementaryCoefficient s 0 = 1 := by
  simp only [elementaryCoefficient, pow_zero, one_mul, Polynomial.coeff_zero_eq_eval_zero,
    Eigenvalues.eulerPolynomial_eval_zero]

/-- The prescribed scalar with the positive square-root residue normalization. -/
def standardHeckeScalar {r : ℕ} (s : Eigenvalues (r + 1)) (i : Fin (r + 2)) : ℂ :=
  (Real.sqrt (F.canonicalTopologicalData.residueCardinality : ℝ) : ℂ) ^
    (i.val * (r + 1 - i.val)) * elementaryCoefficient s i.val

@[simp] theorem standardHeckeScalar_zero {r : ℕ} (s : Eigenvalues (r + 1)) :
    standardHeckeScalar F s 0 = 1 := by simp [standardHeckeScalar]

/-- A nonzero actual spherical fixed space on which all the standard double-coset
operators have the specified scalars. This is a relation, not a classification assumption. -/
def HasSphericalHeckeSpectrum {r : ℕ} (A : AutomorphicObject.{uF, uV} F r.succPNat)
    (s : Eigenvalues (r + 1)) : Prop :=
  fixedVectors A.obj.representation (sphericalSubgroup F r) ≠ ⊥ ∧
    ∀ (i : Fin (r + 2)) (v : fixedVectors A.obj.representation (sphericalSubgroup F r)),
      standardHeckeOperator F A i v = standardHeckeScalar F s i • v

/-- The zeroth operator always satisfies the prescribed identity scalar. -/
theorem standardHeckeOperator_zero_scalar {r : ℕ}
    (A : AutomorphicObject.{uF, uV} F r.succPNat) (s : Eigenvalues (r + 1))
    (v : fixedVectors A.obj.representation (sphericalSubgroup F r)) :
    standardHeckeOperator F A 0 v = standardHeckeScalar F s 0 • v := by
  rw [standardHeckeOperator_zero, standardHeckeScalar_zero, one_smul]
  rfl

/-- Equivalences on the actual fixed spaces commute with every standard operator. -/
theorem standardHeckeOperator_equiv {r : ℕ}
    {A : AutomorphicObject.{uF, uV} F r.succPNat}
    {B : AutomorphicObject.{uF, uW} F r.succPNat}
    (e : A.obj.representation.Equiv B.obj.representation) (i : Fin (r + 2))
    (v : fixedVectors A.obj.representation (sphericalSubgroup F r)) :
    fixedVectorsEquiv e (sphericalSubgroup F r) (standardHeckeOperator F A i v) =
      standardHeckeOperator F B i (fixedVectorsEquiv e (sphericalSubgroup F r) v) := by
  exact @Hecke.cornerAction_equiv (GeneralLinear (r + 1) F.Carrier) _
    (F.canonicalGeneralLinearTopology (r + 1))
    (F.canonicalGeneralLinearTopologicalGroup (r + 1)) _ _ _ _ _ _ _ _
    (sphericalHaar F r) _ A.obj.representation A.obj.isSmooth
    (sphericalOpenSubgroup F r) (sphericalOpenSubgroup_isCompact F r)
    B.obj.representation B.obj.isSmooth e (standardHeckeElement F r i) v

/-- The Hecke spectral relation is invariant across independent carrier universes. -/
theorem hasSphericalHeckeSpectrum_iff_of_equiv {r : ℕ}
    {A : AutomorphicObject.{uF, uV} F r.succPNat}
    {B : AutomorphicObject.{uF, uW} F r.succPNat}
    (e : A.obj.representation.Equiv B.obj.representation) (s : Eigenvalues (r + 1)) :
    HasSphericalHeckeSpectrum F A s ↔ HasSphericalHeckeSpectrum F B s := by
  constructor
  · rintro ⟨hne, hs⟩
    refine ⟨(fixedVectors_ne_bot_iff_of_equiv e _).mp hne, ?_⟩
    intro i w
    obtain ⟨v, rfl⟩ := (fixedVectorsEquiv e (sphericalSubgroup F r)).surjective w
    rw [← standardHeckeOperator_equiv F e, hs, map_smul]
  · rintro ⟨hne, hs⟩
    refine ⟨(fixedVectors_ne_bot_iff_of_equiv e _).mpr hne, ?_⟩
    intro i v
    obtain ⟨w, rfl⟩ := (fixedVectorsEquiv e.symm (sphericalSubgroup F r)).surjective v
    rw [← standardHeckeOperator_equiv F e.symm, hs, map_smul]

/-- The Hecke relation on the genuine quotient by representation equivalence. -/
def HasSphericalHeckeSpectrumClass {r : ℕ}
    (π : AutomorphicClass.{uF, uV} F r.succPNat) (s : Eigenvalues (r + 1)) : Prop :=
  ∃ A : AutomorphicObject.{uF, uV} F r.succPNat,
    automorphicClassOf F A = π ∧ HasSphericalHeckeSpectrum F A s

@[simp] theorem hasSphericalHeckeSpectrumClass_classOf {r : ℕ}
    (A : AutomorphicObject.{uF, uV} F r.succPNat) (s : Eigenvalues (r + 1)) :
    HasSphericalHeckeSpectrumClass F (automorphicClassOf F A) s ↔
      HasSphericalHeckeSpectrum F A s := by
  constructor
  · rintro ⟨B, hB, h⟩
    obtain ⟨e⟩ := (automorphicClassOf_eq_iff F B A).mp hB
    exact (hasSphericalHeckeSpectrum_iff_of_equiv F e s).mp h
  · intro h
    exact ⟨A, rfl, h⟩

theorem HasSphericalHeckeSpectrumClass.isSpherical {r : ℕ}
    {π : AutomorphicClass.{uF, uV} F r.succPNat} {s : Eigenvalues (r + 1)}
    (h : HasSphericalHeckeSpectrumClass F π s) : IsSphericalClass F π := by
  obtain ⟨A, hA, hfixed, _⟩ := h
  exact ⟨A, hA, hfixed⟩

end Langlands.Unramified
