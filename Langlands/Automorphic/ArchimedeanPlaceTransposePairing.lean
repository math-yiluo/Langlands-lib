import Langlands.Automorphic.CuspidalArchimedeanDensityModels
import Langlands.Representation.Archimedean.TransposePairing
import Langlands.Global.ArchimedeanTransposeCompact

/-! # Assembling the actual archimedean inverse-transpose pairing -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open scoped TensorProduct Matrix

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F]

namespace InfinitePlaceFamily

/-- The genuine inverse-transpose twist on the compact group at each place. -/
def compactTwist (n : ℕ) (i : Index F) : Compact n i ≃* Compact n i :=
  match i with
  | .inl _ => Archimedean.compactIota ℝ n
  | .inr _ => Archimedean.compactIota ℂ n

/-- The genuine complexification of negative transpose at each place. -/
def lieTwist (n : ℕ) (i : Index F) : Lie n i ≃ₗ⁅ℂ⁆ Lie n i :=
  match i with
  | .inl _ => Archimedean.complexifiedMatrixLieIota ℝ n
  | .inr _ => Archimedean.complexifiedMatrixLieIota ℂ n

omit [NumberField F] in
theorem compactTranspose_toStandardCompact (n : ℕ) (p : ArchimedeanCompactFactors F n) :
    compactTranspose F n (ArchimedeanCompactFactors.toStandardCompact F n p) =
      ArchimedeanCompactFactors.toStandardCompact F n
        (fun v => Archimedean.compactIota ℝ n (p.1 v),
          fun v => Archimedean.compactIota ℂ n (p.2 v)) := by
  apply Subtype.ext
  apply (archimedeanGLCoordinates F n).injective
  rw [compactTranspose_val, ArchimedeanCompactFactors.toStandardCompact_val,
    coordinates_inverseTranspose, ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL,
    ArchimedeanCompactFactors.toStandardCompact_val,
    ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
  apply Units.ext
  apply Matrix.ext
  intro a b
  apply Prod.ext <;> funext v <;> rfl

/-- Local inverse transpose is the restriction of the actual global compact involution. -/
theorem compactTranspose_inclusion (n : ℕ) (i : Index F) (k : Compact n i) :
    compactTranspose F n (compactInclusion n i k) =
      compactInclusion n i (compactTwist n i k) := by
  classical
  change compactTranspose F n
      (ArchimedeanCompactFactors.toStandardCompact F n (compactFactor n i k)) =
    ArchimedeanCompactFactors.toStandardCompact F n
      (compactFactor n i (compactTwist n i k))
  rw [compactTranspose_toStandardCompact]
  apply congrArg (ArchimedeanCompactFactors.toStandardCompact F n)
  cases i with
  | inl v =>
    apply Prod.ext
    · funext w
      by_cases h : w = v
      · subst w
        simp [compactFactor, compactTwist]
      · simp [compactFactor, compactTwist, h]
    · funext w
      simp [compactFactor]
  | inr v =>
    apply Prod.ext
    · funext w
      simp [compactFactor]
    · funext w
      by_cases h : w = v
      · subst w
        simp [compactFactor, compactTwist]
      · simp [compactFactor, compactTwist, h]

omit [NumberField F] in
private theorem realProjection_iota (n : ℕ)
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) (X : RealLieAlgebra F n) :
    realPlaceLieProjection F n v (realLieIota F n X) =
      -(realPlaceLieProjection F n v X).transpose := rfl

omit [NumberField F] in
private theorem complexProjection_iota (n : ℕ)
    (v : {v : NumberField.InfinitePlace F // v.IsComplex}) (X : RealLieAlgebra F n) :
    complexPlaceLieProjection F n v (realLieIota F n X) =
      -(complexPlaceLieProjection F n v X).transpose := rfl

omit [NumberField F] in
theorem realLieIota_realInclusion (n : ℕ)
    (v : {v : NumberField.InfinitePlace F // v.IsReal})
    (X : Matrix (Fin n) (Fin n) ℝ) :
    realLieIota F n (realPlaceLieInclusion F n v X) =
      realPlaceLieInclusion F n v (-X.transpose) := by
  classical
  apply (realLiePlaceCoordinates F n).injective
  apply Prod.ext
  · funext w
    change realPlaceLieProjection F n w _ = realPlaceLieProjection F n w _
    rw [realProjection_iota, realProjection_realInclusion, realProjection_realInclusion]
    by_cases h : w = v
    · subst w
      simp
    · simp [h]
  · funext w
    change complexPlaceLieProjection F n w _ = complexPlaceLieProjection F n w _
    rw [complexProjection_iota, complexProjection_realInclusion, complexProjection_realInclusion]
    simp

omit [NumberField F] in
theorem realLieIota_complexInclusion (n : ℕ)
    (v : {v : NumberField.InfinitePlace F // v.IsComplex})
    (X : Matrix (Fin n) (Fin n) ℂ) :
    realLieIota F n (complexPlaceLieInclusion F n v X) =
      complexPlaceLieInclusion F n v (-X.transpose) := by
  classical
  apply (realLiePlaceCoordinates F n).injective
  apply Prod.ext
  · funext w
    change realPlaceLieProjection F n w _ = realPlaceLieProjection F n w _
    rw [realProjection_iota, realProjection_complexInclusion, realProjection_complexInclusion]
    simp
  · funext w
    change complexPlaceLieProjection F n w _ = complexPlaceLieProjection F n w _
    rw [complexProjection_iota, complexProjection_complexInclusion, complexProjection_complexInclusion]
    by_cases h : w = v
    · subst w
      simp
    · simp [h]

/-- Local complexified negative transpose is the restriction of the global Lie involution. -/
theorem complexLieIota_inclusion (n : ℕ) (i : Index F) (X : Lie n i) :
    complexLieIota F n (lieInclusion n i X) =
      lieInclusion n i (lieTwist n i X) := by
  cases i with
  | inl v =>
    change complexLieIota F n (realPlaceComplexLieInclusion F n v X) =
      realPlaceComplexLieInclusion F n v (Archimedean.complexifiedMatrixLieIota ℝ n X)
    induction X using TensorProduct.inductionOn with
    | tmul c X =>
      simp only [realPlaceComplexLieInclusion_tmul, complexLieIota_tmul,
        Archimedean.complexifiedMatrixLieIota_tmul, realLieIota_realInclusion]
    | add X Y hX hY => simpa only [map_add] using congrArg₂ (· + ·) hX hY
  | inr v =>
    change complexLieIota F n (complexPlaceComplexLieInclusion F n v X) =
      complexPlaceComplexLieInclusion F n v (Archimedean.complexifiedMatrixLieIota ℂ n X)
    induction X using TensorProduct.inductionOn with
    | tmul c X =>
      simp only [complexPlaceComplexLieInclusion_tmul, complexLieIota_tmul,
        Archimedean.complexifiedMatrixLieIota_tmul, realLieIota_complexInclusion]
    | add X Y hX hY => simpa only [map_add] using congrArg₂ (· + ·) hX hY

/-- A complex-linear map on the global Lie algebra vanishes if it vanishes on each place. -/
theorem linearMap_eq_zero_of_places {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : ComplexLieAlgebra F n →ₗ[ℂ] V) (hf : ∀ i X, f (lieInclusion n i X) = 0) :
    f = 0 := by
  classical
  apply LinearMap.ext
  intro Y
  induction Y using TensorProduct.inductionOn with
  | tmul c X =>
    have hX : f (complexify F n X) = 0 := by
      have h := congrArg (fun X : RealLieAlgebra F n => f (complexify F n X))
        (sum_placeLieInclusions F n X)
      have hr (v : {v : NumberField.InfinitePlace F // v.IsReal}) :
          f (complexify F n (realPlaceLieInclusion F n v (realPlaceLieProjection F n v X))) = 0 :=
        hf (.inl v) ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieProjection F n v X)
      have hc (v : {v : NumberField.InfinitePlace F // v.IsComplex}) :
          f (complexify F n (complexPlaceLieInclusion F n v (complexPlaceLieProjection F n v X))) = 0 :=
        hf (.inr v) ((1 : ℂ) ⊗ₜ[ℝ] complexPlaceLieProjection F n v X)
      simpa only [map_add, map_sum, hr, hc, Finset.sum_const_zero, add_zero] using h.symm
    have heq : (c ⊗ₜ[ℝ] X : ComplexLieAlgebra F n) = c • complexify F n X := by
      rw [complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    change f (c ⊗ₜ[ℝ] X) = 0
    rw [heq, map_smul, hX, smul_zero]
  | add Y Z hY hZ => simpa only [map_add, add_zero] using congrArg₂ (· + ·) hY hZ

/-- Simultaneous actual place identities imply the full archimedean transpose identities. -/
theorem globalPairing_of_local {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (κ : Representation ℂ (standardInfiniteCompact F n) V)
    (π : ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ V)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hB : ∀ i, Archimedean.FiniteFamilyPairing.IsTwistedPairing
      (fun k => compactTwist n i k) (fun X => lieTwist n i X)
      (κ.comp (compactInclusion n i).toMonoidHom) (π.comp (lieInclusion n i)) B) :
    (∀ k x y, B (κ k x) (κ (compactTranspose F n k) y) = B x y) ∧
      ∀ X x y, B (π X x) y + B x (π (complexLieIota F n X) y) = 0 := by
  constructor
  · let H : Submonoid (standardInfiniteCompact F n) :=
      { carrier := {k | ∀ x y, B (κ k x) (κ (compactTranspose F n k) y) = B x y}
        one_mem' := by
          intro x y
          simp
        mul_mem' := by
          intro k l hk hl x y
          simp only [map_mul, Module.End.mul_apply]
          exact (hk (κ l x) (κ (compactTranspose F n l) y)).trans (hl x y) }
    have hH : ∀ i k, compactInclusion n i k ∈ H := by
      intro i k x y
      rw [compactTranspose_inclusion]
      exact (hB i).1 k x y
    exact fun k => mem_of_place_mem n H hH k
  · intro X x y
    let f : ComplexLieAlgebra F n →ₗ[ℂ] ℂ :=
      { toFun := fun Y => B (π Y x) y + B x (π (complexLieIota F n Y) y)
        map_add' := by
          intro Y Z
          simp only [map_add, LinearMap.add_apply]
          ring
        map_smul' := by
          intro c Y
          simp only [map_smul, LinearMap.smul_apply, smul_add, RingHom.id_apply] }
    have hf : f = 0 := linearMap_eq_zero_of_places f fun i Y => by
      change B (π (lieInclusion n i Y) x) y +
        B x (π (complexLieIota F n (lieInclusion n i Y)) y) = 0
      rw [complexLieIota_inclusion]
      exact (hB i).2 Y x y
    exact LinearMap.congr_fun hf X

end InfinitePlaceFamily

local instance placeTransposeRationalGroup {n : ℕ} :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance placeTransposeContinuousGroup {n : ℕ} :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance placeTransposeSmoothGroup {n : ℕ} :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance placeTransposeFormsGroup {n : ℕ} :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance placeTransposeStableGroup {n : ℕ} :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance placeTransposeSpaceGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization.PlaceDensityModels

open InfinitePlaceFamily

variable {n : ℕ} {S : OperatorRealization F n} (D : S.PlaceDensityModels)
  (A : Subrepresentation S.finiteRepresentation)

local instance placeTransposeSourceGroup (i : Index F) :
    AddCommGroup (D.subspace i) := Submodule.addCommGroup _

/-- Nonzero inverse-transpose pairings on the actual local sources assemble into a
nonzero pairing for the full archimedean action on the actual multiplicity space. -/
def transposeMultiplicityPairing
    (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (ha : IsAdmissible A.toRepresentation)
    (hr : ∀ v : {v : NumberField.InfinitePlace F // v.IsReal},
      Archimedean.HasNonzeroTransposeGKPairing ℝ n
        (D.sourceCompact (.inl v)) (D.sourceLie (.inl v)))
    (hc : ∀ v : {v : NumberField.InfinitePlace F // v.IsComplex},
      Archimedean.HasNonzeroTransposeGKPairing ℂ n
        (D.sourceCompact (.inr v)) (D.sourceLie (.inr v))) :
    {B : S.FiniteMultiplicity A →ₗ[ℂ] S.FiniteMultiplicity A →ₗ[ℂ] ℂ //
      ((∀ k x y, B (S.finiteMultiplicityCompact A k x)
        (S.finiteMultiplicityCompact A (compactTranspose F n k) y) = B x y) ∧
        ∀ X x y, B (S.finiteMultiplicityLie A X x) y +
          B x (S.finiteMultiplicityLie A (complexLieIota F n X) y) = 0) ∧ B ≠ 0} := by
  have hlocal : ∀ i : Index F, ∃ B : D.subspace i →ₗ[ℂ] D.subspace i →ₗ[ℂ] ℂ,
      Archimedean.FiniteFamilyPairing.IsTwistedPairing
        (fun k => compactTwist n i k) (fun X => lieTwist n i X)
        (D.sourceCompact i) (D.sourceLie i) B ∧ B ≠ 0 := by
    intro i
    cases i with
    | inl v => exact hr v
    | inr v => exact hc v
  let B := D.multiplicityPairing A hS hne hA ha
    (fun i k => compactTwist n i k) (fun i X => lieTwist n i X) hlocal
  exact ⟨B.val, globalPairing_of_local (S.finiteMultiplicityCompact A)
    (S.finiteMultiplicityLie A) B.val B.property.1, B.property.2⟩

end OperatorRealization.PlaceDensityModels
end Langlands.Automorphic
