import Langlands.Geometry.FormalGroup.SpecialModule
import Langlands.Algebra.LocalDivisionSubfieldCyclic

/-! # Cyclic relations on the division order and its tangent representation -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)
variable {π : 𝒪[K]} (uniformizer : Dˣ) (σ : L ≃ₐ[K] L)

/-- The division uniformizer of the cyclic relations belongs to the actual order. -/
def drinfeldIntegralUniformizer
    (hUniformizer : (uniformizer : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K)) :
    IntegerRing K D :=
  ⟨uniformizer, by
    change localReducedNormValuation K D (uniformizer : D) ≤ 1
    apply (pow_le_one_iff_of_nonneg zero_le (CentralSimple.reducedDegree_pos K D).ne').mp
    rw [← map_pow, hUniformizer, localReducedNormValuation_algebraMap]
    exact pow_le_one₀ zero_le π.property⟩

@[simp]
theorem drinfeldIntegralUniformizer_coe
    (hUniformizer : (uniformizer : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K)) :
    (drinfeldIntegralUniformizer uniformizer hUniformizer : D) = uniformizer := rfl

/-- The power relation holds in the integral order. -/
theorem drinfeldIntegralUniformizer_pow
    (hUniformizer : (uniformizer : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K)) :
    drinfeldIntegralUniformizer uniformizer hUniformizer ^ CentralSimple.reducedDegree K D =
      algebraMap 𝒪[K] (IntegerRing K D) π :=
  Subtype.ext hUniformizer

/-- Frobenius restricts to an algebra automorphism of the actual integer subfield. -/
def subfieldIntegerFrobenius (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) :
    SubfieldIntegerRing K D ι ≃ₐ[𝒪[K]] SubfieldIntegerRing K D ι :=
  letI : FiniteDimensional K L := hL.1
  { __ := localDivisionSubfieldIntegerAut K D ι σ
    commutes' := fun a => Subtype.ext (σ.commutes a.val) }

@[simp]
theorem subfieldIntegerFrobenius_coe (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (a : SubfieldIntegerRing K D ι) :
    (subfieldIntegerFrobenius ι σ hL a : L) = σ (a : L) := rfl

/-- The relation between Frobenius and the division uniformizer holds in the order. -/
theorem drinfeldIntegralUniformizer_mul_subfield
    (hUniformizer : (uniformizer : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K))
    (hσ : ∀ a : L, (uniformizer : D) * ι a = ι (σ a) * (uniformizer : D))
    (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) (a : SubfieldIntegerRing K D ι) :
    drinfeldIntegralUniformizer uniformizer hUniformizer * subfieldIntegerInclusion K D ι a =
      subfieldIntegerInclusion K D ι (subfieldIntegerFrobenius ι σ hL a) *
        drinfeldIntegralUniformizer uniformizer hUniformizer :=
  Subtype.ext (hσ a.val)

/-- Multiplying by the division uniformizer moves an eigenspace to the one with
its character precomposed by inverse Frobenius. -/
theorem SpecialModule.fiberTangent_uniformizer_shift
    {R : Type v} [CommRing R] [Algebra 𝒪[K] R] (X : SpecialModule K D ι R)
    {S : Type w} [CommRing S] (φ : R →+* S)
    (χ : SubfieldIntegerRing K D ι →+* S)
    (hUniformizer : (uniformizer : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K))
    (hσ : ∀ a : L, (uniformizer : D) * ι a = ι (σ a) * (uniformizer : D))
    (x : Fin (CentralSimple.reducedDegree K D) → S)
    (hx : ∀ a : SubfieldIntegerRing K D ι,
      X.order.fiberTangent φ (subfieldIntegerInclusion K D ι a) x = χ a • x)
    (a : SubfieldIntegerRing K D ι) :
    X.order.fiberTangent φ (subfieldIntegerInclusion K D ι a)
        (X.order.fiberTangent φ (drinfeldIntegralUniformizer uniformizer hUniformizer) x) =
      χ ((subfieldIntegerFrobenius ι σ X.unramified).symm a) •
        X.order.fiberTangent φ (drinfeldIntegralUniformizer uniformizer hUniformizer) x := by
  let t := X.order.fiberTangent φ
  let P := drinfeldIntegralUniformizer uniformizer hUniformizer
  let f := subfieldIntegerFrobenius ι σ X.unramified
  let j := subfieldIntegerInclusion K D ι
  change t (j a) (t P x) = χ (f.symm a) • t P x
  have h := drinfeldIntegralUniformizer_mul_subfield ι uniformizer σ hUniformizer hσ X.unramified (f.symm a)
  change P * j (f.symm a) = j (f (f.symm a)) * P at h
  rw [f.apply_symm_apply] at h
  calc
    t (j a) (t P x) = t (j a * P) x := by rw [map_mul]; rfl
    _ = t (P * j (f.symm a)) x := by rw [h]
    _ = t P (t (j (f.symm a)) x) := by rw [map_mul]; rfl
    _ = χ (f.symm a) • t P x := by rw [hx, map_smul]

/-- The reduced-degree power of the tangent uniformizer is multiplication by π. -/
theorem SpecialModule.fiberTangent_uniformizer_pow
    {R : Type v} [CommRing R] [Algebra 𝒪[K] R] (X : SpecialModule K D ι R)
    {S : Type w} [CommRing S] (φ : R →+* S)
    (hUniformizer : (uniformizer : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K))
    (x : Fin (CentralSimple.reducedDegree K D) → S) :
    ((X.order.fiberTangent φ (drinfeldIntegralUniformizer uniformizer hUniformizer)) ^
        CentralSimple.reducedDegree K D) x = φ (algebraMap 𝒪[K] R π) • x := by
  rw [← map_pow, drinfeldIntegralUniformizer_pow, X.order.fiberTangent_scalar]

end Langlands.FormalGroup.LocalDivision
