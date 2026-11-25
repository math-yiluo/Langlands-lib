import Langlands.Global.NumberFieldAdeleContinuousTensor
import Langlands.Global.AdelicGLTransport
import Langlands.Global.AdeleGaloisAction
import Langlands.ClassFieldTheory.Global.IdeleGaloisDescentProof
import Langlands.BaseChange.CyclicNormDeterminant

/-! # Fixed adelic coefficients of a cyclic generator -/

noncomputable section

universe u

open NumberField

namespace Langlands.Global

open AdelicFunctoriality Langlands.BaseChange

variable (K L : Type u) [Field K] [Field L] [NumberField L] [Algebra K L]

local instance cyclicAdeleFixedCoefficientsAlgebra : Algebra K (Adeles L) :=
  ((algebraMap L (Adeles L)).comp (algebraMap K L)).toAlgebra

/-- Arithmetic transport on adeles, viewed as an automorphism over the
ground field. -/
def adeleCoefficientAut : (L ≃ₐ[K] L) →* (Adeles L ≃ₐ[K] Adeles L) where
  toFun σ :=
    { adeleEquiv σ.toRingEquiv with
      commutes' := fun a => by
        change adeleEquiv σ.toRingEquiv (algebraMap L (Adeles L) (algebraMap K L a)) = _
        exact (adeleEquiv_diagonal σ.toRingEquiv (algebraMap K L a)).trans
          (congrArg (algebraMap L (Adeles L)) (σ.commutes a)) }
  map_one' := AlgEquiv.ext fun a => RingEquiv.congr_fun adeleEquiv_refl a
  map_mul' σ τ := AlgEquiv.ext fun a =>
    RingEquiv.congr_fun (adeleEquiv_trans τ.toRingEquiv σ.toRingEquiv) a

@[simp]
theorem adeleCoefficientAut_apply (σ : L ≃ₐ[K] L) (a : Adeles L) :
    adeleCoefficientAut K L σ a = adeleEquiv σ.toRingEquiv a := rfl

/-- The coefficient action on matrices is the original adelic transport. -/
theorem entrywiseAut_adeleCoefficientAut (σ : L ≃ₐ[K] L) (n : ℕ) (x : AdelicGL L n) :
    entrywiseAut (adeleCoefficientAut K L σ) n x =
      AdelicGLTransport.adelicEquiv n σ.toRingEquiv x := rfl

omit [NumberField L] in
private theorem powers_surject_of_cyclic {σ : L ≃ₐ[K] L} {l : ℕ}
    (hcyc : IsCyclicAlgebra σ l) : Function.Surjective (fun k : Fin l => σ ^ (k : ℕ)) := by
  classical
  let : FiniteDimensional K L := hcyc.1
  let : IsGalois K L := hcyc.isGalois
  have hinj : Function.Injective (fun k : Fin l => σ ^ (k : ℕ)) := by
    intro i j hij
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (x := σ)
      (hcyc.2.2.2.1.symm ▸ i.isLt) (hcyc.2.2.2.1.symm ▸ j.isLt) hij
  have hcard : Fintype.card (Fin l) = Fintype.card (L ≃ₐ[K] L) := by
    rw [Fintype.card_fin, Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, hcyc.2.1]
  exact ((Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩).2

open Langlands.ClassFieldTheory.Global.IdeleGaloisDescentProof

variable [NumberField K]

open scoped NNReal

/-- Positive real scalar ideles belong to the fixed part of the upper field. -/
theorem adelicEquiv_scalar_positiveReal (σ : L ≃ₐ[K] L) (n : ℕ) (t : ℝ≥0ˣ) :
    AdelicGLTransport.adelicEquiv n σ.toRingEquiv
        (AdelicGL.scalar L n (PositiveRealIdeles.full L t)) =
      AdelicGL.scalar L n (PositiveRealIdeles.full L t) := by
  rw [AdelicGLTransport.adelicEquiv_scalar]
  congr 1
  apply Units.ext
  change adeleEquiv σ.toRingEquiv (PositiveRealIdeles.full L t : Adeles L) = _
  rw [← AdeleGalois.adeleInclusion_positiveReal (F := K), adeleEquiv_adeleInclusion]

/-- The scalars fixed by the chosen cyclic generator are precisely the
original ground-field adeles. -/
theorem adeleCoefficientAut_fixed_iff {σ : L ≃ₐ[K] L} {l : ℕ}
    (hcyc : IsCyclicAlgebra σ l) (x : Adeles L) :
    adeleCoefficientAut K L σ x = x ↔ x ∈ Set.range (adeleInclusionAlgHom K L) := by
  constructor
  · intro hx
    let : IsGalois K L := hcyc.isGalois
    apply exists_adele_descent
    intro τ
    obtain ⟨i, rfl⟩ := powers_surject_of_cyclic K L hcyc τ
    change adeleCoefficientAut K L (σ ^ (i : ℕ)) x = x
    rw [map_pow]
    have hfix (m : ℕ) : (adeleCoefficientAut K L σ ^ m) x = x := by
      induction m with
      | zero => rfl
      | succ m ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hx]
    exact hfix _
  · rintro ⟨y, rfl⟩
    exact adeleEquiv_adeleInclusion σ y

end Langlands.Global
