import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-! # Detection in noetherian rings by local Artinian quotients -/

noncomputable section

universe u v

namespace Langlands.AlgebraicGeometry.Deformation
namespace ArtinianDetection

/-- The positive maximal-ideal quotient of a local ring. -/
abbrev LocalTestRing (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) :=
  A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)

instance localTestRing_nontrivial (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) :
    Nontrivial (LocalTestRing A n) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro h
  have hle := Ideal.pow_le_self (I := IsLocalRing.maximalIdeal A) (Nat.succ_ne_zero n)
  rw [h] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp hle)

instance localTestRing_isLocalRing (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) :
    IsLocalRing (LocalTestRing A n) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

instance localTestRing_isArtinianRing (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (n : ℕ) : IsArtinianRing (LocalTestRing A n) := by
  have : IsNoetherianRing (LocalTestRing A n) :=
    isNoetherianRing_of_surjective A _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  apply (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr
  refine ⟨n + 1, ?_⟩
  rw [← IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)))
    Ideal.Quotient.mk_surjective, ← Ideal.map_pow]
  exact Ideal.map_mk_eq_bot_of_le le_rfl

/-- Krull intersection detects a local noetherian element on its positive quotients. -/
theorem local_eq_zero (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (a : A) (h : ∀ n : ℕ, Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)) a = 0) :
    a = 0 := by
  apply Ideal.mem_bot.mp
  rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top]
  apply Ideal.mem_iInf.mpr
  intro n
  cases n with
  | zero => simp
  | succ n => exact Ideal.Quotient.eq_zero_iff_mem.mp (h n)

/-- The actual ring homomorphism evaluating at all local Artinian quotients. -/
def evaluation (R : Type u) [CommRing R] :
    R →+* ∀ (P : MaximalSpectrum R) (n : ℕ),
      LocalTestRing (Localization.AtPrime P.asIdeal) n :=
  RingHom.pi fun P ↦ RingHom.pi fun _n ↦
    (Ideal.Quotient.mk _).comp (algebraMap R (Localization.AtPrime P.asIdeal))

@[simp]
theorem evaluation_apply (R : Type u) [CommRing R] (a : R) (P : MaximalSpectrum R) (n : ℕ) :
    evaluation R a P n =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ^ (n + 1))
        (algebraMap R (Localization.AtPrime P.asIdeal) a) := rfl

/-- The evaluation map is injective for every noetherian commutative ring. -/
theorem evaluation_injective (R : Type u) [CommRing R] [IsNoetherianRing R] :
    Function.Injective (evaluation R) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply eq_bot_iff.mpr
  intro a ha
  apply Ideal.mem_bot.mpr
  apply eq_zero_of_localization a
  intro P hP
  apply local_eq_zero (Localization.AtPrime P) _
  intro n
  have h := congrFun (congrFun (RingHom.mem_ker.mp ha) (MaximalSpectrum.mk P hP)) n
  exact h

/-- Equality of ring homomorphisms into a noetherian ring is detected by these tests. -/
theorem ringHom_ext {B : Type v} [CommRing B] (R : Type u) [CommRing R]
    [IsNoetherianRing R] (f g : B →+* R)
    (h : ∀ (P : MaximalSpectrum R) (n : ℕ),
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ^ (n + 1))).comp
        (algebraMap R (Localization.AtPrime P.asIdeal))).comp f =
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ^ (n + 1))).comp
        (algebraMap R (Localization.AtPrime P.asIdeal))).comp g) :
    f = g := by
  ext b
  apply evaluation_injective R
  funext P n
  exact DFunLike.congr_fun (h P n) b

end ArtinianDetection
end Langlands.AlgebraicGeometry.Deformation
