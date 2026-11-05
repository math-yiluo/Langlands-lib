import Langlands.AlgebraicGeometry.Deformation.ArtinianQuotients
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Noetherian.Basic

/-! # The actual Artinian quotients of an augmented noetherian local algebra -/

noncomputable section

universe u

open CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Deformation

namespace LocalAdicArtinianTests

private lemma lift_comp_factor {k R S : Type u} [CommRing k] [CommRing R]
    [CommRing S] [Algebra k R] [Algebra k S]
    {I J : Ideal R} (hIJ : I ≤ J) (ε : R →ₐ[k] S)
    (hI : I ≤ RingHom.ker ε.toRingHom) (hJ : J ≤ RingHom.ker ε.toRingHom) :
    (Ideal.Quotient.liftₐ J ε (fun _ hx ↦ RingHom.mem_ker.mp (hJ hx))).comp
      (Ideal.Quotient.factorₐ k hIJ) =
        Ideal.Quotient.liftₐ I ε (fun _ hx ↦ RingHom.mem_ker.mp (hI hx)) := by
  apply Ideal.Quotient.algHom_ext
  rw [AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp_mk,
    Ideal.Quotient.liftₐ_comp, Ideal.Quotient.liftₐ_comp]

variable {k K R : Type u} [CommRing k] [Field K] [Algebra k K]
  [CommRing R] [Algebra k R] [IsLocalRing R]
  (ε : R →ₐ[k] K) (hε : Function.Surjective ε)

local notation "m" => IsLocalRing.maximalIdeal R

include hε in
/-- The positive maximal-ideal power killed by the given residue augmentation. -/
lemma power_le_ker (n : ℕ) :
    m ^ (n + 1) ≤ RingHom.ker ε.toRingHom := by
  rw [IsLocalRing.ker_eq_maximalIdeal ε.toRingHom hε]
  exact Ideal.pow_le_self (Nat.succ_ne_zero n)

/-- The original augmentation descends to every positive maximal-ideal quotient. -/
def augmentation (n : ℕ) : R ⧸ m ^ (n + 1) →ₐ[k] K :=
  Ideal.Quotient.liftₐ _ ε (fun _ hx ↦ RingHom.mem_ker.mp (power_le_ker ε hε n hx))

lemma augmentation_surjective (n : ℕ) :
    Function.Surjective (augmentation ε hε n) := by
  intro a
  obtain ⟨r, hr⟩ := hε a
  exact ⟨Ideal.Quotient.mk _ r, hr⟩

variable [IsNoetherianRing R]

include ε hε in
/-- Every positive maximal-ideal quotient is local Artinian. -/
lemma quotient_artinian (n : ℕ) : IsArtinianRing (R ⧸ m ^ (n + 1)) := by
  have : Nontrivial (R ⧸ m ^ (n + 1)) :=
    (augmentation ε hε n).toRingHom.domain_nontrivial
  have : IsLocalRing (R ⧸ m ^ (n + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsNoetherianRing (R ⧸ m ^ (n + 1)) :=
    isNoetherianRing_of_surjective R _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  apply (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr
  refine ⟨n + 1, ?_⟩
  rw [← IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk (m ^ (n + 1))) Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow]
  exact Ideal.map_mk_eq_bot_of_le le_rfl

/-- The actual augmented Artinian test at adic stage `n`, beginning with `R/m`. -/
def test (n : ℕ) : ArtinianTest k K := by
  have : Nontrivial (R ⧸ m ^ (n + 1)) :=
    (augmentation ε hε n).toRingHom.domain_nontrivial
  have : IsLocalRing (R ⧸ m ^ (n + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have := quotient_artinian ε hε n
  exact ArtinianTest.mk (R ⧸ m ^ (n + 1)) (augmentation ε hε n)
    (augmentation_surjective ε hε n)

/-- The original scalar-preserving quotient map to an adic test. -/
def projection (n : ℕ) : R →ₐ[k] (test ε hε n).algebra :=
  Ideal.Quotient.mkₐ k (m ^ (n + 1))

lemma augmentation_projection (n : ℕ) :
    (test ε hε n).augmentation.comp (projection ε hε n) = ε :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- All later stages map to earlier ones by the actual quotient factor. -/
def transition {n p : ℕ} (hnp : n ≤ p) : test ε hε p ⟶ test ε hε n :=
  ArtinianTest.homMk
    (Ideal.Quotient.factorₐ k
      (Ideal.pow_le_pow_right (Nat.add_le_add_right hnp 1)))
    (lift_comp_factor _ ε (power_le_ker ε hε p) (power_le_ker ε hε n))

@[simp]
lemma toAlgHom_transition {n p : ℕ} (hnp : n ≤ p) :
    ArtinianTest.toAlgHom (transition ε hε hnp) =
      Ideal.Quotient.factorₐ k
        (Ideal.pow_le_pow_right (Nat.add_le_add_right hnp 1)) := rfl

lemma transition_surjective {n p : ℕ} (hnp : n ≤ p) :
    Function.Surjective (ArtinianTest.toAlgHom (transition ε hε hnp)) :=
  Ideal.Quotient.factor_surjective
    (Ideal.pow_le_pow_right (Nat.add_le_add_right hnp 1))

lemma projection_transition {n p : ℕ} (hnp : n ≤ p) :
    (ArtinianTest.toAlgHom (transition ε hε hnp)).comp (projection ε hε p) =
      projection ε hε n := rfl

@[simp]
lemma transition_refl (n : ℕ) : transition ε hε (le_refl n) = 𝟙 (test ε hε n) := by
  apply ArtinianTest.hom_ext
  apply Ideal.Quotient.algHom_ext
  rfl

@[simp]
lemma transition_comp {n p q : ℕ} (hnp : n ≤ p) (hpq : p ≤ q) :
    transition ε hε hpq ≫ transition ε hε hnp = transition ε hε (hnp.trans hpq) := by
  apply ArtinianTest.hom_ext
  exact Ideal.Quotient.factorₐ_comp k _ _

/-- The actual kernel is the image of the earlier positive maximal-ideal power. -/
lemma ker_transition {n p : ℕ} (hnp : n ≤ p) :
    RingHom.ker (ArtinianTest.toAlgHom (transition ε hε hnp)).toRingHom =
      (m ^ (n + 1)).map (Ideal.Quotient.mk (m ^ (p + 1))) := by
  change RingHom.ker (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.add_le_add_right hnp 1))) = _
  unfold Ideal.Quotient.factor
  rw [Ideal.ker_quotient_lift, Ideal.mk_ker]

/-- Consecutive stages are elementary, retaining the given residue augmentation. -/
lemma transition_succ_elementary (n : ℕ) :
    ArtinianTest.IsElementarySurjection (transition ε hε (Nat.le_succ n)) := by
  refine ⟨transition_surjective ε hε _, ?_⟩
  rw [ker_transition]
  have : IsLocalRing (R ⧸ m ^ (n + 1 + 1)) :=
    inferInstanceAs (IsLocalRing (test ε hε (n + 1)).algebra)
  change IsLocalRing.maximalIdeal (R ⧸ m ^ (n + 1 + 1)) *
    (m ^ (n + 1)).map (Ideal.Quotient.mk (m ^ (n + 1 + 1))) = ⊥
  rw [← IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk (m ^ (n + 1 + 1))) Ideal.Quotient.mk_surjective,
    ← Ideal.map_mul, ← pow_succ']
  exact Ideal.map_mk_eq_bot_of_le le_rfl

variable {A : ArtinianTest k K} (α : R →ₐ[k] A.algebra)

omit [IsNoetherianRing R] in
include hε in
/-- Every augmentation-compatible map to a test kills a positive maximal-ideal power. -/
lemma exists_bound (hα : A.augmentation.comp α = ε) :
    ∃ n : ℕ, m ^ (n + 1) ≤ RingHom.ker α.toRingHom := by
  have hmap : (m).map α.toRingHom ≤ IsLocalRing.maximalIdeal A.algebra := by
    rw [← ArtinianTest.ker_augmentation A, Ideal.map_le_iff_le_comap]
    intro r hr
    change A.augmentation (α r) = 0
    have hk : r ∈ RingHom.ker ε.toRingHom := by
      rwa [IsLocalRing.ker_eq_maximalIdeal ε.toRingHom hε]
    have hr' : ε r = 0 := RingHom.mem_ker.mp hk
    exact (congrArg (fun e : R →ₐ[k] K ↦ e r) hα).trans hr'
  obtain ⟨n, hn⟩ := A.maximalIdeal_isNilpotent
  refine ⟨n, ?_⟩
  apply Ideal.map_le_iff_le_comap.mp
  rw [Ideal.map_pow]
  calc
    ((m).map α.toRingHom) ^ (n + 1) ≤
        (IsLocalRing.maximalIdeal A.algebra) ^ (n + 1) :=
      pow_le_pow_left' hmap _
    _ = ⊥ := by rw [pow_succ, hn, zero_mul]; rfl

/-- An actual compatible bounded map gives an arrow from its finite adic test. -/
def factor (hα : A.augmentation.comp α = ε) (n : ℕ)
    (h : m ^ (n + 1) ≤ RingHom.ker α.toRingHom) : test ε hε n ⟶ A :=
  ArtinianTest.homMk
    (Ideal.Quotient.liftₐ _ α (fun _ hx ↦ RingHom.mem_ker.mp (h hx))) (by
      apply Ideal.Quotient.algHom_ext
      exact hα)

/-- The finite-stage arrow factors the original algebra map exactly. -/
lemma factor_projection (hα : A.augmentation.comp α = ε) (n : ℕ)
    (h : m ^ (n + 1) ≤ RingHom.ker α.toRingHom) :
    (ArtinianTest.toAlgHom (factor ε hε α hα n h)).comp (projection ε hε n) = α :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- A finite-stage test arrow is uniquely determined by its composite from `R`. -/
lemma factor_unique (hα : A.augmentation.comp α = ε) (n : ℕ)
    (h : m ^ (n + 1) ≤ RingHom.ker α.toRingHom)
    (q : test ε hε n ⟶ A)
    (hq : (ArtinianTest.toAlgHom q).comp (projection ε hε n) = α) :
    q = factor ε hε α hα n h := by
  apply ArtinianTest.hom_ext
  apply Ideal.Quotient.algHom_ext
  exact hq

/-- Every compatible map factors uniquely at some finite adic stage. -/
lemma exists_unique_factor (hα : A.augmentation.comp α = ε) :
    ∃ n : ℕ, ∃! q : test ε hε n ⟶ A,
      (ArtinianTest.toAlgHom q).comp (projection ε hε n) = α := by
  obtain ⟨n, hn⟩ := exists_bound ε hε α hα
  exact ⟨n, factor ε hε α hα n hn,
    factor_projection ε hε α hα n hn,
    fun q hq ↦ factor_unique ε hε α hα n hn q hq⟩

end LocalAdicArtinianTests

end Langlands.AlgebraicGeometry.Deformation
