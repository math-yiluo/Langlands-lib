import Mathlib.RingTheory.AdicCompletion.LocalRing
import Langlands.AlgebraicGeometry.Deformation.LocalAdicArtinianTests

/-! # Actual adic completions with a specified residue augmentation -/

noncomputable section

universe u

open CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Deformation.AugmentedAdicCompletion

private lemma factor_eval {R : Type u} [CommRing R] (I : Ideal R)
    {n p : ℕ} (hnp : n ≤ p) (s : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hnp) (AdicCompletion.evalₐ I p s) =
      AdicCompletion.evalₐ I n s := by
  induction s using AdicCompletion.induction_on with
  | h a =>
    simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
    exact AdicCompletion.Ideal.mk_eq_mk I hnp a

private lemma ker_eval {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  ext s
  change AdicCompletion.evalₐ I n s = 0 ↔ _
  let e : (R ⧸ (I ^ n • ⊤ : Ideal R)) ≃ₐ[R] R ⧸ I ^ n :=
    Ideal.quotientEquivAlgOfEq R (by simp)
  change e (AdicCompletion.eval I R n s) = 0 ↔ _
  rw [map_eq_zero_iff e e.injective]
  change s ∈ (AdicCompletion.eval I R n).ker ↔ _
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval (M := R) I.fg_of_isNoetherianRing]
  simp only [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]

variable {k K R : Type u} [CommRing k] [Field K] [Algebra k K]
  [CommRing R] [Algebra k R] [IsLocalRing R] [IsNoetherianRing R]
  (ε : R →ₐ[k] K) (hε : Function.Surjective ε)

/-- The actual completion of the original local algebra at its maximal ideal. -/
abbrev ring := AdicCompletion (IsLocalRing.maximalIdeal R) R

/-- The original scalar-preserving canonical map into the actual completion. -/
abbrev sourceMap : R →ₐ[k] ring (R := R) := Algebra.algHom k R (ring (R := R))

/-- The original residue augmentation factored through the residue quotient. -/
def residueFactor : R ⧸ IsLocalRing.maximalIdeal R →ₐ[k] K :=
  Ideal.Quotient.liftₐ _ ε (fun _ hr ↦
    RingHom.mem_ker.mp (show _ ∈ RingHom.ker ε.toRingHom from by
      rwa [IsLocalRing.ker_eq_maximalIdeal ε.toRingHom hε]))

/-- The completion carries the specified original residue augmentation. -/
def augmentation : ring (R := R) →ₐ[k] K :=
  (residueFactor ε hε).comp
    ((AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal R)).restrictScalars k)

omit [IsNoetherianRing R] in
@[simp]
lemma augmentation_sourceMap : (augmentation ε hε).comp (sourceMap (k := k)) = ε := by
  ext r
  change residueFactor ε hε (AdicCompletion.evalOneₐ _ (AdicCompletion.of _ R r)) = ε r
  rw [AdicCompletion.evalOneₐ_of]
  rfl

omit [IsNoetherianRing R] in
lemma augmentation_surjective : Function.Surjective (augmentation ε hε) := by
  intro x
  obtain ⟨r, hr⟩ := hε x
  refine ⟨sourceMap (k := k) r, ?_⟩
  exact (DFunLike.congr_fun (augmentation_sourceMap ε hε) r).trans hr

/-- The completion projects to the original augmented Artinian quotient. -/
def projection (n : ℕ) : ring (R := R) →ₐ[k]
    (LocalAdicArtinianTests.test ε hε n).algebra :=
  (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R) (n + 1)).restrictScalars k

lemma projection_sourceMap (n : ℕ) :
    (projection ε hε n).comp (sourceMap (k := k)) =
      LocalAdicArtinianTests.projection ε hε n := by
  ext r
  exact AdicCompletion.evalₐ_of _ (n + 1) r

lemma projection_transition {n p : ℕ} (hnp : n ≤ p) :
    (ArtinianTest.toAlgHom (LocalAdicArtinianTests.transition ε hε hnp)).comp
      (projection ε hε p) = projection ε hε n := by
  ext s
  exact factor_eval (IsLocalRing.maximalIdeal R) (Nat.add_le_add_right hnp 1) s

lemma augmentation_projection (n : ℕ) :
    (LocalAdicArtinianTests.test ε hε n).augmentation.comp (projection ε hε n) =
      augmentation ε hε := by
  ext s
  induction s using AdicCompletion.induction_on with
  | h a =>
    simp only [projection, AlgHom.comp_apply]
    change ε (a (n + 1)) = residueFactor ε hε (AdicCompletion.evalOneₐ _ (AdicCompletion.mk _ R a))
    rw [← AdicCompletion.factorₐ_evalₐ_one, AdicCompletion.evalₐ_mk]
    change ε (a (n + 1)) = ε (a 1)
    have ha : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (a (n + 1)) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (a 1) := by
      exact congrArg
        (Ideal.Quotient.factor (show IsLocalRing.maximalIdeal R ^ 1 ≤
          IsLocalRing.maximalIdeal R by rw [pow_one]))
        (AdicCompletion.Ideal.mk_eq_mk
          (IsLocalRing.maximalIdeal R) (Nat.le_add_left 1 n) a)
    exact congrArg (residueFactor ε hε) ha

lemma projection_surjective (n : ℕ) :
    Function.Surjective (projection ε hε n) :=
  AdicCompletion.surjective_evalₐ _ (n + 1)

/-- A projection kernel is exactly the corresponding power of the completion's
actual maximal ideal. -/
lemma ker_projection (n : ℕ) :
    RingHom.ker (projection ε hε n).toRingHom =
      IsLocalRing.maximalIdeal (ring (R := R)) ^ (n + 1) := by
  change RingHom.ker (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal R)
    (n + 1)).toRingHom = _
  rw [ker_eval, AdicCompletion.maximalIdeal_eq_map, Ideal.map_pow]

include ε hε in
/-- Every completion element agrees with an original element modulo any
specified positive power of the actual maximal ideal. -/
lemma exists_approximation (n : ℕ) (s : ring (R := R)) :
    ∃ r : R, s - sourceMap (k := k) r ∈
      IsLocalRing.maximalIdeal (ring (R := R)) ^ (n + 1) := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
    (projection ε hε n s)
  refine ⟨r, ?_⟩
  rw [← ker_projection ε hε n, RingHom.mem_ker, map_sub]
  exact sub_eq_zero.mpr (hr.symm.trans
    (DFunLike.congr_fun (projection_sourceMap ε hε n) r).symm)

/-- All scalar-preserving maps with the specified residue equation. -/
def Maps (A : ArtinianTest k K) :=
  {α : R →ₐ[k] A.algebra // A.augmentation.comp α = ε}

/-- Postcomposition uses every actual augmented test arrow. -/
def postcomp {A B : ArtinianTest k K} (q : A ⟶ B) : Maps ε A → Maps ε B :=
  fun α ↦ ⟨(ArtinianTest.toAlgHom q).comp α.val, by
    rw [← AlgHom.comp_assoc, ArtinianTest.augmentation_comp, α.property]⟩

/-- Restrict a compatible map along the canonical map into the actual completion. -/
def restriction (A : ArtinianTest k K) :
    Maps (augmentation ε hε) A → Maps ε A :=
  fun α ↦ ⟨α.val.comp (sourceMap (k := k)), by
    rw [← AlgHom.comp_assoc, α.property, augmentation_sourceMap]⟩

/-- A bounded original map extends through the actual finite-stage projection. -/
def extensionAt {A : ArtinianTest k K} (α : Maps ε A) (n : ℕ)
    (hn : IsLocalRing.maximalIdeal R ^ (n + 1) ≤ RingHom.ker α.val.toRingHom) :
    Maps (augmentation ε hε) A :=
  ⟨(ArtinianTest.toAlgHom (LocalAdicArtinianTests.factor ε hε α.val
      α.property n hn)).comp (projection ε hε n), by
    rw [← AlgHom.comp_assoc, ArtinianTest.augmentation_comp,
      augmentation_projection]⟩

@[simp]
lemma restriction_extensionAt {A : ArtinianTest k K} (α : Maps ε A) (n : ℕ)
    (hn : IsLocalRing.maximalIdeal R ^ (n + 1) ≤ RingHom.ker α.val.toRingHom) :
    restriction ε hε A (extensionAt ε hε α n hn) = α := by
  apply Subtype.ext
  change ((ArtinianTest.toAlgHom (LocalAdicArtinianTests.factor ε hε α.val
    α.property n hn)).comp (projection ε hε n)).comp (sourceMap (k := k)) = α.val
  rw [AlgHom.comp_assoc, projection_sourceMap,
    LocalAdicArtinianTests.factor_projection]

lemma restriction_surjective (A : ArtinianTest k K) :
    Function.Surjective (restriction ε hε A) := by
  intro α
  obtain ⟨n, hn⟩ := LocalAdicArtinianTests.exists_bound ε hε α.val α.property
  exact ⟨extensionAt ε hε α n hn, restriction_extensionAt ε hε α n hn⟩

lemma restriction_injective (A : ArtinianTest k K) :
    Function.Injective (restriction ε hε A) := by
  intro α β h
  obtain ⟨n, hn⟩ := LocalAdicArtinianTests.exists_bound
    (augmentation ε hε) (augmentation_surjective ε hε) α.val α.property
  obtain ⟨p, hp⟩ := LocalAdicArtinianTests.exists_bound
    (augmentation ε hε) (augmentation_surjective ε hε) β.val β.property
  apply Subtype.ext
  apply AlgHom.ext
  intro s
  obtain ⟨r, hr⟩ := exists_approximation ε hε (max n p) s
  have hα : s - sourceMap (k := k) r ∈ RingHom.ker α.val.toRingHom :=
    hn ((Ideal.pow_le_pow_right (Nat.add_le_add_right (le_max_left n p) 1)) hr)
  have hβ : s - sourceMap (k := k) r ∈ RingHom.ker β.val.toRingHom :=
    hp ((Ideal.pow_le_pow_right (Nat.add_le_add_right (le_max_right n p) 1)) hr)
  have hα' : α.val s = α.val (sourceMap (k := k) r) := by
    change α.val (s - sourceMap (k := k) r) = 0 at hα
    rw [map_sub] at hα
    exact sub_eq_zero.mp hα
  have hβ' : β.val s = β.val (sourceMap (k := k) r) := by
    change β.val (s - sourceMap (k := k) r) = 0 at hβ
    rw [map_sub] at hβ
    exact sub_eq_zero.mp hβ
  exact hα'.trans ((DFunLike.congr_fun (congrArg Subtype.val h) r).trans hβ'.symm)

/-- Actual adic completion preserves all compatible maps to every Artinian test. -/
def mapEquiv (A : ArtinianTest k K) :
    Maps (augmentation ε hε) A ≃ Maps ε A :=
  Equiv.ofBijective (restriction ε hε A)
    ⟨restriction_injective ε hε A, restriction_surjective ε hε A⟩

@[simp]
lemma mapEquiv_apply (A : ArtinianTest k K) (α : Maps (augmentation ε hε) A) :
    mapEquiv ε hε A α = restriction ε hε A α := rfl

/-- The comparison commutes with every test arrow. -/
lemma mapEquiv_naturality {A B : ArtinianTest k K} (q : A ⟶ B)
    (α : Maps (augmentation ε hε) A) :
    mapEquiv ε hε B (postcomp (augmentation ε hε) q α) =
      postcomp ε q (mapEquiv ε hε A α) := rfl

/-- Every permitted finite-stage extension is the inverse of restriction. -/
lemma mapEquiv_symm_eq_extensionAt {A : ArtinianTest k K} (α : Maps ε A) (n : ℕ)
    (hn : IsLocalRing.maximalIdeal R ^ (n + 1) ≤ RingHom.ker α.val.toRingHom) :
    (mapEquiv ε hε A).symm α = extensionAt ε hε α n hn := by
  apply (mapEquiv ε hε A).injective
  rw [Equiv.apply_symm_apply, mapEquiv_apply, restriction_extensionAt]

end Langlands.AlgebraicGeometry.Deformation.AugmentedAdicCompletion
