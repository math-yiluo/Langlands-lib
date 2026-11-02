import Langlands.AlgebraicGeometry.GroupoidCoactionCokernel
import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.Support

/-! # Coactions modulo invariant ideals -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}
variable {M : Type v} [AddCommGroup M] [Module B M]

/-- A coaction descends to a quotient whenever its composite with tensoring
the quotient map vanishes on the submodule. -/
def quotientSemilinearMap (θ : GroupoidCoaction t M) (P : Submodule B M)
    (hP : ∀ m ∈ P, LinearMap.lTensor C P.mkQ (θ.coaction m) = 0) :
    M ⧸ P →ₛₗ[t] C ⊗[B] (M ⧸ P) :=
  P.liftQ ((AlgebraTensorModule.lTensor C C P.mkQ).comp θ.semilinearMap) hP

@[simp]
lemma quotientSemilinearMap_mkQ (θ : GroupoidCoaction t M) (P : Submodule B M)
    (hP : ∀ m ∈ P, LinearMap.lTensor C P.mkQ (θ.coaction m) = 0) (m : M) :
    quotientSemilinearMap θ P hP (P.mkQ m) =
      LinearMap.lTensor C P.mkQ (θ.coaction m) :=
  rfl

/-- The actual coaction on the quotient by a stable submodule. -/
def quotient (θ : GroupoidCoaction t M) (P : Submodule B M)
    (hP : ∀ m ∈ P, LinearMap.lTensor C P.mkQ (θ.coaction m) = 0) :
    GroupoidCoaction t (M ⧸ P) :=
  ofSurjective θ P.mkQ P.mkQ_surjective
    (quotientSemilinearMap θ P hP).toAddMonoidHom
    (fun b m => (quotientSemilinearMap θ P hP).map_smulₛₗ b m)
    (quotientSemilinearMap_mkQ θ P hP)

lemma quotient_mkQ_isHom (θ : GroupoidCoaction t M) (P : Submodule B M)
    (hP : ∀ m ∈ P, LinearMap.lTensor C P.mkQ (θ.coaction m) = 0) :
    θ.IsHom (quotient θ P hP) P.mkQ :=
  quotientSemilinearMap_mkQ θ P hP

/-- Source-extension of an ideal annihilates the tensor of its module quotient. -/
lemma map_source_le_annihilator_tensor_quotient (I : Ideal B) :
    I.map (algebraMap B C) ≤
      Module.annihilator C (C ⊗[B] (M ⧸ (I • ⊤ : Submodule B M))) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  apply Module.mem_annihilator.mpr
  intro x
  induction x with
  | tmul c q =>
    obtain ⟨m, rfl⟩ := (I • (⊤ : Submodule B M)).mkQ_surjective q
    change algebraMap B C a •
      (c ⊗ₜ[B] (I • (⊤ : Submodule B M)).mkQ m) = 0
    rw [IsScalarTower.algebraMap_smul, ← tmul_smul,
      ← (I • (⊤ : Submodule B M)).mkQ.map_smul a m]
    have hzero : (I • (⊤ : Submodule B M)).mkQ (a • m) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr
        (Submodule.smul_mem_smul ha (Submodule.mem_top : m ∈ (⊤ : Submodule B M)))
    rw [hzero, tmul_zero]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- Equality of the two extended ideals is stronger than needed: the target
extension being contained in the source extension suffices for reduction. -/
lemma ideal_smul_top_stable (θ : GroupoidCoaction t M) (I : Ideal B)
    (hI : I.map t ≤ I.map (algebraMap B C)) :
    ∀ m ∈ (I • ⊤ : Submodule B M),
      LinearMap.lTensor C (I • (⊤ : Submodule B M)).mkQ (θ.coaction m) = 0 := by
  intro m hm
  refine Submodule.smul_induction_on hm ?_ ?_
  · intro a ha n _
    rw [θ.map_smul, lTensor_alg_smul]
    exact Module.mem_annihilator.mp
      (map_source_le_annihilator_tensor_quotient (M := M) I
        (hI (Ideal.mem_map_of_mem t ha))) _
  · intro x y hx hy
    simp [hx, hy]

/-- Reduction of a coaction modulo an ideal with invariant extension. -/
def idealQuotient (θ : GroupoidCoaction t M) (I : Ideal B)
    (hI : I.map t ≤ I.map (algebraMap B C)) :
    GroupoidCoaction t (M ⧸ (I • ⊤ : Submodule B M)) :=
  quotient θ (I • ⊤) (ideal_smul_top_stable θ I hI)

lemma idealQuotient_mkQ_isHom (θ : GroupoidCoaction t M) (I : Ideal B)
    (hI : I.map t ≤ I.map (algebraMap B C)) :
    θ.IsHom (idealQuotient θ I hI) (I • (⊤ : Submodule B M)).mkQ :=
  quotient_mkQ_isHom θ (I • ⊤) (ideal_smul_top_stable θ I hI)

/-- Acyclicity makes every invariant of the ideal quotient lift to an invariant. -/
lemma idealQuotient_invariantsMap_surjective
    (hE : RingEtaleEquivalenceRelation t)
    (hacyclic : ∀ (K : Type v) [AddCommGroup K] [Module B K]
      (θK : GroupoidCoaction t K), θK.IsAcyclic)
    (θ : GroupoidCoaction t M) (I : Ideal B)
    (hI : I.map t ≤ I.map (algebraMap B C)) :
    Function.Surjective (θ.invariantsMap (idealQuotient θ I hI)
      (I • (⊤ : Submodule B M)).mkQ (idealQuotient_mkQ_isHom θ I hI)) :=
  invariantsMap_surjective hE hacyclic θ (idealQuotient θ I hI)
    (I • (⊤ : Submodule B M)).mkQ (idealQuotient_mkQ_isHom θ I hI)
    (I • (⊤ : Submodule B M)).mkQ_surjective

/-- A nonzero invariant in the ideal quotient lifts to a nonzero invariant in
the original module. -/
lemma exists_nonzero_invariant_of_idealQuotient
    (hE : RingEtaleEquivalenceRelation t)
    (hacyclic : ∀ (K : Type v) [AddCommGroup K] [Module B K]
      (θK : GroupoidCoaction t K), θK.IsAcyclic)
    (θ : GroupoidCoaction t M) (I : Ideal B)
    (hI : I.map t ≤ I.map (algebraMap B C))
    (hq : ∃ q, q ∈ (idealQuotient θ I hI).invariants ∧ q ≠ 0) :
    ∃ m, m ∈ θ.invariants ∧ m ≠ 0 := by
  obtain ⟨q, hq, hq0⟩ := hq
  obtain ⟨m, hm⟩ :=
    idealQuotient_invariantsMap_surjective hE hacyclic θ I hI ⟨q, hq⟩
  refine ⟨m, m.property, ?_⟩
  intro hm0
  apply hq0
  have heq := congrArg Subtype.val hm
  simpa [hm0] using heq.symm

/-- For a finite module, meeting its support ensures that reduction by the
ideal remains nonzero. -/
lemma idealQuotient_nontrivial_of_mem_support [Module.Finite B M]
    (I : Ideal B) (p : PrimeSpectrum B) (hp : p ∈ Module.support B M)
    (hIp : I ≤ p.asIdeal) :
    Nontrivial (M ⧸ (I • ⊤ : Submodule B M)) := by
  apply (Module.nonempty_support_iff
    (R := B) (M := M ⧸ (I • ⊤ : Submodule B M))).mp
  refine ⟨p, ?_⟩
  rw [Module.support_quotient]
  exact ⟨hp, hIp⟩

end Langlands.AlgebraicGeometry.GroupoidCoaction
