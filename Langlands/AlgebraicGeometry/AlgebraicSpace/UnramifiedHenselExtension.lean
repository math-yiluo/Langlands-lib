import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Henselian monic extensions of complete local rings

Let `O` be a local ring, complete for its maximal ideal `𝔪`, and let `m ∈ O[X]` be monic with
irreducible reduction modulo `𝔪`. Then `O[X]/(m)` is a local ring with maximal ideal `𝔪 O[X]/(m)`,
free of rank `deg m` over `O`, complete for its maximal ideal, hence henselian. This supplies the henselianity needed for
the lifted residue extensions in the proof of Conrad's Proposition 5.2. No étaleness
conclusion is asserted here.
-/

noncomputable section

universe u

open Polynomial Module

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace UnramifiedHensel

section Basis

variable {O S : Type u} [CommRing O] [CommRing S] [Algebra O S] {ι : Type*} [Fintype ι]

/-- With a basis, an element lies in the extension of an ideal exactly when all its
coordinates lie in the ideal. -/
theorem mem_map_iff (b : Basis ι O S) (I : Ideal O) (x : S) :
    x ∈ I.map (algebraMap O S) ↔ ∀ k, b.repr x k ∈ I := by
  constructor
  · intro hx
    have hx' : x ∈ I • (⊤ : Submodule O S) := by
      rw [Ideal.smul_top_eq_map]
      exact hx
    refine Submodule.smul_induction_on (p := fun y => ∀ k, b.repr y k ∈ I) hx' ?_ ?_
    · intro a ha s _ k
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ ha
    · intro y z hy hz k
      rw [map_add, Finsupp.add_apply]
      exact I.add_mem (hy k) (hz k)
  · intro h
    rw [← b.sum_repr x]
    refine Ideal.sum_mem _ fun k _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (h k))

/-- The extension of the powers of an ideal. -/
theorem mem_pow_map_iff (b : Basis ι O S) (I : Ideal O) (n : ℕ) (x : S) :
    x ∈ I.map (algebraMap O S) ^ n ↔ ∀ k, b.repr x k ∈ I ^ n := by
  rw [← Ideal.map_pow, mem_map_iff b]

/-- A finite free algebra over an adically complete ring is adically complete for the extended
ideal. -/
theorem isAdicComplete (b : Basis ι O S) (I : Ideal O) [IsAdicComplete I O] :
    IsAdicComplete (I.map (algebraMap O S)) S := by
  have hsm : ∀ (n : ℕ) (x y : S), x ≡ y [SMOD (I.map (algebraMap O S) ^ n •
      (⊤ : Submodule S S))] ↔ ∀ k, b.repr x k ≡ b.repr y k [SMOD (I ^ n • (⊤ : Submodule O O))] := by
    intro n x y
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_pow_map_iff b, map_sub,
      Finsupp.sub_apply]
  have hH : IsHausdorff (I.map (algebraMap O S)) S := by
    refine ⟨fun x hx => ?_⟩
    have h0 : ∀ k, b.repr x k = 0 := by
      intro k
      apply IsHausdorff.haus (inferInstance : IsHausdorff I O)
      intro n
      have := (hsm n x 0).mp (hx n) k
      simpa using this
    rw [← b.sum_repr x]
    simp [h0]
  have hP : IsPrecomplete (I.map (algebraMap O S)) S := by
    refine ⟨fun f hf => ?_⟩
    have hcoord : ∀ k, ∃ L : O, ∀ n, b.repr (f n) k ≡ L [SMOD (I ^ n • (⊤ : Submodule O O))] := by
      intro k
      exact IsPrecomplete.prec (inferInstance : IsPrecomplete I O)
        (fun {m n} hmn => (hsm m (f m) (f n)).mp (hf hmn) k)
    choose L hL using hcoord
    refine ⟨∑ k, L k • b k, fun n => (hsm n _ _).mpr fun k => ?_⟩
    have : b.repr (∑ k, L k • b k) k = L k := by
      rw [b.repr_sum_self]
    rw [this]
    exact hL k n
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

end Basis

section Local

variable {O : Type u} [CommRing O] [IsLocalRing O] (m : O[X])

/-- The reduction of `m` modulo the maximal ideal. -/
abbrev reduction : (IsLocalRing.ResidueField O)[X] := m.map (IsLocalRing.residue O)

variable [hirr : Fact (Irreducible (reduction m))]

include hirr in
/-- The extension of the maximal ideal is maximal. -/
theorem isMaximal_map : (Ideal.map (algebraMap O (AdjoinRoot m))
    (IsLocalRing.maximalIdeal O)).IsMaximal := by
  have e := AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (IsLocalRing.maximalIdeal O) m
  have hmax : (Ideal.span ({reduction m} : Set (IsLocalRing.ResidueField O)[X])).IsMaximal :=
    AdjoinRoot.span_maximal_of_irreducible
  have hfield := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact MulEquiv.isField hfield e.toMulEquiv

variable (hm : m.Monic)

include hirr hm in
/-- `O[X]/(m)` is a local ring. -/
theorem isLocalRing : IsLocalRing (AdjoinRoot m) := by
  have : Module.Finite O (AdjoinRoot m) := (AdjoinRoot.powerBasis' hm).finite
  have : Algebra.IsIntegral O (AdjoinRoot m) := Algebra.IsIntegral.of_finite O _
  have hmax := isMaximal_map m
  refine IsLocalRing.of_unique_max_ideal ⟨_, hmax, fun M hM => ?_⟩
  have hunder : (M.under O).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
  have hle : Ideal.map (algebraMap O (AdjoinRoot m)) (IsLocalRing.maximalIdeal O) ≤ M := by
    rw [Ideal.map_le_iff_le_comap]
    exact (IsLocalRing.eq_maximalIdeal hunder).symm.le
  exact (hmax.eq_of_le hM.ne_top hle).symm

include hirr hm in
theorem maximalIdeal_eq :
    let := isLocalRing m hm
    IsLocalRing.maximalIdeal (AdjoinRoot m) =
      Ideal.map (algebraMap O (AdjoinRoot m)) (IsLocalRing.maximalIdeal O) := by
  let := isLocalRing m hm
  exact (IsLocalRing.eq_maximalIdeal (isMaximal_map m)).symm

include hirr hm in
/-- A monic extension with irreducible reduction of a complete local ring is henselian. -/
theorem henselianLocalRing [IsAdicComplete (IsLocalRing.maximalIdeal O) O] :
    let := isLocalRing m hm
    HenselianLocalRing (AdjoinRoot m) := by
  let := isLocalRing m hm
  have hc : IsAdicComplete (IsLocalRing.maximalIdeal (AdjoinRoot m)) (AdjoinRoot m) := by
    rw [maximalIdeal_eq m hm]
    exact isAdicComplete (AdjoinRoot.powerBasis' hm).basis _
  constructor
  intro f hf a₀ hroot hsimple
  exact HenselianRing.is_henselian f hf a₀ hroot
    (hsimple.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (AdjoinRoot m))))

end Local

end UnramifiedHensel

end Langlands.AlgebraicGeometry.AlgebraicSpace
