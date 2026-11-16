import Langlands.CommutativeAlgebra.EtaleDvrRootExtensions
import Mathlib.Algebra.Algebra.Subalgebra.Directed
import Mathlib.Order.Zorn

/-! # Maximal subalgebras preserving a uniformizer -/

noncomputable section

open IsLocalRing Module

namespace Langlands.CommutativeAlgebra

variable {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]

/-- The image of `t` is a nonunit and every element is zero or a power of that
image times a unit. -/
def FixedUniformizer (t : R) (S : Subalgebra R Ω) : Prop :=
  ¬ IsUnit (algebraMap R S t) ∧
    ∀ y : S, y = 0 ∨ ∃ (n : ℕ) (u : S), IsUnit u ∧ y = algebraMap R S t ^ n * u

namespace FixedUniformizer

theorem of_irreducible [IsDomain R] [IsDiscreteValuationRing R]
    {t : R} (ht : Irreducible t) :
    ¬ IsUnit t ∧ ∀ y : R, y = 0 ∨ ∃ (n : ℕ) (u : R), IsUnit u ∧ y = t ^ n * u := by
  refine ⟨ht.not_isUnit, fun y => ?_⟩
  by_cases hy : y = 0
  · exact Or.inl hy
  · obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy ht
    exact Or.inr ⟨n, u, u.isUnit, h.trans (mul_comm _ _)⟩

theorem bot [IsDomain R] [IsDiscreteValuationRing R] [FaithfulSMul R Ω]
    {t : R} (ht : Irreducible t) : FixedUniformizer t (⊥ : Subalgebra R Ω) := by
  let e := Algebra.botEquivOfInjective (FaithfulSMul.algebraMap_injective R Ω)
  have he : e (algebraMap R (⊥ : Subalgebra R Ω) t) = t := e.commutes t
  refine ⟨fun h => ht.not_isUnit (he ▸ h.map e), fun y => ?_⟩
  rcases (of_irreducible ht).2 (e y) with h0 | ⟨n, u, hu, h⟩
  · exact Or.inl (e.injective (by simpa using h0))
  · refine Or.inr ⟨n, e.symm u, hu.map e.symm, e.injective ?_⟩
    simpa only [map_mul, map_pow, he, e.apply_symm_apply] using h

theorem iSup {ι : Type*} [Nonempty ι] (S : ι → Subalgebra R Ω)
    (hS : ∀ i, FixedUniformizer t (S i)) (hdir : Directed (· ≤ ·) S) :
    FixedUniformizer t (⨆ i, S i) := by
  classical
  let U : Subalgebra R Ω := ⨆ i, S i
  have hmem (x : Ω) : x ∈ U ↔ ∃ i, x ∈ S i := by
    rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hdir]
    exact Set.mem_iUnion
  refine ⟨?_, fun y => ?_⟩
  · intro ht
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ht
    obtain ⟨i, hi⟩ := (hmem b).mp b.property
    apply (hS i).1
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨b, hi⟩, Subtype.ext ?_⟩
    exact congrArg (fun z : U => (z : Ω)) hb
  · obtain ⟨i, hi⟩ := (hmem y).mp y.property
    let z : S i := ⟨y, hi⟩
    let j : S i →ₐ[R] U := Subalgebra.inclusion (le_iSup S i)
    rcases (hS i).2 z with h0 | ⟨n, u, hu, h⟩
    · exact Or.inl (Subtype.ext (congrArg (fun z : S i => (z : Ω)) h0))
    · refine Or.inr ⟨n, j u, hu.map j, ?_⟩
      exact congrArg j h |>.trans (by rw [map_mul, map_pow, j.commutes])

theorem exists_maximal [IsDomain R] [IsDiscreteValuationRing R] [FaithfulSMul R Ω]
    {t : R} (ht : Irreducible t) :
    ∃ S : Subalgebra R Ω, Maximal (FixedUniformizer t) S := by
  classical
  apply zorn_le_nonempty₀ {S : Subalgebra R Ω | FixedUniformizer t S} ?_
    (⊥ : Subalgebra R Ω) (bot ht) |>.imp fun S h => h.2
  intro c hc hchain S₀ hS₀
  let : Nonempty c := ⟨⟨S₀, hS₀⟩⟩
  let F : c → Subalgebra R Ω := Subtype.val
  have hdir : Directed (· ≤ ·) F := by
    intro i j
    rcases hchain.total i.property j.property with h | h
    · exact ⟨j, h, le_rfl⟩
    · exact ⟨i, le_rfl, h⟩
  exact ⟨⨆ i, F i, iSup F (fun i => hc i.property) hdir,
    fun S hS => le_iSup F ⟨S, hS⟩⟩

theorem isDiscreteValuationRing [IsDomain R] [FaithfulSMul R Ω]
    {t : R} (ht : t ≠ 0) {S : Subalgebra R Ω} (hS : FixedUniformizer t S) :
    IsDiscreteValuationRing S := by
  apply DVRAlgebraicBaseChange.isDiscreteValuationRing_of_forall_eq_zero_or
    (algebraMap R S t) hS.1 ?_ hS.2
  intro h
  apply ht
  exact FaithfulSMul.algebraMap_injective R Ω
    (show algebraMap R Ω t = algebraMap R Ω 0 from
      (congrArg (fun z : S => (z : Ω)) h).trans (map_zero _).symm)

theorem isLocalHom [IsDomain R] [IsDiscreteValuationRing R]
    {t : R} (ht : Irreducible t) {S : Subalgebra R Ω} (hS : FixedUniformizer t S) :
    IsLocalHom (algebraMap R S) := by
  constructor
  intro r hr
  by_contra hru
  have hrm : r ∈ maximalIdeal R := (mem_maximalIdeal r).mpr hru
  rw [ht.maximalIdeal_eq, Ideal.mem_span_singleton] at hrm
  obtain ⟨a, rfl⟩ := hrm
  exact hS.1 (isUnit_of_mul_isUnit_left (by simpa only [map_mul] using hr))

theorem irreducible [IsDomain R] [FaithfulSMul R Ω]
    {t : R} {S : Subalgebra R Ω} (hS : FixedUniformizer t S)
    [IsDiscreteValuationRing S] : Irreducible (algebraMap R S t) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S
  rcases hS.2 π with h0 | ⟨n, u, hu, h⟩
  · exact (hπ.ne_zero h0).elim
  have hn : n ≠ 0 := by
    rintro rfl
    apply hπ.not_isUnit
    rw [h]
    simpa only [pow_zero, one_mul] using hu
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hdiv : algebraMap R S t ∣ π := by
    rw [h]
    exact dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.succ_ne_zero m)) _
  exact (hπ.dvd_iff.mp hdiv).resolve_left hS.1 |>.irreducible hπ

end FixedUniformizer

end Langlands.CommutativeAlgebra
