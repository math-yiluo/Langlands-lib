import Langlands.CommutativeAlgebra.Popescu.AnnihilatorStabilizationStatement
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Proof of Ogoma's lemma on annihilators after localization

Let `K' = {m ∈ M | (r π²) • m = 0 for some r ∈ S}`, the elements whose image under `π²`
vanishes in `S⁻¹M`. It is a submodule of `M`, finitely generated because `A` is Noetherian
and `M` is finite. By hypothesis each generator `g` satisfies `(sᵍ π) • g = 0` for some
`sᵍ ∈ S`; the product `s` of these finitely many elements satisfies `(s π) • m = 0` for all
`m ∈ K'`. If `(t s π)² • m = 0` with `t ∈ S`, then `m ∈ K'` (witness `(t s)²`), so
`(s π) • m = 0` and hence `(t s π) • m = t • (s π) • m = 0`.
-/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- If each element of a finite set `G` is killed by `r * x` for some `r ∈ S`, then a single
`s ∈ S` has `s * x` killing every element of `G`. -/
theorem exists_mem_submonoid_mul_smul_eq_zero_of_finset {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (S : Submonoid A) (x : A) (G : Finset M)
    (hG : ∀ g ∈ G, ∃ r ∈ S, (r * x) • g = 0) :
    ∃ s ∈ S, ∀ g ∈ G, (s * x) • g = 0 := by
  classical
  induction G using Finset.induction_on with
  | empty => exact ⟨1, S.one_mem, fun g hg => absurd hg (Finset.notMem_empty g)⟩
  | insert a G _ ih =>
    obtain ⟨s, hs, hsG⟩ := ih fun g hg => hG g (Finset.mem_insert_of_mem hg)
    obtain ⟨r, hr, hra⟩ := hG a (Finset.mem_insert_self a G)
    refine ⟨r * s, S.mul_mem hr hs, fun g hg => ?_⟩
    rcases Finset.mem_insert.mp hg with rfl | hg
    · rw [show r * s * x = s * (r * x) by ring, mul_smul, hra, smul_zero]
    · rw [show r * s * x = r * (s * x) by ring, mul_smul, hsG g hg, smul_zero]

/-- Ogoma's lemma (Stacks, Tag 07FC): if `π` and `π²` have the same kernel on `S⁻¹M`, then
some `s ∈ S` makes `t s π` and `(t s π)²` have the same kernel on `M` for every `t ∈ S`. -/
theorem annihilatorStabilization : AnnihilatorStabilizationStatement.{u} := by
  intro A M _ _ _ _ _ S π h
  -- `K'`: the elements of `M` whose image under `π²` vanishes in `S⁻¹M`.
  let K' : Submodule A M :=
    { carrier := {m | ∃ r ∈ S, (r * π ^ 2) • m = 0}
      add_mem' := by
        rintro a b ⟨r, hr, ha⟩ ⟨r', hr', hb⟩
        refine ⟨r * r', S.mul_mem hr hr', ?_⟩
        have ha' : (r * r' * π ^ 2) • a = 0 := by
          rw [show r * r' * π ^ 2 = r' * (r * π ^ 2) by ring, mul_smul, ha, smul_zero]
        have hb' : (r * r' * π ^ 2) • b = 0 := by
          rw [show r * r' * π ^ 2 = r * (r' * π ^ 2) by ring, mul_smul, hb, smul_zero]
        rw [smul_add, ha', hb', add_zero]
      zero_mem' := ⟨1, S.one_mem, smul_zero _⟩
      smul_mem' := by
        rintro c m ⟨r, hr, hm⟩
        exact ⟨r, hr, by rw [smul_comm, hm, smul_zero]⟩ }
  have hK' : ∀ m, m ∈ K' ↔ ∃ r ∈ S, (r * π ^ 2) • m = 0 := fun _ => Iff.rfl
  -- `K'` is finitely generated since `M` is a Noetherian module.
  obtain ⟨G, hG⟩ := IsNoetherian.noetherian K'
  -- One element of `S` times `π` kills all generators, hence all of `K'`.
  obtain ⟨s, hs, hsG⟩ := exists_mem_submonoid_mul_smul_eq_zero_of_finset S π G
    fun g hg => h g ((hK' g).mp (hG ▸ Submodule.subset_span hg))
  have hsK' : K' ≤ LinearMap.ker (LinearMap.lsmul A M (s * π)) := by
    rw [← hG, Submodule.span_le]
    intro g hg
    simpa only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.lsmul_apply] using hsG g hg
  refine ⟨s, hs, fun t ht m hm => ?_⟩
  have hmK' : m ∈ K' := by
    refine (hK' m).mpr ⟨(t * s) ^ 2, pow_mem (S.mul_mem ht hs) 2, ?_⟩
    rw [show (t * s) ^ 2 * π ^ 2 = (t * s * π) ^ 2 by ring]
    exact hm
  have hsm : (s * π) • m = 0 := by
    simpa only [LinearMap.mem_ker, LinearMap.lsmul_apply] using hsK' hmK'
  rw [show t * s * π = t * (s * π) by ring, mul_smul, hsm, smul_zero]

end Langlands.CommutativeAlgebra.Popescu
