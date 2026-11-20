import Langlands.Representation.Archimedean.RealDiscreteSeparatedCore
import Langlands.Representation.Archimedean.RealTiedDiscreteScalarCommutantCases
import Langlands.Representation.Archimedean.RealSphericalCyclicProof

/-!
# The separated discrete-series case

A tied list `ds` of real blocks with separated discrete exponents is, up to permutation, a list
`nd` of non-discrete blocks followed by discrete-series blocks `Ds₀` (`exists_split`). Expanding
the blocks of `nd` into characters (`blockChars`), sorting the characters by parity
(`sortParity`) and the discrete-series data by decreasing absolute weight (`AbsRel`) gives data
satisfying `IsSepData`, so the sorted list has a scalar commutant
(`hasScalarCommutant_tgtList`). Permutations of tied lists and the expansion of weight-zero
blocks transfer the scalar commutant back to `ds` (`hasScalarCommutant_of_separated`).
With `RealSphericalCyclicProof.realSphericalCyclic` this proves
`RealTiedDiscreteSeparatedScalarCommutantStatement` (`realTiedDiscreteSeparatedScalarCommutant`).
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealDiscreteSeparated

open RealTiedScalarAssembly RealTemperedCommutantReduction

/-- `e` may precede `f` when sorting by decreasing absolute weight. -/
def AbsRel (e f : ComplexCharacterData) : Prop := f.weight.natAbs ≤ e.weight.natAbs

instance : DecidableRel AbsRel := fun e f =>
  inferInstanceAs (Decidable (f.weight.natAbs ≤ e.weight.natAbs))

instance : Std.Total AbsRel := ⟨fun e f => le_total f.weight.natAbs e.weight.natAbs⟩

instance : IsTrans ComplexCharacterData AbsRel := ⟨fun _ _ _ hab hbc => le_trans hbc hab⟩

/-- Every list of real blocks is a permutation of a list of non-discrete blocks followed by
discrete-series blocks. -/
theorem exists_split : ∀ ds : List RealBlock, ∃ (nd : List RealBlock)
    (Ds : List ComplexCharacterData), (nd ++ Ds.map RealBlock.induced).Perm ds ∧
      (∀ x ∈ nd, ¬ IsRealDiscreteSeriesBlock x) ∧ ∀ e ∈ Ds, e.weight ≠ 0
  | [] => ⟨[], [], by simp, by simp, by simp⟩
  | x :: ds => by
      obtain ⟨nd, Ds, hp, hnd, hDs⟩ := exists_split ds
      by_cases hx : IsRealDiscreteSeriesBlock x
      · rcases x with c | d
        · exact (hx : False).elim
        · refine ⟨nd, d :: Ds, ?_, hnd, ?_⟩
          · rw [List.map_cons]
            exact List.perm_middle.trans (hp.cons _)
          · intro e he
            rcases List.mem_cons.mp he with rfl | he
            · exact hx
            · exact hDs e he
      · refine ⟨x :: nd, Ds, ?_, ?_, hDs⟩
        · rw [List.cons_append]
          exact hp.cons x
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hx
          · exact hnd y hy

theorem exponent_of_mem_blockChars {x : RealBlock} {c : RealCharacterData}
    (hc : c ∈ blockChars x) : c.exponent = realBlockComplexExponent x := by
  rcases x with c' | d
  · simp only [blockChars, List.mem_singleton] at hc
    subst hc
    rfl
  · simp only [blockChars, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> rfl

theorem absWeight_ne_of_not_ds {x : RealBlock} (hx : ¬ IsRealDiscreteSeriesBlock x) {k : ℕ}
    (hk : 0 < k) : realBlockAbsWeight x ≠ some k := by
  rcases x with c | d
  · simp [realBlockAbsWeight]
  · simp only [IsRealDiscreteSeriesBlock, ne_eq, not_not] at hx
    simp only [realBlockAbsWeight, hx, Int.natAbs_zero, ne_eq, Option.some.injEq]
    omega

/-- **The separated case**, given spherical cyclicity. -/
theorem hasScalarCommutant_of_separated (hS : RealSphericalCyclicStatement) (n : ℕ)
    (ds : List RealBlock) (hrank : realRank ds = n)
    (htied : ∀ x ∈ ds, ∀ y ∈ ds, realBlockExponent x = realBlockExponent y)
    (hsep : IsRealDiscreteExponentSeparated ds) : HasScalarCommutant n ds := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, ∀ x ∈ ds, realBlockExponent x = r := by
    rcases ds with _ | ⟨x₀, ds'⟩
    · exact ⟨0, by simp⟩
    · exact ⟨realBlockExponent x₀, fun x hx => htied x hx x₀ (by simp)⟩
  obtain ⟨nd, Ds0, hp, hnd, hDs0⟩ := exists_split ds
  set X := Ds0.map RealBlock.induced with hX
  set cs0 := nd.flatMap blockChars with hcs0
  set cs := sortParity cs0 with hcs
  set Ds := Ds0.insertionSort AbsRel with hDs
  have hDperm : Ds.Perm Ds0 := List.perm_insertionSort AbsRel Ds0
  have hmem_nd : ∀ x ∈ nd, x ∈ ds := fun x hx => hp.subset (List.mem_append_left _ hx)
  have hmem_X : ∀ x ∈ X, x ∈ ds := fun x hx => hp.subset (List.mem_append_right _ hx)
  have hmem_D : ∀ e ∈ Ds, RealBlock.induced e ∈ ds := fun e he =>
    hmem_X _ (List.mem_map_of_mem (hDperm.subset he))
  have hw : ∀ e ∈ Ds, e.weight ≠ 0 := fun e he => hDs0 e (hDperm.subset he)
  have hcs0_re : ∀ c ∈ cs0, c.exponent.re = r := by
    intro c hc
    obtain ⟨x, hx, hcx⟩ := List.mem_flatMap.mp hc
    rw [exponent_re_of_mem_blockChars hcx, hr x (hmem_nd x hx)]
  have hcs_mem : ∀ c ∈ cs, ∃ x ∈ nd, c ∈ blockChars x := fun c hc =>
    List.mem_flatMap.mp ((sortParity_perm cs0).subset hc)
  have hsd : IsSepData r cs Ds := by
    refine ⟨fun c hc => hcs0_re c ((sortParity_perm cs0).subset hc),
      fun e he => hr _ (hmem_D e he), pairwise_sortParity cs0,
      List.pairwise_insertionSort AbsRel Ds0, ?_, ?_, ?_⟩
    · intro e he
      have := hw e he
      omega
    · intro c hc e he hce
      obtain ⟨x, hx, hcx⟩ := hcs_mem c hc
      have h1 := hsep (.induced e) (hmem_D e he) (hw e he) x (hmem_nd x hx)
        (by rw [← exponent_of_mem_blockChars hcx, hce]; rfl)
      exact absWeight_ne_of_not_ds (hnd x hx) (by have := hw e he; omega) h1
    · intro e he f hf hef
      have h1 := hsep (.induced e) (hmem_D e he) (hw e he) (.induced f) (hmem_D f hf) hef.symm
      simp only [realBlockAbsWeight, Option.some.injEq] at h1
      exact h1.symm
  -- the length count
  have hexp : nd.flatMap realBlockExpand = cs0.map RealBlock.character :=
    flatMap_expand_eq nd hnd
  have hcs0_len : cs0.length = realRank nd := by
    rw [← realRank_map_character, ← hexp, realRank_flatMap_expand]
  have hrank' : realRank nd + 2 * Ds0.length = n := by
    rw [← hrank, ← realRank_perm hp, Langlands.LocalFactor.Archimedean.realRank_append,
      realRank_map_induced]
  have hcs_len : cs.length = cs0.length := (sortParity_perm cs0).length_eq
  have hDs_len : Ds.length = Ds0.length := hDperm.length_eq
  have hn : Ds.length + cs.length + Ds.length = n := by omega
  have hcore := hasScalarCommutant_tgtList hS hsd hn
  -- permute to `X ++ cs0`
  have hperm1 : (tgtList cs Ds).Perm (X ++ cs0.map RealBlock.character) := by
    refine List.perm_append_comm.trans (List.Perm.append ?_ ?_)
    · exact ((List.reverse_perm Ds).trans hDperm).map _
    · exact (sortParity_perm cs0).map _
  have htied1 : ∀ x ∈ X ++ cs0.map RealBlock.character, realBlockExponent x = r := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hr x (hmem_X x hx)
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact hcs0_re c hc
  have h2 : HasScalarCommutant n (X ++ cs0.map RealBlock.character) :=
    hasScalarCommutant_perm (r := r) hperm1 (by rw [realRank_tgtList]; omega)
      (fun x hx => htied1 x (hperm1.subset hx)) hcore
  -- expand the non-discrete blocks
  have hmod : realStandardModule n (X ++ nd) =
      realStandardModule n (X ++ cs0.map RealBlock.character) := by
    rw [← hexp]
    exact realStandardModule_append_flatMap_expand n nd X
  have h3 : HasScalarCommutant n (X ++ nd) :=
    hasScalarCommutant_of_twoWay ((RealInjectiveIntertwinerExists.refl n _).of_eq rfl hmod.symm)
      ((RealInjectiveIntertwinerExists.refl n _).of_eq rfl hmod) h2
  -- permute back to `ds`
  have hperm2 : (X ++ nd).Perm ds := List.perm_append_comm.trans hp
  exact hasScalarCommutant_perm (r := r) hperm2 (by rw [realRank_perm hperm2, hrank])
    (fun x hx => hr x (hperm2.subset hx)) h3

end RealDiscreteSeparated

/-- The reduction of the separated discrete-series case to spherical cyclicity. -/
theorem realTiedDiscreteSeparated_of_sphericalCyclic (hS : RealSphericalCyclicStatement) :
    RealTiedDiscreteSeparatedScalarCommutantStatement :=
  fun n ds hrank htied _ hsep =>
    RealDiscreteSeparated.hasScalarCommutant_of_separated hS n ds hrank htied hsep

/-- **The separated discrete-series case.** A tied list of real blocks containing a
discrete-series block, whose discrete exponents are separated, has a scalar commutant. -/
theorem realTiedDiscreteSeparatedScalarCommutant :
    RealTiedDiscreteSeparatedScalarCommutantStatement :=
  realTiedDiscreteSeparated_of_sphericalCyclic RealSphericalCyclicProof.realSphericalCyclic

end Langlands.Archimedean
