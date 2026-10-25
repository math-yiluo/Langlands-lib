import Langlands.Representation.Jacquet.RefinedOppositePowerKernelProof
import Langlands.Representation.Jacquet.CanonicalLiftBijectivityProof

namespace Langlands.Jacquet

open GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- A common inverse scalar power makes the whole compact upper product fix a vector. -/
theorem exists_refined_inverse_scalar_pow_upper_fixed
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ (ρ : Representation ℂ (B.Levi F.Carrier) V), IsSmooth ρ →
      ∀ (K : ∀ i, OpenSubgroup (GeneralLinear (B.size i) F.Carrier)),
      (∀ i, IsCompact (K i : Set (GeneralLinear (B.size i) F.Carrier))) →
      ∀ a : ∀ i, Fin (S i).length → F.Carrierˣ,
        (∀ i, (S i).IsStrictlyContracting T (a i)) →
        ∀ v : V, ∃ s : ℕ, ∀ u : B.Levi F.Carrier,
          (∀ i, u i ∈ (S i).iwahoriUpper F.Carrier (K i).toSubgroup) →
          let g : B.Levi F.Carrier := fun i => ((S i).blockScalar F.Carrier (a i))⁻¹
          ρ u (ρ (g ^ s) v) = ρ (g ^ s) v := by
  classical
  let := T.topology
  let := T.leviTopologicalGroup B
  intro ρ hρ K hK a ha v
  obtain ⟨U, hU⟩ := hρ v
  obtain ⟨L, -, -, hLU⟩ := CuspidalSupport.exists_leviPiOpenSubgroup_subset T B S
    (U.isOpen.mem_nhds U.one_mem)
  have hcomponent (i : Fin B.length) : ∃ r : ℕ, ∀ s : ℕ, r ≤ s →
      ∀ u ∈ (S i).iwahoriUpper F.Carrier (K i).toSubgroup,
        (S i).blockScalar F.Carrier (a i) ^ s * u *
          ((S i).blockScalar F.Carrier (a i) ^ s)⁻¹ ∈ L i := by
    have hclosed : IsClosed ((S i).unipotentSubgroup F.Carrier :
        Set (GeneralLinear (B.size i) F.Carrier)) := by
      let := T.valuativeRel
      let := T.localField
      let := T.fieldT2
      exact (S i).isClosed_unipotentSubgroup F.Carrier
    have hUc : IsCompact ((S i).iwahoriUpper F.Carrier (K i).toSubgroup :
        Set (GeneralLinear (B.size i) F.Carrier)) := (hK i).inter_right hclosed
    obtain ⟨ε, hε, -, hc⟩ := (S i).uniformCompactBlockContraction T
      ((S i).iwahoriUpper F.Carrier (K i).toSubgroup :
        Set (GeneralLinear (B.size i) F.Carrier)) ∅
      hUc (fun u hu => hu.2) isCompact_empty (Set.empty_subset _)
      (L i : Set (GeneralLinear (B.size i) F.Carrier))
      ((L i).isOpen.mem_nhds (L i).one_mem)
    obtain ⟨r, hr⟩ := (S i).strictPowersEventuallyDeep T (a i) (ha i) ε hε
    refine ⟨r, fun s hs u hu => ?_⟩
    have h := (hc (fun j => a i j ^ s) (hr s hs)).1 u hu
    have hp : (S i).blockScalar F.Carrier (fun j => a i j ^ s) =
        (S i).blockScalar F.Carrier (a i) ^ s := map_pow _ _ _
    change (S i).blockScalar F.Carrier (fun j => a i j ^ s) * u *
      ((S i).blockScalar F.Carrier (fun j => a i j ^ s))⁻¹ ∈ L i at h
    simpa only [hp] using h
  choose r hr using hcomponent
  let s := Finset.univ.sup r
  let g : B.Levi F.Carrier := fun i => ((S i).blockScalar F.Carrier (a i))⁻¹
  refine ⟨s, fun u hu => ?_⟩
  have huU : (g ^ s)⁻¹ * u * g ^ s ∈ U := by
    apply hLU
    apply (CuspidalSupport.mem_leviPiOpenSubgroup T B L _).mpr
    intro i
    have hi := hr i s (Finset.le_sup (Finset.mem_univ i)) (u i) (hu i)
    simpa only [g, Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, inv_pow, inv_inv] using hi
  calc
    ρ u (ρ (g ^ s) v) = ρ (g ^ s) (ρ ((g ^ s)⁻¹ * u * g ^ s) v) := by
      simp only [← Module.End.mul_apply, ← map_mul ρ]
      congr 1
      group
    _ = ρ (g ^ s) v := congrArg (ρ (g ^ s)) (hU ⟨_, huU⟩)

/-- Product opposite canonical lifts when the fixed space alone is finite dimensional. -/
theorem refinedOppositeStableImage_bijective_of_finiteDimensional
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ (ρ : Representation ℂ (B.Levi F.Carrier) V) (hρ : IsSmooth ρ)
      (K : ∀ i, OpenSubgroup (GeneralLinear (B.size i) F.Carrier))
      (hK : ∀ i, IsCompact (K i : Set (GeneralLinear (B.size i) F.Carrier))),
      FiniteDimensional ℂ (fixedVectors ρ
        (CuspidalSupport.leviPiOpenSubgroup T B K).toSubgroup) →
      (∀ i, (S i).HasBlockIwahoriFactorization T (K i)) →
      ∀ a : ∀ i, Fin (S i).length → F.Carrierˣ,
        (∀ i, (S i).IsStrictlyContracting T (a i)) →
        let KP := CuspidalSupport.leviPiOpenSubgroup T B K
        let hKP := CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK
        let g : B.Levi F.Carrier := fun i => ((S i).blockScalar F.Carrier (a i))⁻¹
        Function.Bijective (stableImageJacquetMap ρ hρ KP hKP g
          (refinedOppositeUnipotent F.Carrier B S) (refinedLevi F.Carrier B S)
          (fun m hm => (refinedOppositeLeviNormalizer F.Carrier B S ⟨m, hm⟩).property)) := by
  classical
  let := T.topology
  let := T.leviTopologicalGroup B
  intro ρ hρ K hK hfin hfac a ha
  let KP := CuspidalSupport.leviPiOpenSubgroup T B K
  let hKP := CuspidalSupport.isCompact_leviPiOpenSubgroup T B K hK
  let N := refinedOppositeUnipotent F.Carrier B S
  let M := refinedLevi F.Carrier B S
  let hMN : M ≤ Subgroup.normalizer (N : Set (B.Levi F.Carrier)) :=
    fun m hm => (refinedOppositeLeviNormalizer F.Carrier B S ⟨m, hm⟩).property
  let g : B.Levi F.Carrier := fun i => ((S i).blockScalar F.Carrier (a i))⁻¹
  let gm : M := ⟨g, fun i _ => (S i).leviSubgroup F.Carrier |>.inv_mem
    ((S i).blockScalarInLevi F.Carrier (a i)).property⟩
  change Function.Bijective (stableImageJacquetMap ρ hρ KP hKP g N M hMN)
  have hcompl := powerKernelSup_isCompl_stableImage ρ hρ KP hKP g hfin
  have hker := refinedOppositePowerKernel_eq_jacquetKernel F T B S V ρ hρ K hK hfac a ha
  change powerKernelSup ρ hρ KP hKP g =
    LinearMap.ker (fixedJacquetMap ρ N M hMN KP.toSubgroup) at hker
  have hsplit : ∀ x : fixedVectors ρ KP.toSubgroup,
      ∃ t : stableImage ρ hρ KP hKP g,
        mk ρ N ((t : fixedVectors ρ KP.toSubgroup) : V) = mk ρ N (x : V) := by
    intro x
    have hx : x ∈ powerKernelSup ρ hρ KP hKP g ⊔ stableImage ρ hρ KP hKP g := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨k, hk, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [hker, LinearMap.mem_ker] at hk
    have hk0 : mk ρ N (k : V) = 0 := congrArg Subtype.val hk
    rw [Submodule.coe_add, map_add, hk0, zero_add]
  have hstep : ∀ z : Coinvariants ρ N,
      (∃ t : stableImage ρ hρ KP hKP g,
        mk ρ N ((t : fixedVectors ρ KP.toSubgroup) : V) = action ρ N M hMN gm z) →
      ∃ t : stableImage ρ hρ KP hKP g,
        mk ρ N ((t : fixedVectors ρ KP.toSubgroup) : V) = z := by
    rintro z ⟨t, htz⟩
    obtain ⟨t', rfl⟩ := (stableImageAction_bijective ρ hρ KP hKP g hfin).2 t
    refine ⟨t', ?_⟩
    apply (Representation.apply_bijective (action ρ N M hMN) gm).injective
    rw [← htz]
    exact ((refinedOppositeCompression p F T n B S V ρ hρ K hK hfac).2
      a (fun i => (ha i).weak) (t' : fixedVectors ρ KP.toSubgroup)).symm
  have hpow : ∀ (s : ℕ) (z : Coinvariants ρ N),
      (∃ t : stableImage ρ hρ KP hKP g,
        mk ρ N ((t : fixedVectors ρ KP.toSubgroup) : V) = action ρ N M hMN (gm ^ s) z) →
      ∃ t : stableImage ρ hρ KP hKP g,
        mk ρ N ((t : fixedVectors ρ KP.toSubgroup) : V) = z := by
    intro s
    induction s with
    | zero =>
      intro z hz
      simpa using hz
    | succ s ih =>
      intro z hz
      apply hstep
      apply ih
      simpa only [pow_succ, map_mul, Module.End.mul_apply] using hz
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro t ht
    have h1 : (t : fixedVectors ρ KP.toSubgroup) ∈
        LinearMap.ker (fixedJacquetMap ρ N M hMN KP.toSubgroup) := ht
    rw [← hker] at h1
    have h0 := hcompl.disjoint.le_bot ⟨h1, t.property⟩
    exact Subtype.ext (by simpa using h0)
  · intro y
    suffices h : ∃ t : stableImage ρ hρ KP hKP g,
        mk ρ N ((t : fixedVectors ρ KP.toSubgroup) : V) = (y : Coinvariants ρ N) by
      obtain ⟨t, ht⟩ := h
      exact ⟨t, Subtype.ext ht⟩
    obtain ⟨v, hv⟩ := mk_surjective ρ N (y : Coinvariants ρ N)
    obtain ⟨s, hs⟩ := exists_refined_inverse_scalar_pow_upper_fixed F T B S V ρ hρ K hK a ha v
    have hlevi : ∀ m : B.Levi F.Carrier, m ∈ KP → m ∈ M →
        mk ρ N (ρ m (ρ (g ^ s) v)) = action ρ N M hMN (gm ^ s) (y : Coinvariants ρ N) := by
      intro m hmK hmM
      have hc0 : g * m = m * g := by
        funext i
        apply Commute.inv_left
        exact blockScalar_mul_eq_of_mem_leviSubgroup F (S i) (a i) (hmM i (Set.mem_univ i))
      have hc : m * g ^ s = g ^ s * m := (Commute.pow_left hc0 s).symm
      have hgs : ((gm ^ s : M) : B.Levi F.Carrier) = g ^ s := by simp [gm]
      have hy := y.property ⟨⟨m, hmM⟩, hmK⟩
      calc
        mk ρ N (ρ m (ρ (g ^ s) v)) =
            mk ρ N (ρ (gm ^ s : M) (ρ m v)) := by
          rw [hgs, ← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
        _ = action ρ N M hMN (gm ^ s) (action ρ N M hMN ⟨m, hmM⟩ (mk ρ N v)) := by
          rw [action_mk, action_mk]
        _ = _ := by
          rw [hv]
          exact congrArg _ hy
    have hconst : ∀ k : KP, mk ρ N (ρ k.val (ρ (g ^ s) v)) =
        action ρ N M hMN (gm ^ s) (y : Coinvariants ρ N) := by
      intro k
      have hk := (CuspidalSupport.mem_leviPiOpenSubgroup T B K k.val).mp k.property
      choose z hz using fun i => (hfac i).1.2 ⟨k.val i, hk i⟩
      let l : B.Levi F.Carrier := fun i => (z i).1.val
      let m : B.Levi F.Carrier := fun i => (z i).2.1.val
      let u : B.Levi F.Carrier := fun i => (z i).2.2.val
      have hprod : k.val = l * (m * u) := by
        funext i
        exact (congrArg Subtype.val (hz i)).symm.trans (mul_assoc _ _ _)
      have hlN : l ∈ N := (mem_refinedOppositeUnipotent F.Carrier B S l).mpr
        fun i => (z i).1.property.2
      have hmK : m ∈ KP := (CuspidalSupport.mem_leviPiOpenSubgroup T B K m).mpr
        fun i => (z i).2.1.property.1
      have hmM : m ∈ M := fun i _ => (z i).2.1.property.2
      have hu : ρ u (ρ (g ^ s) v) = ρ (g ^ s) v := hs u fun i => (z i).2.2.property
      rw [hprod, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hu]
      rw [mk_apply_subgroup ρ N ⟨l, hlN⟩]
      exact hlevi m hmK hmM
    apply hpow s
    obtain ⟨t, ht⟩ := hsplit ⟨Compact.averageMap ρ hρ KP hKP (ρ (g ^ s) v),
      Compact.averageMap_mem_fixedVectors ρ hρ KP hKP _⟩
    exact ⟨t, ht.trans (map_averageMap_of_forall_eq ρ hρ KP hKP (mk ρ N) _ _ hconst)⟩

/-- The exact published product opposite stable-image bijectivity clause. -/
theorem refinedOppositeStableImageJacquetBijective
    (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    RefinedOppositeStableImageJacquetBijectiveClause F T B S V := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro ρ hAdmissible
  dsimp only
  intro K hK hfac a ha
  exact refinedOppositeStableImage_bijective_of_finiteDimensional F T B S V ρ hAdmissible.1
    K hK (hAdmissible.2 (CuspidalSupport.leviPiOpenSubgroup T B K)) hfac a ha

end Langlands.Jacquet
