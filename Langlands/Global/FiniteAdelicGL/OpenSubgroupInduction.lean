import Langlands.Global.FiniteAdelicGL.RestrictedProduct
import Langlands.Representation.Smooth.Definitions

/-!
# Open subgroups of the finite adelic general linear group and local factors

For a number field `K`, every open subgroup `L` of `GL_n(𝔸_K,f)` contains the matrices that
are integral at every finite place and equal to the identity at the places of a finite set
`T` (`exists_finset_forall_mem`). Consequences:

* `induction_localInclusion`: a property of finite adelic matrices that holds on an open
  subgroup and is preserved by left multiplication with the image of a local matrix holds for
  every finite adelic matrix (a finite adelic matrix is a finite product of local matrices
  times an element of the open subgroup);
* `eventually_fixed_localIntegral`: a vector of a smooth representation of `GL_n(𝔸_K,f)` is
  fixed by the local integral subgroup `GL_n(𝒪_v)` at almost every finite place `v`.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Global.FiniteAdelicGL

open scoped RestrictedProduct

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}

/-- The finite adelic matrix whose local components are given local integral matrices. -/
def ofIntegral (y : ∀ v : FinitePlace K, localIntegral K n v) : FiniteAdelicGL K n :=
  fromRestrictedProduct K n
    (RestrictedProduct.structureMap (FiniteLocalGL K n)
      (fun v => (localIntegral K n v : Set (FiniteLocalGL K n v))) Filter.cofinite y)

theorem localProjection_ofIntegral (y : ∀ v : FinitePlace K, localIntegral K n v)
    (v : FinitePlace K) : localProjection K n v (ofIntegral y) = y v :=
  localProjection_fromRestrictedProduct K n _ v

theorem continuous_ofIntegral :
    Continuous (ofIntegral : (∀ v : FinitePlace K, localIntegral K n v) →
      FiniteAdelicGL K n) :=
  (continuous_fromRestrictedProduct K n).comp
    (RestrictedProduct.isEmbedding_structureMap (R := FiniteLocalGL K n)
      (A := fun v => (localIntegral K n v : Set (FiniteLocalGL K n v)))
      (𝓕 := Filter.cofinite)).continuous

/-- **Open subgroups contain the integral matrices trivial at finitely many places.** For
every open subgroup `L` of `GL_n(𝔸_K,f)` there is a finite set `T` of finite places such that
`L` contains every finite adelic matrix that is integral (with integral inverse) at every
place and is the identity at the places of `T`. -/
theorem exists_finset_forall_mem (L : OpenSubgroup (FiniteAdelicGL K n)) :
    ∃ T : Finset (FinitePlace K), ∀ ℓ : FiniteAdelicGL K n,
      (∀ v ∈ T, localProjection K n v ℓ = 1) →
      (∀ v, localProjection K n v ℓ ∈ localIntegral K n v) → ℓ ∈ L := by
  have hopen : IsOpen (ofIntegral ⁻¹' (L : Set (FiniteAdelicGL K n)) :
      Set (∀ v : FinitePlace K, localIntegral K n v)) :=
    L.isOpen.preimage continuous_ofIntegral
  have hone : ofIntegral (1 : ∀ v : FinitePlace K, localIntegral K n v) = 1 :=
    ext_localProjection K n fun v => by
      rw [localProjection_ofIntegral, map_one]
      rfl
  have h1 : (1 : ∀ v : FinitePlace K, localIntegral K n v) ∈
      ofIntegral ⁻¹' (L : Set (FiniteAdelicGL K n)) := by
    rw [Set.mem_preimage, hone]
    exact L.one_mem
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hopen 1 h1
  refine ⟨I, fun ℓ hℓ hint => ?_⟩
  let y : ∀ v : FinitePlace K, localIntegral K n v := fun v =>
    ⟨localProjection K n v ℓ, hint v⟩
  have hy : y ∈ (I : Set (FinitePlace K)).pi u := by
    refine Set.mem_pi.mpr fun v hv => ?_
    have hv1 : y v = 1 := Subtype.ext (hℓ v hv)
    rw [hv1]
    exact (hu v hv).2
  have hmem := hsub hy
  have heq : ofIntegral y = ℓ :=
    ext_localProjection K n fun v => localProjection_ofIntegral y v
  rw [Set.mem_preimage, heq] at hmem
  exact hmem

/-- Removing the local component at `v`: the projections of `(ι_v g)⁻¹ d` are `g⁻¹ d_v` at `v`
and `d_w` at `w ≠ v`. -/
theorem localProjection_inv_localInclusion_mul_of_ne (v w : FinitePlace K) (h : w ≠ v)
    (g : FiniteLocalGL K n v) (d : FiniteAdelicGL K n) :
    localProjection K n w ((localInclusion K n v g)⁻¹ * d) = localProjection K n w d := by
  rw [map_mul, map_inv, localProjection_localInclusion_of_ne K n v w h, inv_one, one_mul]

theorem localProjection_inv_localInclusion_mul_self (v : FinitePlace K)
    (d : FiniteAdelicGL K n) :
    localProjection K n v ((localInclusion K n v (localProjection K n v d))⁻¹ * d) = 1 := by
  rw [map_mul, map_inv, localProjection_localInclusion, inv_mul_cancel]

/-- **Induction over local factors.** A property of finite adelic matrices that holds on an
open subgroup and is preserved by left multiplication with local matrices `ι_v(g)` holds for
every finite adelic matrix. -/
theorem induction_localInclusion (P : FiniteAdelicGL K n → Prop)
    (L : OpenSubgroup (FiniteAdelicGL K n)) (hL : ∀ ℓ ∈ L, P ℓ)
    (hstep : ∀ (v : FinitePlace K) (g : FiniteLocalGL K n v) (d : FiniteAdelicGL K n),
      P d → P (localInclusion K n v g * d)) (d : FiniteAdelicGL K n) : P d := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_forall_mem L
  have key : ∀ S : Finset (FinitePlace K), ∀ d : FiniteAdelicGL K n,
      (∀ v ∉ S, (v ∈ T → localProjection K n v d = 1) ∧
        localProjection K n v d ∈ localIntegral K n v) → P d := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro d hd
      exact hL d (hT d (fun v hv => (hd v (Finset.notMem_empty v)).1 hv)
        (fun v => (hd v (Finset.notMem_empty v)).2))
    | insert w S hw ih =>
      intro d hd
      have hd' : localInclusion K n w (localProjection K n w d) *
          ((localInclusion K n w (localProjection K n w d))⁻¹ * d) = d :=
        mul_inv_cancel_left _ _
      rw [← hd']
      refine hstep w _ _ (ih _ fun v hv => ?_)
      rcases eq_or_ne v w with rfl | hvw
      · rw [localProjection_inv_localInclusion_mul_self]
        exact ⟨fun _ => rfl, (localIntegral K n v).one_mem⟩
      · rw [localProjection_inv_localInclusion_mul_of_ne w v hvw]
        exact hd v (by simp [hvw, hv])
  have hfin := Filter.eventually_cofinite.mp (eventually_localIntegral K n d)
  refine key (T ∪ hfin.toFinset) d fun v hv => ?_
  simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
    not_not] at hv
  exact ⟨fun h => absurd h hv.1, hv.2⟩

/-- **Smooth vectors are fixed by `GL_n(𝒪_v)` at almost every place.** A vector of a smooth
representation of `GL_n(𝔸_K,f)` is fixed by the image of the local integral subgroup at all
but finitely many finite places. -/
theorem eventually_fixed_localIntegral {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (FiniteAdelicGL K n) V} (hρ : Langlands.IsSmooth ρ) (x : V) :
    ∀ᶠ v in Filter.cofinite, ∀ g ∈ localIntegral K n v,
      ρ (localInclusion K n v g) x = x := by
  obtain ⟨L, hL⟩ := hρ x
  obtain ⟨T, hT⟩ := exists_finset_forall_mem L
  refine Filter.eventually_cofinite.mpr (T.finite_toSet.subset fun v hv => ?_)
  by_contra hvT
  apply hv
  intro g hg
  have hmem : localInclusion K n v g ∈ L := by
    refine hT _ (fun w hw => ?_) (fun w => ?_)
    · exact localProjection_localInclusion_of_ne K n v w (fun h => hvT (h ▸ hw)) g
    · rcases eq_or_ne w v with rfl | hw
      · rw [localProjection_localInclusion]
        exact hg
      · rw [localProjection_localInclusion_of_ne K n v w hw]
        exact (localIntegral K n w).one_mem
  exact hL ⟨_, hmem⟩

end Langlands.Global.FiniteAdelicGL
