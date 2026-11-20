import Langlands.Representation.Smooth.Factorization.RestrictedTensorStatement
import Langlands.Representation.RestrictedTensor.Irreducibility
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.RestrictedTensor.LocalSeparation

/-!
# Admissibility of restricted tensor representations

Proof of `RestrictedTensorAdmissibilityStatement` (Flath 1979, §2, Example 2).

* `RestrictedTensor.exists_finset_forall_mem`: an open subgroup `K` of the restricted product
  contains every element of `∏ H i` that is `1` on some finite set `T`;
  `RestrictedTensor.mem_of_localInsertion_mem`: it then contains every element `g` of `∏ H i`
  whose coordinates `g i`, `i ∈ T`, satisfy `localInsertion H i (g i) ∈ K`.
* `RestrictedTensor.localOpenSubgroup`: these coordinates form an open subgroup of `G i`.
* `RestrictedTensor.fixedVectors_le_range`: the vectors fixed by `K` lie in the image of the
  tensor product, over a fixed finite stage, of the vectors fixed by open subgroups of the
  local groups.
* `restrictedTensorAdmissibility`: the statement.
-/

noncomputable section

open scoped Classical

universe uI uG uV

namespace Langlands.RestrictedTensor

variable {ι : Type uI} {G : ι → Type uG} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]

/-- **Open subgroups contain the elements trivial on a finite set.** -/
theorem exists_finset_forall_mem (H : ∀ i, Subgroup (G i))
    (K : OpenSubgroup (RestrictedGroup G H)) :
    ∃ T : Finset ι, ∀ g : RestrictedGroup G H, (∀ i, g i ∈ H i) → (∀ i ∈ T, g i = 1) →
      g ∈ K := by
  let φ : (∀ i, H i) → RestrictedGroup G H :=
    RestrictedProduct.structureMap G (fun i => (H i : Set (G i))) Filter.cofinite
  have hφ : Continuous φ :=
    (RestrictedProduct.isEmbedding_structureMap (R := G) (A := fun i => (H i : Set (G i)))
      (𝓕 := Filter.cofinite)).continuous
  have hopen : IsOpen (φ ⁻¹' (K : Set (RestrictedGroup G H))) := K.isOpen.preimage hφ
  have hone : φ 1 = 1 := by
    ext i
    rfl
  have h1 : (1 : ∀ i, H i) ∈ φ ⁻¹' (K : Set (RestrictedGroup G H)) := by
    rw [Set.mem_preimage, hone]
    exact K.one_mem
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hopen 1 h1
  refine ⟨I, fun g hg hT => ?_⟩
  let y : ∀ i, H i := fun i => ⟨g i, hg i⟩
  have hy : y ∈ (I : Set ι).pi u := by
    refine Set.mem_pi.mpr fun i hi => ?_
    have hyi : y i = 1 := Subtype.ext (hT i hi)
    rw [hyi]
    exact (hu i hi).2
  have hmem := hsub hy
  have heq : φ y = g := by
    ext i
    rfl
  rw [Set.mem_preimage, heq] at hmem
  exact hmem

omit [∀ i, TopologicalSpace (G i)] in
/-- Removing one coordinate: the coordinates of `(localInsertion H w x)⁻¹ * g`. -/
theorem inv_localInsertion_mul_apply (H : ∀ i, Subgroup (G i)) (w : ι)
    (g : RestrictedGroup G H) (i : ι) :
    ((localInsertion H w (g w))⁻¹ * g) i = if i = w then 1 else g i := by
  rw [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply]
  by_cases h : i = w
  · subst h
    rw [localInsertion_same, inv_mul_cancel]
    simp
  · rw [localInsertion_of_ne H w _ h, inv_one, one_mul]
    simp [h]

/-- **Products of local factors.** If `K` contains the elements of `∏ H i` trivial on `T`, it
contains every element `g` of `∏ H i` with `localInsertion H i (g i) ∈ K` for `i ∈ T`. -/
theorem mem_of_localInsertion_mem (H : ∀ i, Subgroup (G i))
    (K : OpenSubgroup (RestrictedGroup G H)) (T : Finset ι)
    (hT : ∀ g : RestrictedGroup G H, (∀ i, g i ∈ H i) → (∀ i ∈ T, g i = 1) → g ∈ K)
    (g : RestrictedGroup G H) (hg : ∀ i, g i ∈ H i)
    (hgT : ∀ i ∈ T, localInsertion H i (g i) ∈ K) : g ∈ K := by
  have key : ∀ S : Finset ι, ∀ g : RestrictedGroup G H, (∀ i, g i ∈ H i) →
      (∀ i ∈ S, localInsertion H i (g i) ∈ K) → (∀ i ∈ T, i ∉ S → g i = 1) → g ∈ K := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun g hg _ h1 => hT g hg fun i hi => h1 i hi (Finset.notMem_empty i)
    | insert w S hw ih =>
      intro g hg hgS h1
      have hdec : g = localInsertion H w (g w) * ((localInsertion H w (g w))⁻¹ * g) :=
        (mul_inv_cancel_left _ _).symm
      rw [hdec]
      refine K.mul_mem (hgS w (Finset.mem_insert_self w S)) (ih _ (fun i => ?_) (fun i hi => ?_)
        (fun i hiT hiS => ?_))
      · rw [inv_localInsertion_mul_apply]
        split_ifs
        · exact (H i).one_mem
        · exact hg i
      · have hiw : i ≠ w := fun h => hw (h ▸ hi)
        have := hgS i (Finset.mem_insert_of_mem hi)
        rw [inv_localInsertion_mul_apply]
        simpa [hiw] using this
      · rw [inv_localInsertion_mul_apply]
        split_ifs with h
        · rfl
        · exact h1 i hiT (fun hm => (Finset.mem_insert.mp hm).elim h hiS)
  exact key T g hg hgT (fun i hi hni => absurd hi hni)

variable [∀ i, IsTopologicalGroup (G i)]

/-- The coordinates in `H i` whose insertion lies in `K`, an open subgroup of `G i` when
`H i` is open. -/
def localOpenSubgroup (H : ∀ i, Subgroup (G i)) (hH : ∀ i, IsOpen (H i : Set (G i)))
    (K : OpenSubgroup (RestrictedGroup G H)) (i : ι) : OpenSubgroup (G i) where
  toSubgroup := K.toSubgroup.comap (localInsertion H i) ⊓ H i
  isOpen' := by
    let φ : (∀ j, H j) → RestrictedGroup G H :=
      RestrictedProduct.structureMap G (fun j => (H j : Set (G j))) Filter.cofinite
    have hφ : Continuous φ :=
      (RestrictedProduct.isEmbedding_structureMap (R := G) (A := fun j => (H j : Set (G j)))
        (𝓕 := Filter.cofinite)).continuous
    let ψ : H i → RestrictedGroup G H := fun x => φ (Pi.mulSingle i x)
    have hψ : Continuous ψ := hφ.comp (continuous_mulSingle (A := fun j => H j) i)
    have hψeq : ∀ x : H i, ψ x = localInsertion H i x := by
      intro x
      ext j
      by_cases h : j = i
      · subst h
        rw [localInsertion_same]
        show ((Pi.mulSingle j x : ∀ k, H k) j : G j) = x
        rw [Pi.mulSingle_eq_same]
      · rw [localInsertion_of_ne H i _ h]
        show ((Pi.mulSingle i x : ∀ k, H k) j : G j) = 1
        rw [Pi.mulSingle_eq_of_ne h]
        rfl
    have hopen : IsOpen (ψ ⁻¹' (K : Set (RestrictedGroup G H))) := K.isOpen.preimage hψ
    have hset : ((K.toSubgroup.comap (localInsertion H i) ⊓ H i : Subgroup (G i)) :
        Set (G i)) = Subtype.val '' (ψ ⁻¹' (K : Set (RestrictedGroup G H))) := by
      ext x
      constructor
      · rintro ⟨hxK, hxH⟩
        refine ⟨⟨x, hxH⟩, ?_, rfl⟩
        rw [Set.mem_preimage, hψeq]
        exact hxK
      · rintro ⟨y, hy, rfl⟩
        rw [Set.mem_preimage, hψeq] at hy
        exact ⟨hy, y.2⟩
    change IsOpen ((K.toSubgroup.comap (localInsertion H i) ⊓ H i : Subgroup (G i)) :
      Set (G i))
    rw [hset]
    exact (hH i).isOpenMap_subtype_val _ hopen

section FixedVectors

variable {k : Type*} [Field k] {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

omit [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] in
/-- **Fixed vectors lie in a fixed finite stage.** Let `L i ≤ H i` be subgroups and `S0` a
finite stage outside which every `L i`-fixed vector is a multiple of the reference vector. Then
every vector of the restricted tensor product fixed by all `g` with `g i ∈ L i` is the image
of a tensor, over `S0`, of `L i`-fixed vectors. -/
theorem fixedVectors_le_range (H : ∀ i, Subgroup (G i))
    (ρ : ∀ i, Representation k (G i) (V i)) (E : Finset ι) (e : ∀ i, V i)
    (he : ∀ i ∉ E, ∀ g ∈ H i, ρ i g (e i) = e i) (hne : ∀ i ∉ E, e i ≠ 0)
    (L : ∀ i, Subgroup (G i)) (S0 : Index E)
    (hline : ∀ i ∉ S0.1, ∀ x : V i, (∀ g : L i, ρ i g x = x) → ∃ c : k, x = c • e i)
    (x : Space k V E e)
    (hx : ∀ g : RestrictedGroup G H, (∀ i, g i ∈ L i) → representation H ρ E e he g x = x) :
    x ∈ LinearMap.range ((of k V E e S0) ∘ₗ
      PiTensorProduct.map (fun i : S0.1 => (fixedVectors (ρ i) (L i)).subtype)) := by
  obtain ⟨S1, t1, rfl⟩ := exists_of E e x
  let S : Index E := ⟨S0.1 ∪ S1.1, S0.2.trans Finset.subset_union_left⟩
  have h0 : S0 ≤ S := Finset.subset_union_left
  have h1 : S1 ≤ S := Finset.subset_union_right
  rw [← of_transition E e h1]
  set t := transition e h1 t1 with ht_def
  -- `t` is fixed by the finite product of the `L i`
  have hfix : t ∈ fixedVectors (FiniteTensor.external (fun i : S.1 => ρ i))
      (Subgroup.pi Set.univ (fun i : S.1 => L i)) := by
    intro g
    apply of_injective E e hne S
    change of k V E e S (FiniteTensor.external (fun i : S.1 => ρ i) (g : ∀ i : S.1, G i) t) =
      of k V E e S t
    rw [of_external H ρ E e he, of_transition]
    refine (congrArg _ (of_transition E e h1 t1).symm).trans ?_
    rw [of_transition]
    refine hx _ fun i => ?_
    change (if h : i ∈ S.1 then (g : ∀ i : S.1, G i) ⟨i, h⟩ else 1) ∈ L i
    split_ifs with h
    · exact g.2 ⟨i, h⟩ (Set.mem_univ _)
    · exact (L i).one_mem
  obtain ⟨u, hu⟩ := FiniteTensor.fixedVectors_external_le (fun i : S.1 => ρ i)
    (fun i : S.1 => L i) hfix
  rw [← hu]
  clear hu hfix ht_def
  induction u using PiTensorProduct.induction_on with
  | smul_tprod a w =>
    rw [map_smul, map_smul]
    refine Submodule.smul_mem _ a ?_
    rw [PiTensorProduct.map_tprod]
    -- coordinates outside `S0` are multiples of the references
    have hc : ∀ i : S.1, ∃ c : k, i.1 ∉ S0.1 → ((w i : V i) = c • e i) := by
      intro i
      by_cases hi : i.1 ∈ S0.1
      · exact ⟨1, fun h => absurd hi h⟩
      · obtain ⟨c, hc⟩ := hline i.1 hi (w i) fun g => (w i).2 g
        exact ⟨c, fun _ => hc⟩
    choose c hc using hc
    let c' : S.1 → k := fun i => if i.1 ∈ S0.1 then 1 else c i
    let v0 : ∀ i : S0.1, V i := fun i => (w ⟨i.1, h0 i.2⟩ : V i)
    have hw : (fun i : S.1 => ((fixedVectors (ρ i) (L i)).subtype (w i) : V i)) =
        fun i => c' i • extend e v0 i := by
      funext i
      by_cases hi : i.1 ∈ S0.1
      · simp only [c', extend, hi, ite_true, dite_true, one_smul, v0]
        rfl
      · simp only [c', extend, hi, ite_false, dite_false]
        exact hc i hi
    rw [hw, MultilinearMap.map_smul_univ, map_smul]
    refine Submodule.smul_mem _ _ ?_
    change pure E e S (extend e v0) ∈ _
    rw [pure_extend E e h0 v0]
    refine ⟨PiTensorProduct.tprod k (fun i : S0.1 => w ⟨i.1, h0 i.2⟩), ?_⟩
    rw [LinearMap.comp_apply, PiTensorProduct.map_tprod]
    rfl
  | add a b ha hb =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ ha hb

end FixedVectors

end Langlands.RestrictedTensor

namespace Langlands

open RestrictedTensor

/-- **Admissibility of restricted tensor representations** (Flath 1979, §2, Example 2):
admissible local representations whose fixed spaces under the open compact subgroups `H i`
are lines at almost every index give an admissible restricted tensor representation. -/
theorem restrictedTensorAdmissibility :
    RestrictedTensorAdmissibilityStatement.{uI, uG, uV} := by
  intro ι G _ _ _ _ _ _ H V _ _ ρ E r hr hHoc hadm hfin
  have hHo : ∀ i, IsOpen (H i : Set (G i)) := fun i => (hHoc i).1
  refine ⟨isSmooth_productRepresentation H hHo ρ (fun i => (hadm i).1) E r hr, fun K => ?_⟩
  obtain ⟨T, hT⟩ := exists_finset_forall_mem H K
  let L : ∀ i, OpenSubgroup (G i) := fun i =>
    if i ∈ T then localOpenSubgroup H hHo K i else ⟨H i, hHo i⟩
  have hLH : ∀ i, (L i : Subgroup (G i)) ≤ H i := by
    intro i
    by_cases hi : i ∈ T
    · simp only [L, hi, ite_true]
      exact inf_le_right
    · simp only [L, hi, ite_false]
      exact le_rfl
  have hLK : ∀ g : RestrictedGroup G H, (∀ i, g i ∈ (L i : Subgroup (G i))) → g ∈ K := by
    intro g hg
    refine mem_of_localInsertion_mem H K T hT g (fun i => hLH i (hg i)) fun i hi => ?_
    have h := hg i
    simp only [L, hi, ite_true] at h
    exact h.1
  let S0 : Index E := ⟨E ∪ T ∪ (Filter.eventually_cofinite.mp hfin).toFinset,
    Finset.subset_union_left.trans Finset.subset_union_left⟩
  have hline : ∀ i ∉ S0.1, ∀ x : V i, (∀ g : (L i : Subgroup (G i)), ρ i g x = x) →
      ∃ c : ℂ, x = c • r.family i := by
    intro i hi x hx
    simp only [S0, Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
      not_not] at hi
    obtain ⟨⟨hiE, hiT⟩, h1⟩ := hi
    have hLi : (L i : Subgroup (G i)) = H i := by simp only [L, hiT, ite_false]
    rw [ReferenceVectors.family_of_not_mem r hiE]
    have hmem : r.vector i hiE ∈ fixedVectors (ρ i) (H i) := fun g => hr i hiE g g.2
    have hxmem : x ∈ fixedVectors (ρ i) (H i) := fun g => hx ⟨g, hLi.symm ▸ g.2⟩
    have hne : (⟨r.vector i hiE, hmem⟩ : fixedVectors (ρ i) (H i)) ≠ 0 := fun h0 =>
      r.nonzero i hiE (congrArg Subtype.val h0)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp h1 ⟨x, hxmem⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  have hle : fixedVectors (productRepresentation H ρ E r hr) K.toSubgroup ≤
      LinearMap.range ((of ℂ V E r.family S0) ∘ₗ
        PiTensorProduct.map (fun i : S0.1 =>
          (fixedVectors (ρ i) (L i : Subgroup (G i))).subtype)) := by
    intro x hx
    exact fixedVectors_le_range H ρ E r.family
      (fun i hi g hg => by
        simpa only [ReferenceVectors.family_of_not_mem r hi] using hr i hi g hg)
      r.family_nonzero
      (fun i => (L i : Subgroup (G i))) S0 hline x fun g hg => hx ⟨g, hLK g hg⟩
  have : ∀ i : S0.1, Module.Finite ℂ (fixedVectors (ρ i) (L i : Subgroup (G i))) :=
    fun i => (hadm i).2 (L i)
  exact Submodule.finiteDimensional_of_le hle

end Langlands
