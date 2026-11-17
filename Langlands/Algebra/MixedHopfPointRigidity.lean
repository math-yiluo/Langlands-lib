import Langlands.Algebra.MixedLatticeConfigurationBound
import Langlands.Algebra.HopfPointKernel

/-! # Hopf points of `ℤ^r × F` with bounded generator supports are determined modulo `m` -/

noncomputable section

open TensorProduct

namespace Langlands.Algebra.MixedHopfPointRigidity

open HopfPointExtension HopfPointClosedLocus LatticeConfiguration MixedLatticeConfiguration

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Bialgebra R A]
  {C : Type*} [CommRing C] [Algebra R C] {r : Type*} [Fintype r] [DecidableEq r]
  {F : Type*} [AddCommGroup F] [Fintype F] {σ : Type*}

/-- Reduction modulo `m` is injective on the box of radius `n` of `ℤ^r × F` when
`2n < m`. -/
theorem injOn_mred_mbox {n m : ℕ} (hm : 2 * n < m) :
    Set.InjOn (mred r F m) (mbox r F n : Set ((r → ℤ) × F)) := by
  intro x hx y hy h
  have hx1 : x.1 ∈ (box r n : Set (r → ℤ)) := mem_box.mpr (mem_mbox.mp hx)
  have hy1 : y.1 ∈ (box r n : Set (r → ℤ)) := mem_box.mpr (mem_mbox.mp hy)
  have h2 : (mred r F m x).2 = (mred r F m y).2 := congrArg Prod.snd h
  exact Prod.ext (HopfPointRigidity.injOn_red_box hm hx1 hy1 (congrArg Prod.fst h)) h2

omit [Fintype r] [DecidableEq r] [Fintype F] in
/-- If the values on generators span `C[M]` as a `C`-algebra over a nonzero ring,
their supports generate `M`. -/
theorem closure_support_eq_top [Nontrivial C] {M : Type*} [AddCommGroup M] {gen : σ → A}
    (hgen : Algebra.adjoin R (Set.range gen) = ⊤)
    {α : A →ₐ[R] AddMonoidAlgebra C M}
    (hα : Algebra.adjoin C (Set.range α) = ⊤) :
    AddSubgroup.closure (⋃ i, (↑(α (gen i)).coeff.support : Set M)) = ⊤ := by
  classical
  set T := AddSubmonoid.closure (⋃ i, (↑(α (gen i)).coeff.support : Set M))
  have key : ∀ x ∈ Algebra.adjoin C (Set.range (α ∘ gen)),
      (x.coeff.support : Set M) ⊆ (T : Set M) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact fun z hz => AddSubmonoid.subset_closure (Set.mem_iUnion.mpr ⟨i, hz⟩)
    | algebraMap c =>
      intro z hz
      rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply,
        AddMonoidAlgebra.coeff_single] at hz
      rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hz)]
      exact T.zero_mem
    | add x y _ _ hx hy =>
      intro z hz
      rw [AddMonoidAlgebra.coeff_add] at hz
      rcases Finset.mem_union.mp (Finsupp.support_add hz) with h | h
      exacts [hx h, hy h]
    | mul x y _ _ hx hy =>
      refine (support_mul_subset hx hy).trans ?_
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact T.add_mem ha hb
  have hrange : Algebra.adjoin C (Set.range α) ≤ Algebra.adjoin C (Set.range (α ∘ gen)) := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨a, rfl⟩
    have ha : a ∈ Algebra.adjoin R (Set.range gen) := hgen ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Algebra.subset_adjoin ⟨i, rfl⟩
    | algebraMap c =>
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R C (AddMonoidAlgebra C M)]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  rw [eq_top_iff]
  intro χ _
  have hmem : AddMonoidAlgebra.single χ (1 : C) ∈ Algebra.adjoin C (Set.range (α ∘ gen)) :=
    hrange (hα ▸ Algebra.mem_top)
  have hχ : χ ∈ ((AddMonoidAlgebra.single χ (1 : C)).coeff.support : Set M) := by
    simp [AddMonoidAlgebra.coeff_single]
  have hT : χ ∈ T := key _ hmem hχ
  exact (AddSubmonoid.closure_le.mpr fun z hz => AddSubgroup.subset_closure hz) hT

/-- A modulus beyond which bounded configurations of `ℤ^r × F` are rigid. -/
def rigidityBound (r : Type*) [Fintype r] [DecidableEq r] (F : Type*) [AddCommGroup F]
    [Fintype F] (n : ℕ) : ℕ :=
  max (Classical.choose (exists_bound r F n)) (2 * n + 1)

/-- Coefficient transport: the reduction of `x'` is the twist of the reduction of `x`. -/
theorem exists_mem_support_of_mred {m n : ℕ} (hm : 2 * n < m)
    (γ : (r → ZMod m) × F ≃+ (r → ZMod m) × F)
    {x x' : AddMonoidAlgebra C ((r → ℤ) × F)}
    (hx : ↑x.coeff.support ⊆ (mbox r F n : Set ((r → ℤ) × F)))
    (h : AddMonoidAlgebra.mapDomainAlgHom R C (mred r F m) x' =
      AddMonoidAlgebra.mapDomainAlgHom R C γ.toAddMonoidHom
        (AddMonoidAlgebra.mapDomainAlgHom R C (mred r F m) x))
    {χ : (r → ℤ) × F} (hχ : χ ∈ x.coeff.support) :
    ∃ χ' ∈ x'.coeff.support, mred r F m χ' = γ (mred r F m χ) := by
  classical
  have hinj := injOn_mred_mbox (r := r) (F := F) hm
  have hcoeff : (AddMonoidAlgebra.mapDomainAlgHom R C (mred r F m) x').coeff
      (γ (mred r F m χ)) = x.coeff χ := by
    rw [h, coeff_mapDomainAlgHom, coeff_mapDomainAlgHom]
    rw [show (γ.toAddMonoidHom : (r → ZMod m) × F → (r → ZMod m) × F) = γ from rfl,
      Finsupp.mapDomain_apply_of_injective γ.injective
        (Finsupp.mapDomain (mred r F m) x.coeff) (mred r F m χ)]
    exact Finsupp.mapDomain_apply' _ x.coeff hx hinj (hx hχ)
  have hne : (AddMonoidAlgebra.mapDomainAlgHom R C (mred r F m) x').coeff
      (γ (mred r F m χ)) ≠ 0 := by
    rw [hcoeff]; exact Finsupp.mem_support_iff.mp hχ
  rw [coeff_mapDomainAlgHom] at hne
  obtain ⟨χ', hχ', he⟩ :=
    Finset.mem_image.mp (Finsupp.mapDomain_support (Finsupp.mem_support_iff.mpr hne))
  exact ⟨χ', hχ', he⟩

/-- Rigidity of bounded Hopf points of `ℤ^r × F`: two Hopf points into `C[ℤ^r × F]`
with generator values supported in the box of radius `n`, whose supports generate
`ℤ^r × F`, and whose reductions modulo `m ≥ rigidityBound r F n` differ by an
automorphism of `(ℤ/m)^r × F`, differ by an automorphism of `ℤ^r × F`. -/
theorem exists_addEquiv_of_mred_eq {n m : ℕ} (hm : rigidityBound r F n ≤ m)
    {gen : σ → A} (hgen : Algebra.adjoin R (Set.range gen) = ⊤)
    {α α' : A →ₐ[R] AddMonoidAlgebra C ((r → ℤ) × F)}
    (hα : ∀ i, ↑(α (gen i)).coeff.support ⊆ (mbox r F n : Set ((r → ℤ) × F)))
    (hα' : ∀ i, ↑(α' (gen i)).coeff.support ⊆ (mbox r F n : Set ((r → ℤ) × F)))
    (hgα : AddSubgroup.closure
      (⋃ i, (↑(α (gen i)).coeff.support : Set ((r → ℤ) × F))) = ⊤)
    (hgα' : AddSubgroup.closure
      (⋃ i, (↑(α' (gen i)).coeff.support : Set ((r → ℤ) × F))) = ⊤)
    (γ : (r → ZMod m) × F ≃+ (r → ZMod m) × F)
    (h : (AddMonoidAlgebra.mapDomainAlgHom R C (mred r F m)).comp α' =
      (AddMonoidAlgebra.mapDomainAlgHom R C γ.toAddMonoidHom).comp
        ((AddMonoidAlgebra.mapDomainAlgHom R C (mred r F m)).comp α)) :
    ∃ T : (r → ℤ) × F ≃+ (r → ℤ) × F,
      (AddMonoidAlgebra.mapDomainAlgHom R C T.toAddMonoidHom).comp α = α' := by
  classical
  have hm₀ : Classical.choose (exists_bound r F n) ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : 2 * n < m := lt_of_lt_of_le (by omega) (le_trans (le_max_right _ _) hm)
  have hinj := injOn_mred_mbox (r := r) (F := F) hm2
  have hbound := Classical.choose_spec (exists_bound r F n) m hm₀
  -- the two support configurations
  let U : Set ((r → ℤ) × F) := ⋃ i, (↑(α (gen i)).coeff.support : Set ((r → ℤ) × F))
  let U' : Set ((r → ℤ) × F) := ⋃ i, (↑(α' (gen i)).coeff.support : Set ((r → ℤ) × F))
  let S : Finset ((r → ℤ) × F) := (mbox r F n).filter (· ∈ U)
  let S' : Finset ((r → ℤ) × F) := (mbox r F n).filter (· ∈ U')
  have hUS : (S : Set ((r → ℤ) × F)) = U := by
    ext χ
    simp only [S, Finset.coe_filter, Set.mem_ofPred_eq]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    exact hα i hi
  have hUS' : (S' : Set ((r → ℤ) × F)) = U' := by
    ext χ
    simp only [S', Finset.coe_filter, Set.mem_ofPred_eq]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    exact hα' i hi
  have hcoeffs : ∀ i, AddMonoidAlgebra.mapDomainAlgHom R C (mred r F m) (α' (gen i)) =
      AddMonoidAlgebra.mapDomainAlgHom R C γ.toAddMonoidHom
        (AddMonoidAlgebra.mapDomainAlgHom R C (mred r F m) (α (gen i))) :=
    fun i => congrArg (fun F => F (gen i)) h
  have hcoeffs' : ∀ i, AddMonoidAlgebra.mapDomainAlgHom R C (mred r F m) (α (gen i)) =
      AddMonoidAlgebra.mapDomainAlgHom R C γ.symm.toAddMonoidHom
        (AddMonoidAlgebra.mapDomainAlgHom R C (mred r F m) (α' (gen i))) := by
    intro i
    rw [hcoeffs i]
    set y := AddMonoidAlgebra.mapDomainAlgHom R C (mred r F m) (α (gen i))
    rw [← AlgHom.comp_apply (AddMonoidAlgebra.mapDomainAlgHom R C γ.symm.toAddMonoidHom)
      (AddMonoidAlgebra.mapDomainAlgHom R C γ.toAddMonoidHom) y,
      ← AddMonoidAlgebra.mapDomainAlgHom_comp]
    have : γ.symm.toAddMonoidHom.comp γ.toAddMonoidHom = AddMonoidHom.id _ := by
      ext x <;> simp
    rw [this, AddMonoidAlgebra.mapDomainAlgHom_id, AlgHom.id_apply]
  -- the correspondence of supports
  let φ : (r → ℤ) × F → (r → ℤ) × F :=
    fun χ => Function.invFunOn (mred r F m) (mbox r F n) (γ (mred r F m χ))
  let φ' : (r → ℤ) × F → (r → ℤ) × F :=
    fun χ => Function.invFunOn (mred r F m) (mbox r F n) (γ.symm (mred r F m χ))
  have hφ : ∀ χ ∈ S, φ χ ∈ mbox r F n ∧ mred r F m (φ χ) = γ (mred r F m χ) ∧
      φ χ ∈ U' := by
    intro χ hχ
    have hχU : χ ∈ U := by rw [← hUS]; exact hχ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hχU
    obtain ⟨χ', hχ', he⟩ :=
      exists_mem_support_of_mred (R := R) hm2 γ (hα i) (hcoeffs i) hi
    have hχ'box : χ' ∈ (mbox r F n : Set ((r → ℤ) × F)) := hα' i hχ'
    have hex : ∃ a ∈ (mbox r F n : Set ((r → ℤ) × F)), mred r F m a = γ (mred r F m χ) :=
      ⟨χ', hχ'box, he⟩
    have hmem := Function.invFunOn_mem hex
    have heq := Function.invFunOn_eq hex
    have : φ χ = χ' := hinj hmem hχ'box (heq.trans he.symm)
    exact ⟨hmem, heq, this ▸ Set.mem_iUnion.mpr ⟨i, hχ'⟩⟩
  have hφ' : ∀ χ ∈ S', φ' χ ∈ mbox r F n ∧ mred r F m (φ' χ) = γ.symm (mred r F m χ) ∧
      φ' χ ∈ U := by
    intro χ hχ
    have hχU : χ ∈ U' := by rw [← hUS']; exact hχ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hχU
    obtain ⟨χ', hχ', he⟩ :=
      exists_mem_support_of_mred (R := R) hm2 γ.symm (hα' i) (hcoeffs' i) hi
    have hχ'box : χ' ∈ (mbox r F n : Set ((r → ℤ) × F)) := hα i hχ'
    have hex : ∃ a ∈ (mbox r F n : Set ((r → ℤ) × F)),
        mred r F m a = γ.symm (mred r F m χ) :=
      ⟨χ', hχ'box, he⟩
    have hmem := Function.invFunOn_mem hex
    have heq := Function.invFunOn_eq hex
    have : φ' χ = χ' := hinj hmem hχ'box (heq.trans he.symm)
    exact ⟨hmem, heq, this ▸ Set.mem_iUnion.mpr ⟨i, hχ'⟩⟩
  have hSbox : ∀ χ ∈ S, χ ∈ mbox r F n := fun χ hχ => (Finset.mem_filter.mp hχ).1
  have hS'box : ∀ χ ∈ S', χ ∈ mbox r F n := fun χ hχ => (Finset.mem_filter.mp hχ).1
  have hSgen : AddSubgroup.closure (S : Set ((r → ℤ) × F)) = ⊤ := by rw [hUS]; exact hgα
  have hS'gen : AddSubgroup.closure (S' : Set ((r → ℤ) × F)) = ⊤ := by
    rw [hUS']; exact hgα'
  obtain ⟨T₀, hT₀⟩ := hbound S hSbox hSgen φ (fun χ hχ => (hφ χ hχ).1)
    γ.toAddMonoidHom (fun χ hχ => (hφ χ hχ).2.1)
  obtain ⟨T₀', hT₀'⟩ := hbound S' hS'box hS'gen φ' (fun χ hχ => (hφ' χ hχ).1)
    γ.symm.toAddMonoidHom (fun χ hχ => (hφ' χ hχ).2.1)
  have hφ'φ : ∀ χ ∈ S, φ' (φ χ) = χ := by
    intro χ hχ
    have h1 : φ χ ∈ S' := by
      rw [← Finset.mem_coe, hUS']; exact (hφ χ hχ).2.2
    have hbox : χ ∈ (mbox r F n : Set ((r → ℤ) × F)) := (Finset.mem_filter.mp hχ).1
    apply hinj (hφ' _ h1).1 hbox
    rw [(hφ' _ h1).2.1, (hφ χ hχ).2.1, AddEquiv.symm_apply_apply]
  have hφφ' : ∀ χ ∈ S', φ (φ' χ) = χ := by
    intro χ hχ
    have h1 : φ' χ ∈ S := by
      rw [← Finset.mem_coe, hUS]; exact (hφ' χ hχ).2.2
    have hbox : χ ∈ (mbox r F n : Set ((r → ℤ) × F)) := (Finset.mem_filter.mp hχ).1
    apply hinj (hφ _ h1).1 hbox
    rw [(hφ _ h1).2.1, (hφ' χ hχ).2.1, AddEquiv.apply_symm_apply]
  have hleft : T₀'.comp T₀ = AddMonoidHom.id _ := by
    apply AddMonoidHom.eq_of_eqOn_dense hSgen
    intro χ hχ
    have h1 : φ χ ∈ S' := by
      rw [← Finset.mem_coe, hUS']; exact (hφ χ hχ).2.2
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
    rw [hT₀ χ hχ, hT₀' _ h1, hφ'φ χ hχ]
  have hright : T₀.comp T₀' = AddMonoidHom.id _ := by
    apply AddMonoidHom.eq_of_eqOn_dense hS'gen
    intro χ hχ
    have h1 : φ' χ ∈ S := by
      rw [← Finset.mem_coe, hUS]; exact (hφ' χ hχ).2.2
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
    rw [hT₀' χ hχ, hT₀ _ h1, hφφ' χ hχ]
  let T : (r → ℤ) × F ≃+ (r → ℤ) × F :=
    { toFun := T₀, invFun := T₀',
      left_inv := fun x => congrArg (fun F => F x) hleft,
      right_inv := fun x => congrArg (fun F => F x) hright,
      map_add' := T₀.map_add }
  refine ⟨T, ?_⟩
  have hredT : (mred r F m).comp T.toAddMonoidHom = γ.toAddMonoidHom.comp (mred r F m) := by
    apply AddMonoidHom.eq_of_eqOn_dense hSgen
    intro χ hχ
    simp only [AddMonoidHom.comp_apply]
    change mred r F m (T₀ χ) = γ (mred r F m χ)
    rw [hT₀ χ hχ, (hφ χ hχ).2.1]
  apply HopfPointExtension.eq_of_mapDomain_eq hgen (mred r F m) hinj
  · intro i
    refine (support_mapDomainAlgHom_subset (R := R) _ (subset_refl _)).trans ?_
    rintro _ ⟨χ, hχ, rfl⟩
    have hχS : χ ∈ S := by
      rw [← Finset.mem_coe, hUS]; exact Set.mem_iUnion.mpr ⟨i, hχ⟩
    change T₀ χ ∈ (mbox r F n : Set ((r → ℤ) × F))
    rw [hT₀ χ hχS]
    exact (hφ χ hχS).1
  · exact hα'
  · rw [← AlgHom.comp_assoc, ← AddMonoidAlgebra.mapDomainAlgHom_comp, hredT,
      AddMonoidAlgebra.mapDomainAlgHom_comp, AlgHom.comp_assoc, h]

/-- Rigidity for kernels: under the hypotheses of `exists_addEquiv_of_mred_eq`, the two
Hopf points have the same kernel after scalar extension. -/
theorem ker_scalarExt_eq_of_mred_eq {n m : ℕ} (hm : rigidityBound r F n ≤ m)
    {gen : σ → A} (hgen : Algebra.adjoin R (Set.range gen) = ⊤)
    {α α' : A →ₐ[R] AddMonoidAlgebra C ((r → ℤ) × F)}
    (hα : ∀ i, ↑(α (gen i)).coeff.support ⊆ (mbox r F n : Set ((r → ℤ) × F)))
    (hα' : ∀ i, ↑(α' (gen i)).coeff.support ⊆ (mbox r F n : Set ((r → ℤ) × F)))
    (hgα : AddSubgroup.closure
      (⋃ i, (↑(α (gen i)).coeff.support : Set ((r → ℤ) × F))) = ⊤)
    (hgα' : AddSubgroup.closure
      (⋃ i, (↑(α' (gen i)).coeff.support : Set ((r → ℤ) × F))) = ⊤)
    (γ : (r → ZMod m) × F ≃+ (r → ZMod m) × F)
    (h : (AddMonoidAlgebra.mapDomainAlgHom R C (mred r F m)).comp α' =
      (AddMonoidAlgebra.mapDomainAlgHom R C γ.toAddMonoidHom).comp
        ((AddMonoidAlgebra.mapDomainAlgHom R C (mred r F m)).comp α)) :
    RingHom.ker (scalarExt α') = RingHom.ker (scalarExt α) := by
  obtain ⟨T, hT⟩ := exists_addEquiv_of_mred_eq hm hgen hα hα' hgα hgα' γ h
  rw [← hT, HopfPointKernel.ker_scalarExt_mapDomain_addEquiv]

end Langlands.Algebra.MixedHopfPointRigidity
