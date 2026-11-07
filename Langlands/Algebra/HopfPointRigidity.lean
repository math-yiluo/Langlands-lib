import Langlands.Algebra.HopfPointExtension
import Langlands.Algebra.LatticeConfigurationBound
import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Hopf points of a lattice with bounded generator supports are determined modulo `m` -/

noncomputable section

open TensorProduct

namespace Langlands.Algebra.HopfPointRigidity

open HopfPointExtension LatticeConfiguration

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Bialgebra R A]
  {C : Type*} [CommRing C] [Algebra R C] {r : Type*} [Fintype r] [DecidableEq r]
  {σ : Type*}

/-- Reduction modulo `m` is injective on the box of radius `n` when `2n < m`. -/
theorem injOn_red_box {n m : ℕ} (hm : 2 * n < m) :
    Set.InjOn (red r m) (box r n : Set (r → ℤ)) := by
  intro x hx y hy h
  funext j
  have hxj := (mem_box.mp hx) j
  have hyj := (mem_box.mp hy) j
  have hj : ((x j - y j : ℤ) : ZMod m) = 0 := by
    have := congrFun h j
    simp only [red_apply] at this
    push_cast
    rw [this, sub_self]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hj
  have : x j - y j = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hj
    have h1 := abs_sub (x j) (y j)
    have : |x j| + |y j| < m := by
      have : (|x j| + |y j| : ℤ) ≤ 2 * n := by linarith
      exact_mod_cast lt_of_le_of_lt this (by exact_mod_cast hm)
    linarith
  linarith

omit [DecidableEq r] in
/-- If the values on generators span `C[M]` as a `C`-algebra over a nonzero ring,
their supports generate `M`. -/
theorem closure_support_eq_top [Nontrivial C] {gen : σ → A}
    (hgen : Algebra.adjoin R (Set.range gen) = ⊤)
    {α : A →ₐ[R] AddMonoidAlgebra C (r → ℤ)}
    (hα : Algebra.adjoin C (Set.range α) = ⊤) :
    AddSubgroup.closure (⋃ i, (↑(α (gen i)).coeff.support : Set (r → ℤ))) = ⊤ := by
  classical
  set T := AddSubmonoid.closure (⋃ i, (↑(α (gen i)).coeff.support : Set (r → ℤ)))
  have key : ∀ x ∈ Algebra.adjoin C (Set.range (α ∘ gen)),
      (x.coeff.support : Set (r → ℤ)) ⊆ (T : Set (r → ℤ)) := by
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
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R C (AddMonoidAlgebra C (r → ℤ))]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  rw [eq_top_iff]
  intro χ _
  have hmem : AddMonoidAlgebra.single χ (1 : C) ∈ Algebra.adjoin C (Set.range (α ∘ gen)) :=
    hrange (hα ▸ Algebra.mem_top)
  have hχ : χ ∈ ((AddMonoidAlgebra.single χ (1 : C)).coeff.support : Set (r → ℤ)) := by
    simp [AddMonoidAlgebra.coeff_single]
  have hT : χ ∈ T := key _ hmem hχ
  exact (AddSubmonoid.closure_le.mpr fun z hz => AddSubgroup.subset_closure hz) hT

/-- A modulus beyond which bounded configurations are rigid. -/
def rigidityBound (r : Type*) [Fintype r] [DecidableEq r] (n : ℕ) : ℕ :=
  max (Classical.choose (exists_bound r n)) (2 * n + 1)

/-- Coefficient transport: the reduction of `α'` is the twist of the reduction of `α`. -/
theorem exists_mem_support_of_red {m n : ℕ} (hm : 2 * n < m)
    (γ : (r → ZMod m) ≃+ (r → ZMod m))
    {x x' : AddMonoidAlgebra C (r → ℤ)}
    (hx : ↑x.coeff.support ⊆ (box r n : Set (r → ℤ)))
    (h : AddMonoidAlgebra.mapDomainAlgHom R C (red r m) x' =
      AddMonoidAlgebra.mapDomainAlgHom R C γ.toAddMonoidHom
        (AddMonoidAlgebra.mapDomainAlgHom R C (red r m) x))
    {χ : r → ℤ} (hχ : χ ∈ x.coeff.support) :
    ∃ χ' ∈ x'.coeff.support, red r m χ' = γ (red r m χ) := by
  classical
  have hinj := injOn_red_box (r := r) hm
  have hcoeff : (AddMonoidAlgebra.mapDomainAlgHom R C (red r m) x').coeff (γ (red r m χ)) =
      x.coeff χ := by
    rw [h, coeff_mapDomainAlgHom, coeff_mapDomainAlgHom]
    rw [show (γ.toAddMonoidHom : (r → ZMod m) → (r → ZMod m)) = γ from rfl,
      Finsupp.mapDomain_apply_of_injective γ.injective (Finsupp.mapDomain (red r m) x.coeff)
        (red r m χ)]
    exact Finsupp.mapDomain_apply' _ x.coeff hx hinj (hx hχ)
  have hne : (AddMonoidAlgebra.mapDomainAlgHom R C (red r m) x').coeff (γ (red r m χ)) ≠ 0 := by
    rw [hcoeff]; exact Finsupp.mem_support_iff.mp hχ
  rw [coeff_mapDomainAlgHom] at hne
  obtain ⟨χ', hχ', he⟩ :=
    Finset.mem_image.mp (Finsupp.mapDomain_support (Finsupp.mem_support_iff.mpr hne))
  exact ⟨χ', hχ', he⟩

/-- Rigidity of bounded Hopf points: two Hopf points into `C[ℤ^r]` with generator
values supported in the box of radius `n`, whose supports generate `ℤ^r`, and whose
reductions modulo `m ≥ rigidityBound r n` differ by an automorphism of
`(ℤ/m)^r`, differ by an automorphism of `ℤ^r`. -/
theorem exists_addEquiv_of_red_eq {n m : ℕ} (hm : rigidityBound r n ≤ m)
    {gen : σ → A} (hgen : Algebra.adjoin R (Set.range gen) = ⊤)
    {α α' : A →ₐ[R] AddMonoidAlgebra C (r → ℤ)}
    (hα : ∀ i, ↑(α (gen i)).coeff.support ⊆ (box r n : Set (r → ℤ)))
    (hα' : ∀ i, ↑(α' (gen i)).coeff.support ⊆ (box r n : Set (r → ℤ)))
    (hgα : AddSubgroup.closure (⋃ i, (↑(α (gen i)).coeff.support : Set (r → ℤ))) = ⊤)
    (hgα' : AddSubgroup.closure (⋃ i, (↑(α' (gen i)).coeff.support : Set (r → ℤ))) = ⊤)
    (γ : (r → ZMod m) ≃+ (r → ZMod m))
    (h : (AddMonoidAlgebra.mapDomainAlgHom R C (red r m)).comp α' =
      (AddMonoidAlgebra.mapDomainAlgHom R C γ.toAddMonoidHom).comp
        ((AddMonoidAlgebra.mapDomainAlgHom R C (red r m)).comp α)) :
    ∃ T : (r → ℤ) ≃+ (r → ℤ),
      (AddMonoidAlgebra.mapDomainAlgHom R C T.toAddMonoidHom).comp α = α' := by
  classical
  have hm₀ : Classical.choose (exists_bound r n) ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : 2 * n < m := lt_of_lt_of_le (by omega) (le_trans (le_max_right _ _) hm)
  have hinj := injOn_red_box (r := r) hm2
  have hbound := Classical.choose_spec (exists_bound r n) m hm₀
  -- the two support configurations
  let U : Set (r → ℤ) := ⋃ i, (↑(α (gen i)).coeff.support : Set (r → ℤ))
  let U' : Set (r → ℤ) := ⋃ i, (↑(α' (gen i)).coeff.support : Set (r → ℤ))
  let S : Finset (r → ℤ) := (box r n).filter (· ∈ U)
  let S' : Finset (r → ℤ) := (box r n).filter (· ∈ U')
  have hUS : (S : Set (r → ℤ)) = U := by
    ext χ
    simp only [S, Finset.coe_filter, Set.mem_ofPred_eq]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    exact hα i hi
  have hUS' : (S' : Set (r → ℤ)) = U' := by
    ext χ
    simp only [S', Finset.coe_filter, Set.mem_ofPred_eq]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    exact hα' i hi
  have hcoeffs : ∀ i, AddMonoidAlgebra.mapDomainAlgHom R C (red r m) (α' (gen i)) =
      AddMonoidAlgebra.mapDomainAlgHom R C γ.toAddMonoidHom
        (AddMonoidAlgebra.mapDomainAlgHom R C (red r m) (α (gen i))) :=
    fun i => congrArg (fun F => F (gen i)) h
  have hcoeffs' : ∀ i, AddMonoidAlgebra.mapDomainAlgHom R C (red r m) (α (gen i)) =
      AddMonoidAlgebra.mapDomainAlgHom R C γ.symm.toAddMonoidHom
        (AddMonoidAlgebra.mapDomainAlgHom R C (red r m) (α' (gen i))) := by
    intro i
    rw [hcoeffs i]
    set y := AddMonoidAlgebra.mapDomainAlgHom R C (red r m) (α (gen i))
    rw [← AlgHom.comp_apply (AddMonoidAlgebra.mapDomainAlgHom R C γ.symm.toAddMonoidHom)
      (AddMonoidAlgebra.mapDomainAlgHom R C γ.toAddMonoidHom) y,
      ← AddMonoidAlgebra.mapDomainAlgHom_comp]
    have : γ.symm.toAddMonoidHom.comp γ.toAddMonoidHom = AddMonoidHom.id _ := by
      ext x; simp
    rw [this, AddMonoidAlgebra.mapDomainAlgHom_id, AlgHom.id_apply]
  -- the correspondence of supports
  let φ : (r → ℤ) → (r → ℤ) := fun χ => Function.invFunOn (red r m) (box r n) (γ (red r m χ))
  let φ' : (r → ℤ) → (r → ℤ) :=
    fun χ => Function.invFunOn (red r m) (box r n) (γ.symm (red r m χ))
  have hφ : ∀ χ ∈ S, φ χ ∈ box r n ∧ red r m (φ χ) = γ (red r m χ) ∧ φ χ ∈ U' := by
    intro χ hχ
    have hχU : χ ∈ U := by rw [← hUS]; exact hχ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hχU
    obtain ⟨χ', hχ', he⟩ :=
      exists_mem_support_of_red (R := R) hm2 γ (hα i) (hcoeffs i) hi
    have hχ'box : χ' ∈ (box r n : Set (r → ℤ)) := hα' i hχ'
    have hex : ∃ a ∈ (box r n : Set (r → ℤ)), red r m a = γ (red r m χ) := ⟨χ', hχ'box, he⟩
    have hmem := Function.invFunOn_mem hex
    have heq := Function.invFunOn_eq hex
    have : φ χ = χ' := hinj hmem hχ'box (heq.trans he.symm)
    exact ⟨hmem, heq, this ▸ Set.mem_iUnion.mpr ⟨i, hχ'⟩⟩
  have hφ' : ∀ χ ∈ S', φ' χ ∈ box r n ∧ red r m (φ' χ) = γ.symm (red r m χ) ∧ φ' χ ∈ U := by
    intro χ hχ
    have hχU : χ ∈ U' := by rw [← hUS']; exact hχ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hχU
    obtain ⟨χ', hχ', he⟩ :=
      exists_mem_support_of_red (R := R) hm2 γ.symm (hα' i) (hcoeffs' i) hi
    have hχ'box : χ' ∈ (box r n : Set (r → ℤ)) := hα i hχ'
    have hex : ∃ a ∈ (box r n : Set (r → ℤ)), red r m a = γ.symm (red r m χ) :=
      ⟨χ', hχ'box, he⟩
    have hmem := Function.invFunOn_mem hex
    have heq := Function.invFunOn_eq hex
    have : φ' χ = χ' := hinj hmem hχ'box (heq.trans he.symm)
    exact ⟨hmem, heq, this ▸ Set.mem_iUnion.mpr ⟨i, hχ'⟩⟩
  have hSbox : ∀ χ ∈ S, ∀ j, |χ j| ≤ n := fun χ hχ => mem_box.mp (Finset.mem_filter.mp hχ).1
  have hS'box : ∀ χ ∈ S', ∀ j, |χ j| ≤ n := fun χ hχ => mem_box.mp (Finset.mem_filter.mp hχ).1
  have hSgen : AddSubgroup.closure (S : Set (r → ℤ)) = ⊤ := by rw [hUS]; exact hgα
  have hS'gen : AddSubgroup.closure (S' : Set (r → ℤ)) = ⊤ := by rw [hUS']; exact hgα'
  obtain ⟨T₀, hT₀⟩ := hbound S hSbox hSgen φ (fun χ hχ => mem_box.mp (hφ χ hχ).1)
    γ.toAddMonoidHom (fun χ hχ => (hφ χ hχ).2.1)
  obtain ⟨T₀', hT₀'⟩ := hbound S' hS'box hS'gen φ' (fun χ hχ => mem_box.mp (hφ' χ hχ).1)
    γ.symm.toAddMonoidHom (fun χ hχ => (hφ' χ hχ).2.1)
  have hφ'φ : ∀ χ ∈ S, φ' (φ χ) = χ := by
    intro χ hχ
    have h1 : φ χ ∈ S' := by
      rw [← Finset.mem_coe, hUS']; exact (hφ χ hχ).2.2
    have hbox : χ ∈ (box r n : Set (r → ℤ)) := (Finset.mem_filter.mp hχ).1
    apply hinj (hφ' _ h1).1 hbox
    rw [(hφ' _ h1).2.1, (hφ χ hχ).2.1, AddEquiv.symm_apply_apply]
  have hφφ' : ∀ χ ∈ S', φ (φ' χ) = χ := by
    intro χ hχ
    have h1 : φ' χ ∈ S := by
      rw [← Finset.mem_coe, hUS]; exact (hφ' χ hχ).2.2
    have hbox : χ ∈ (box r n : Set (r → ℤ)) := (Finset.mem_filter.mp hχ).1
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
  let T : (r → ℤ) ≃+ (r → ℤ) :=
    { toFun := T₀, invFun := T₀',
      left_inv := fun x => congrArg (fun F => F x) hleft,
      right_inv := fun x => congrArg (fun F => F x) hright,
      map_add' := T₀.map_add }
  refine ⟨T, ?_⟩
  have hredT : (red r m).comp T.toAddMonoidHom = γ.toAddMonoidHom.comp (red r m) := by
    apply AddMonoidHom.eq_of_eqOn_dense hSgen
    intro χ hχ
    simp only [AddMonoidHom.comp_apply]
    change red r m (T₀ χ) = γ (red r m χ)
    rw [hT₀ χ hχ, (hφ χ hχ).2.1]
  apply HopfPointExtension.eq_of_mapDomain_eq hgen (red r m) hinj
  · intro i
    refine (support_mapDomainAlgHom_subset (R := R) _ (subset_refl _)).trans ?_
    rintro _ ⟨χ, hχ, rfl⟩
    have hχS : χ ∈ S := by
      rw [← Finset.mem_coe, hUS]; exact Set.mem_iUnion.mpr ⟨i, hχ⟩
    change T₀ χ ∈ (box r n : Set (r → ℤ))
    rw [hT₀ χ hχS]
    exact (hφ χ hχS).1
  · exact hα'
  · rw [← AlgHom.comp_assoc, ← AddMonoidAlgebra.mapDomainAlgHom_comp, hredT,
      AddMonoidAlgebra.mapDomainAlgHom_comp, AlgHom.comp_assoc, h]

end Langlands.Algebra.HopfPointRigidity
