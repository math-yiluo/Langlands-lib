import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-! # Orbits of pairing-preserving actions on simple roots -/

noncomputable section

open Set Function

set_option autoImplicit false

namespace Langlands.LinearAlgebra.RootDatumOrbitPairs

variable {ι M N : Type*} [Finite ι] [AddCommGroup M] [AddCommGroup N]
    {P : RootDatum ι M N} (b : P.Base) {Γ : Type*} [Group Γ]
    (ρ : Γ →* Equiv.Perm b.support)

/-- Every group element acts on the simple roots through a permutation of all
root indices preserving the integral pairing. -/
def IsPairingCompatible : Prop :=
  ∀ γ : Γ, ∃ e : ι ≃ ι, (∀ i j, P.pairing (e i) (e j) = P.pairing i j) ∧
    ∀ a : b.support, ((ρ γ a : b.support) : ι) = e a

omit [Finite ι] in
variable {b ρ} in
/-- A pairing-compatible action preserves the pairing of simple roots. -/
theorem IsPairingCompatible.pairing_apply (hρ : IsPairingCompatible b ρ) (γ : Γ)
    (a c : b.support) :
    P.pairing (ρ γ a : ι) (ρ γ c : ι) = P.pairing a c := by
  obtain ⟨e, he, hρe⟩ := hρ γ
  rw [hρe, hρe, he]

omit [Finite ι] in
private theorem rootForm_root_root [Fintype ι] (i j : ι) :
    P.RootForm (P.root i) (P.root j) = ∑ k, P.pairing i k * P.pairing j k := by
  simp [RootPairing.rootForm_apply_apply]

omit [Finite ι] in
private theorem rootForm_root_equiv [Fintype ι] (e : ι ≃ ι)
    (he : ∀ i j, P.pairing (e i) (e j) = P.pairing i j) (i j : ι) :
    P.RootForm (P.root (e i)) (P.root (e j)) = P.RootForm (P.root i) (P.root j) := by
  rw [rootForm_root_root, rootForm_root_root, ← Equiv.sum_comp e]
  simp only [he]

omit [Finite ι] in
private theorem rootForm_root_comm [Fintype ι] (i j : ι) :
    P.RootForm (P.root i) (P.root j) = P.RootForm (P.root j) (P.root i) := by
  rw [rootForm_root_root, rootForm_root_root]
  simp only [mul_comm]

omit [Finite ι] in
private theorem two_mul_rootForm_root_root [Fintype ι] (i j : ι) :
    2 * P.RootForm (P.root i) (P.root j) =
      P.pairing j i * P.RootForm (P.root i) (P.root i) := by
  have h := congrArg (P.toLinearMap (P.root j)) (P.rootForm_self_smul_coroot i)
  simp only [map_smul, map_nsmul, RootPairing.root_coroot_eq_pairing,
    RootPairing.toLinearMap_apply_apply_Polarization, smul_eq_mul, nsmul_eq_mul] at h
  push_cast at h
  linarith

omit [Finite ι] in
private theorem rootForm_pos [Fintype ι] {x : M} (hx : x ∈ P.rootSpan ℤ) (hx0 : x ≠ 0) :
    0 < P.RootForm x x := by
  rw [RootPairing.rootForm_apply_apply]
  have hnonneg : ∀ k ∈ Finset.univ, 0 ≤ P.coroot' k x * P.coroot' k x :=
    fun k _ => mul_self_nonneg _
  rcases (Finset.sum_nonneg hnonneg).lt_or_eq with h | h
  · exact h
  · exfalso
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h.symm
    have hker : x ∈ LinearMap.ker P.RootForm := by
      rw [LinearMap.mem_ker]
      ext y
      rw [RootPairing.rootForm_apply_apply, LinearMap.zero_apply]
      refine Finset.sum_eq_zero fun k hk => ?_
      have := hzero k hk
      rw [mul_self_eq_zero] at this
      rw [this, zero_mul]
    exact hx0 ((Submodule.disjoint_def.mp P.disjoint_rootSpan_ker_rootForm) x hx hker)

omit [Finite ι] in
private theorem pairing_eq_pairingIn (i j : ι) : P.pairing i j = P.pairingIn ℤ i j := by
  rw [← P.algebraMap_pairingIn ℤ i j]
  rfl

section Orbit

open scoped Classical

variable {b} (hρ : IsPairingCompatible b ρ) (a : b.support)

/-- The orbit of `a`. -/
private def orbit : Finset b.support :=
  Finset.univ.filter fun j => ∃ γ : Γ, ρ γ a = j

/-- The non-orthogonal companions of `i` in the orbit of `a`. -/
private def companions (i : b.support) : Finset b.support :=
  ((orbit ρ a).erase i).filter fun j => P.pairing (j : ι) i ≠ 0

omit [Finite ι] in
private theorem self_mem_orbit : a ∈ orbit ρ a := by
  simp only [orbit, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨1, by simp⟩

omit [Finite ι] in
private theorem apply_mem_orbit' (γ : Γ) : ρ γ a ∈ orbit ρ a := by
  simp only [orbit, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨γ, rfl⟩

omit [Finite ι] in
private theorem apply_mem_orbit {i : b.support} (hi : i ∈ orbit ρ a) (δ : Γ) :
    ρ δ i ∈ orbit ρ a := by
  simp only [orbit, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  obtain ⟨γ, rfl⟩ := hi
  exact ⟨δ * γ, by rw [map_mul, Equiv.Perm.mul_apply]⟩

omit [Finite ι] in
private theorem mem_companions {i j : b.support} (hj : j ∈ orbit ρ a) (hji : j ≠ i)
    (hpair : P.pairing (j : ι) i ≠ 0) : j ∈ companions ρ a i := by
  simp only [companions, Finset.mem_filter, Finset.mem_erase]
  exact ⟨⟨hji, hj⟩, hpair⟩

omit [Finite ι] in
include hρ in
private theorem card_companions_le (i : b.support) (δ : Γ) :
    (companions ρ a i).card ≤ (companions ρ a (ρ δ i)).card := by
  refine Finset.card_le_card_of_injOn (ρ δ) (fun j hj => ?_)
    (fun j _ j' _ h => (ρ δ).injective h)
  simp only [companions, Finset.coe_filter, Finset.mem_erase, Set.mem_ofPred_eq] at hj ⊢
  obtain ⟨⟨hji, hj⟩, hpair⟩ := hj
  refine ⟨⟨fun h => hji ((ρ δ).injective h), apply_mem_orbit ρ a hj δ⟩, ?_⟩
  rwa [hρ.pairing_apply]

omit [Finite ι] in
include hρ in
private theorem card_companions_eq {i : b.support} (hi : i ∈ orbit ρ a) :
    (companions ρ a i).card = (companions ρ a a).card := by
  obtain ⟨γ, rfl⟩ : ∃ γ : Γ, ρ γ a = i := by
    simpa [orbit] using hi
  refine le_antisymm ?_ (card_companions_le ρ hρ a a γ)
  have h := card_companions_le ρ hρ a (ρ γ a) γ⁻¹
  rwa [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Equiv.Perm.one_apply] at h

private theorem sum_pairing_le (i : b.support) (hi : i ∈ orbit ρ a) :
    ∑ j ∈ orbit ρ a, P.pairing (j : ι) i ≤ 2 - (companions ρ a i).card := by
  rw [← Finset.add_sum_erase _ _ hi, P.pairing_same]
  have hle : ∑ j ∈ (orbit ρ a).erase i, P.pairing (j : ι) i ≤
      ∑ j ∈ (orbit ρ a).erase i, if P.pairing (j : ι) i ≠ 0 then (-1 : ℤ) else 0 := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hji : (j : ι) ≠ i := fun h => (Finset.mem_erase.mp hj).1 (Subtype.ext h)
    have hle0 : P.pairing (j : ι) i ≤ 0 := by
      rw [pairing_eq_pairingIn]
      exact b.pairingIn_le_zero_of_ne hji j.2 i.2
    split_ifs with h
    · omega
    · exact hle0
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_neg,
    nsmul_eq_mul, mul_one] at hle
  simp only [companions]
  omega

omit [Finite ι] in
include hρ in
private theorem two_mul_rootForm_orbitSum [Fintype ι] :
    2 * P.RootForm (∑ i ∈ orbit ρ a, P.root (i : ι)) (∑ j ∈ orbit ρ a, P.root (j : ι)) =
      P.RootForm (P.root a) (P.root a) *
        ∑ i ∈ orbit ρ a, ∑ j ∈ orbit ρ a, P.pairing (j : ι) i := by
  simp only [map_sum, LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨γ, rfl⟩ : ∃ γ : Γ, ρ γ a = i := by
    simpa [orbit] using hi
  obtain ⟨e, he, hρe⟩ := hρ γ
  have key : 2 * P.RootForm (P.root (ρ γ a : ι)) (P.root (j : ι)) =
      P.RootForm (P.root a) (P.root a) * P.pairing (j : ι) (ρ γ a : ι) := by
    rw [two_mul_rootForm_root_root, hρe a, rootForm_root_equiv e he, mul_comm]
  rw [rootForm_root_comm]
  exact key

include hρ in
private theorem card_companions_le_one [Fintype ι] : (companions ρ a a).card ≤ 1 := by
  have ha := self_mem_orbit ρ a
  have hmem : (∑ i ∈ orbit ρ a, P.root (i : ι)) ∈ P.rootSpan ℤ :=
    Submodule.sum_mem _ fun i _ => Submodule.subset_span (Set.mem_range_self _)
  have hne : (∑ i ∈ orbit ρ a, P.root (i : ι)) ≠ 0 := by
    intro h
    have hli := linearIndepOn_iff'.mp b.linearIndepOn_root
      ((orbit ρ a).map (Function.Embedding.subtype _)) 1
      (fun x hx => by
        obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
        exact y.2)
      (by simpa using h) (a : ι) (by simp [ha])
    simp at hli
  have hpos := rootForm_pos hmem hne
  have hℓ : 0 < P.RootForm (P.root a) (P.root a) :=
    rootForm_pos (Submodule.subset_span (Set.mem_range_self _)) (P.ne_zero a)
  have hS : 0 < ∑ i ∈ orbit ρ a, ∑ j ∈ orbit ρ a, P.pairing (j : ι) i := by
    have h2 := two_mul_rootForm_orbitSum ρ hρ a
    nlinarith
  have hbound : ∑ i ∈ orbit ρ a, ∑ j ∈ orbit ρ a, P.pairing (j : ι) i ≤
      ∑ _i ∈ orbit ρ a, (2 - ((companions ρ a a).card : ℤ)) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have := sum_pairing_le ρ a i hi
    rwa [card_companions_eq ρ hρ a hi] at this
  rw [Finset.sum_const, nsmul_eq_mul] at hbound
  by_contra hk
  replace hk := not_le.mp hk
  have hk' : (2 : ℤ) - (companions ρ a a).card ≤ 0 := by omega
  have := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α := ℤ) (orbit ρ a).card) hk'
  omega

include hρ in
private theorem companion_unique [Fintype ι] {i : b.support} (hi : i ∈ orbit ρ a)
    {j j' : b.support} (hj : j ∈ companions ρ a i) (hj' : j' ∈ companions ρ a i) :
    j = j' := by
  have h := card_companions_le_one ρ hρ a
  rw [← card_companions_eq ρ hρ a hi] at h
  exact Finset.card_le_one.mp h j hj j' hj'

end Orbit

omit [Finite ι] in
private theorem pairing_ne_zero_of_not_isOrthogonal {i j : ι} (h : ¬ P.IsOrthogonal i j) :
    P.pairing j i ≠ 0 := by
  intro hji
  exact h ⟨P.pairing_eq_zero_iff'.mpr hji, hji⟩

variable {b ρ} (hρ : IsPairingCompatible b ρ)

include hρ in
/-- A simple root has at most one non-orthogonal companion in its orbit. -/
theorem eq_of_not_isOrthogonal (a : b.support) {γ δ : Γ} (hγ : ρ γ a ≠ a) (hδ : ρ δ a ≠ a)
    (hγo : ¬ P.IsOrthogonal (a : ι) (ρ γ a : ι)) (hδo : ¬ P.IsOrthogonal (a : ι) (ρ δ a : ι)) :
    ρ γ a = ρ δ a := by
  classical
  let := Fintype.ofFinite ι
  exact companion_unique ρ hρ a (self_mem_orbit ρ a)
    (mem_companions ρ a (apply_mem_orbit' ρ a γ) hγ (pairing_ne_zero_of_not_isOrthogonal hγo))
    (mem_companions ρ a (apply_mem_orbit' ρ a δ) hδ (pairing_ne_zero_of_not_isOrthogonal hδo))

include hρ in
/-- Two distinct non-orthogonal simple roots in one orbit form an `A₂` pair:
both pairings are `-1`. -/
theorem pairing_eq_neg_one_of_not_isOrthogonal (a : b.support) {γ : Γ} (hγ : ρ γ a ≠ a)
    (hγo : ¬ P.IsOrthogonal (a : ι) (ρ γ a : ι)) :
    P.pairing (a : ι) (ρ γ a : ι) = -1 ∧ P.pairing (ρ γ a : ι) a = -1 := by
  classical
  let := Fintype.ofFinite ι
  set c := ρ γ a with hc
  obtain ⟨e, he, hρe⟩ := hρ γ
  have hlen : P.RootForm (P.root c) (P.root c) = P.RootForm (P.root a) (P.root a) := by
    rw [hc, hρe a, rootForm_root_equiv e he]
  have hℓ : 0 < P.RootForm (P.root a) (P.root a) :=
    rootForm_pos (Submodule.subset_span (Set.mem_range_self _)) (P.ne_zero a)
  have h1 := two_mul_rootForm_root_root (P := P) (a : ι) (c : ι)
  have h2 := two_mul_rootForm_root_root (P := P) (c : ι) (a : ι)
  rw [hlen, rootForm_root_comm (c : ι) (a : ι)] at h2
  have hsymm : P.pairing (a : ι) c = P.pairing (c : ι) a := by
    have : P.pairing (c : ι) a * P.RootForm (P.root a) (P.root a) =
        P.pairing (a : ι) c * P.RootForm (P.root a) (P.root a) := by
      rw [← h1, ← h2]
    exact (mul_right_cancel₀ hℓ.ne' this).symm
  have hca : (c : ι) ≠ a := fun h => hγ (Subtype.ext h)
  have hle : P.pairing (c : ι) a ≤ 0 := by
    rw [pairing_eq_pairingIn]
    exact b.pairingIn_le_zero_of_ne hca c.2 a.2
  have hne : P.pairing (c : ι) a ≠ 0 := pairing_ne_zero_of_not_isOrthogonal hγo
  have hmem : P.root (a : ι) + P.root (c : ι) ∈ P.rootSpan ℤ :=
    Submodule.add_mem _ (Submodule.subset_span (Set.mem_range_self _))
      (Submodule.subset_span (Set.mem_range_self _))
  have hsum0 : P.root (a : ι) + P.root (c : ι) ≠ 0 := by
    intro h
    exact b.root_ne_neg_of_ne a.2 c.2 (fun h' => hca h'.symm) (eq_neg_of_add_eq_zero_left h)
  have hpos := rootForm_pos hmem hsum0
  simp only [map_add, LinearMap.add_apply] at hpos
  rw [rootForm_root_comm (c : ι) (a : ι), hlen] at hpos
  have : -2 < P.pairing (c : ι) a := by nlinarith
  constructor <;> omega

include hρ in
/-- The element moving a simple root to its non-orthogonal companion swaps the
two roots. -/
theorem apply_apply_eq_of_not_isOrthogonal (a : b.support) {γ : Γ} (hγ : ρ γ a ≠ a)
    (hγo : ¬ P.IsOrthogonal (a : ι) (ρ γ a : ι)) :
    ρ γ (ρ γ a) = a := by
  classical
  let := Fintype.ofFinite ι
  have hc := apply_mem_orbit' ρ a γ
  have hpair : P.pairing (ρ γ a : ι) a ≠ 0 := pairing_ne_zero_of_not_isOrthogonal hγo
  have h1 : ρ γ (ρ γ a) ∈ companions ρ a (ρ γ a) := by
    refine mem_companions ρ a (apply_mem_orbit ρ a hc γ)
      (fun h => hγ ((ρ γ).injective h)) ?_
    rwa [hρ.pairing_apply]
  have h2 : a ∈ companions ρ a (ρ γ a) :=
    mem_companions ρ a (self_mem_orbit ρ a) (Ne.symm hγ)
      (fun h => hpair (P.pairing_eq_zero_iff'.mp h))
  exact companion_unique ρ hρ a hc h1 h2

include hρ in
/-- The sum of two non-orthogonal simple roots in one orbit is a root. -/
theorem exists_root_eq_add_of_not_isOrthogonal (a : b.support) {γ : Γ} (hγ : ρ γ a ≠ a)
    (hγo : ¬ P.IsOrthogonal (a : ι) (ρ γ a : ι)) :
    ∃ k : ι, P.root k = P.root a + P.root (ρ γ a : ι) := by
  refine ⟨P.reflectionPerm (ρ γ a : ι) a, ?_⟩
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    (pairing_eq_neg_one_of_not_isOrthogonal hρ a hγ hγo).1]
  simp [sub_eq_add_neg]

include hρ in
/-- Orbits are orthogonal as soon as no orbit contains an `A₂` pair. -/
theorem isOrthogonal_of_forall_pairing_ne_neg_one
    (h : ∀ (γ : Γ) (a : b.support), ρ γ a ≠ a → P.pairing (a : ι) (ρ γ a : ι) ≠ -1)
    (γ : Γ) (a : b.support) (hγ : a ≠ ρ γ a) : P.IsOrthogonal (a : ι) (ρ γ a : ι) := by
  by_contra hγo
  exact h γ a (Ne.symm hγ) (pairing_eq_neg_one_of_not_isOrthogonal hρ a (Ne.symm hγ) hγo).1

end Langlands.LinearAlgebra.RootDatumOrbitPairs
