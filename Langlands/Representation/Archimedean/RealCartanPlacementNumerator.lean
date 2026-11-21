import Langlands.Representation.Archimedean.RealCartanPlacedWeights
import Mathlib.GroupTheory.Perm.Finite

/-! # Normalization of the finite real Cartan placement sum -/

noncomputable section

open Set MeasureTheory

namespace Langlands.Archimedean.RealCartanPlacementNumerator

open Langlands.LocalFactor.Archimedean RealBlockFourierFinite RealBlockPropagation
  RealCartanBlockLayout RealCartanCompactSupport RealCartanFixedCosets RealCartanLowTraceHaar
  RealCartanPlacedTrace RealCartanPlacedWeights RealCartanRadialWeight RealCartanTraceCoordinates
  RealLeviChart RealLeviCompactChart RealPrincipalSeriesDuality RealStandardEllipticCartan

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance] measurableSpaceK RealLeviBlockHaar.secondCountableTopology_GL
  RealLeviBlockHaar.secondCountableTopology_O
local instance borelSpaceK (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩
local instance assignmentFintype {r t : ℕ} (sz : Fin t → ℕ)
    (a : Fin (∑ i, sz i) → Fin r) : Fintype (Assignment sz a) := Fintype.ofFinite _

private theorem perm_positions {α : Type*} {l k : List α} (h : l.Perm k) :
    ∃ e : Fin l.length ≃ Fin k.length, ∀ i, l.get i = k.get (e i) := by
  induction h with
  | nil => exact ⟨Equiv.refl _, fun _ => rfl⟩
  | @cons a l k h ih =>
    obtain ⟨e, he⟩ := ih
    let e' := (finSuccEquiv l.length).trans ((Equiv.optionCongr e).trans (finSuccEquiv k.length).symm)
    refine ⟨e', fun i => ?_⟩
    cases i using Fin.cases with
    | zero => simp [e']
    | succ i =>
      have hs : e' i.succ = (e i).succ := by simp [e']
      exact (he i).trans (congrArg (a :: k).get hs.symm)
  | swap a b l =>
    let e : Equiv.Perm (Fin (l.length + 1 + 1)) := Equiv.swap 0 1
    refine ⟨e, fun i => ?_⟩
    cases i using Fin.cases with
    | zero => simp [e]
    | succ i =>
      cases i using Fin.cases with
      | zero => simp [e, Fin.succ_zero_eq_one]
      | succ i =>
        have h0 : i.succ.succ ≠ (0 : Fin (l.length + 1 + 1)) := Fin.succ_ne_zero _
        have h1 : i.succ.succ ≠ (1 : Fin (l.length + 1 + 1)) := by
          intro hi
          have hv := congrArg Fin.val hi
          simp at hv
        simp [e, Equiv.swap_apply_of_ne_of_ne h0 h1]
  | trans h₁ h₂ ih₁ ih₂ =>
    obtain ⟨e, he⟩ := ih₁
    obtain ⟨f, hf⟩ := ih₂
    exact ⟨e.trans f, fun i => (he i).trans (hf (e i))⟩

section Enumeration

variable {r s t : ℕ} (d : Fin r → ComplexCharacterData) (a : Fin s → RealCharacterData)

private def datum : CartanSlot r s → RealBlock :=
  Sum.elim (fun i => .induced (d i)) (fun j => .character (a j))

private theorem rank_datum (u : CartanSlot r s) : (datum d a u).rank = slotSize u := by
  cases u <;> rfl

private theorem exists_blockEnumeration (b : Fin t → RealBlock) (h : (List.ofFn b).Perm (ofBlockData d a)) :
    ∃ τ : CartanSlot r s ≃ Fin t, ∀ u, b (τ u) = datum d a u := by
  let E : CartanSlot r s ≃ Fin (ofBlockData d a).length := finSumFinEquiv.trans (finCongr (by simp [ofBlockData]))
  have hget (u : CartanSlot r s) : (ofBlockData d a).get (E u) = datum d a u := by
    cases u with
    | inl i => simp [E, ofBlockData, List.getElem_append_left, datum]
    | inr j => simp [E, ofBlockData, List.getElem_append_right, datum]
  obtain ⟨T, hT⟩ := perm_positions h.symm
  let Q := finCongr (show (List.ofFn b).length = t from List.length_ofFn)
  refine ⟨E.trans (T.trans Q), fun u => ?_⟩
  calc
    _ = (List.ofFn b).get (T (E u)) := by
      simp [Q]
      rfl
    _ = _ := (hT (E u)).symm.trans (hget u)

end Enumeration

section Assignments

variable {r s t : ℕ} (sz : Fin t → ℕ) (h : 2 * r + s = ∑ i, sz i)
variable (τ : CartanSlot r s ≃ Fin t) (hτ : ∀ u, sz (τ u) = slotSize u)

local notation "A" => Assignment sz (cartanLabel h)
local notation "Perms" => Equiv.Perm (Fin r) × Equiv.Perm (Fin s)

private def assign (p : Perms) : A :=
  ⟨finSumFinEquiv.symm.trans ((Equiv.sumCongr p.1 p.2).trans τ), fun j => by
    obtain ⟨u, rfl⟩ := finSumFinEquiv.surjective j
    rw [cartanFiber_card, card_cls_fiber]
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply, hτ]
    cases u <;> rfl⟩

private theorem assign_apply (p : Perms) (u : CartanSlot r s) :
    (assign sz h τ hτ p).val (finSumFinEquiv u) = τ (Equiv.sumCongr p.1 p.2 u) := by
  simp only [assign, Equiv.trans_apply, Equiv.symm_apply_apply]

private theorem assign_bijective : Function.Bijective (assign sz h τ hτ) := by
  constructor
  · intro p q he
    have hh (u : CartanSlot r s) : Equiv.sumCongr p.1 p.2 u = Equiv.sumCongr q.1 q.2 u := by
      apply τ.injective
      simpa only [assign_apply] using congrArg (fun e : A => e.val (finSumFinEquiv u)) he
    exact Prod.ext (Equiv.ext fun i => Sum.inl.inj (hh (.inl i)))
      (Equiv.ext fun j => Sum.inr.inj (hh (.inr j)))
  · intro e
    let T : Equiv.Perm (CartanSlot r s) := finSumFinEquiv.trans (e.val.trans τ.symm)
    have hT (u : CartanSlot r s) : slotSize (T u) = slotSize u := by
      rw [← hτ (T u)]
      simp only [T, Equiv.trans_apply, Equiv.apply_symm_apply]
      rw [← card_cls_fiber sz (e.val (finSumFinEquiv u)), ← e.property, cartanFiber_card]
    have hm : Set.MapsTo T (range Sum.inl) (range Sum.inl) := by
      rintro _ ⟨u, rfl⟩
      cases hTu : T (.inl u) with
      | inl i => exact ⟨i, rfl⟩
      | inr j =>
        have hs := hT (.inl u)
        rw [hTu] at hs
        cases hs
    obtain ⟨⟨π, σ⟩, hπ⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hm
    refine ⟨(π, σ), Subtype.ext (Equiv.ext fun j => ?_)⟩
    obtain ⟨u, rfl⟩ := finSumFinEquiv.surjective j
    rw [assign_apply]
    change Equiv.sumCongr π σ = T at hπ
    rw [hπ]
    simp [T]

private def assignmentEquiv : Perms ≃ A := Equiv.ofBijective _ (assign_bijective sz h τ hτ)

end Assignments

section Sum

variable {r s t : ℕ} (b : Fin t → RealBlock) (h : 2 * r + s = ∑ i, blockSizes b i)
variable (x : Coordinates r s)
local notation "Sizes" => blockSizes b

private def weightedSlot (x : Coordinates r s) (d : RealBlock) (u : CartanSlot r s) : ℂ :=
  Complex.exp ((coordinateRadius x u : ℂ) * ((d.rank : ℂ) * blockTwist d)) * slotDensity x d u

private theorem placementTerm (e : Assignment Sizes (cartanLabel h)) :
    centralRadialProduct b (matchingRadius b h x e) *
      (∫ κ, ∏ i, frameDensity b i (fixedLeftFrame Sizes (matchedOrthogonal b h x e) κ i) ∂frameMeasure Sizes) =
      ∏ u : CartanSlot r s, weightedSlot x (b (e.val (finSumFinEquiv u))) u := by
  simp_rw [realCartanPlacedWeights r s t b h x e, integral_const, probReal_univ, one_smul]
  rw [centralRadialProduct, ← Finset.prod_mul_distrib]
  let T : Fin t ≃ CartanSlot r s := e.val.symm.trans finSumFinEquiv.symm
  refine Fintype.prod_equiv T _ _ fun i => ?_
  have hi : e.val (finSumFinEquiv (T i)) = i := by simp [T]
  rw [hi]
  change Complex.exp ((Real.log (matchingRadius b h x e i) : ℂ) * _) * _ =
    Complex.exp ((coordinateRadius x (T i) : ℂ) * _) * _
  rw [matchingRadius, sourceRadius, Real.log_exp]
  rfl

/-- The placement sum is the finite Cartan window sum for any enumeration of the original blocks. -/
theorem placementSum_eq_windowSum (d : Fin r → ComplexCharacterData) (a : Fin s → RealCharacterData)
    (hp : (List.ofFn b).Perm (ofBlockData d a)) :
    placementSum b h x = cartanWindowSum (blockParameters d a) x := by
  obtain ⟨τ, hτ⟩ := exists_blockEnumeration d a b hp
  have hs (u : CartanSlot r s) : Sizes (τ u) = slotSize u := by
    change (b (τ u)).rank = _
    rw [hτ, rank_datum]
  let E := assignmentEquiv Sizes h τ hs
  calc
    _ = ∑ p : Equiv.Perm (Fin r) × Equiv.Perm (Fin s),
        ∏ u : CartanSlot r s, weightedSlot x (b ((E p).val (finSumFinEquiv u))) u := by
      unfold placementSum
      rw [← E.sum_comp]
      exact Finset.sum_congr rfl fun p _ => placementTerm b h x (E p)
    _ = _ := by
      rw [cartanWindowSum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun σ _ => ?_
      simp only [E, assignmentEquiv, Equiv.ofBijective_apply, assign_apply, hτ]
      rw [Fintype.prod_sum_type]
      congr 1
      exact Finset.prod_congr rfl fun j _ => by
        simp [weightedSlot, datum, coordinateRadius, slotDensity, blockTwist, RealBlock.rank,
          blockParameters, realTerm, MonoidHom.coe_mk, OneHom.coe_mk]

end Sum

/-- The finite sum of actual fixed flags gives the prescribed Cartan numerator after
multiplication by the common angular factor. -/
def RealCartanPlacementNumeratorStatement : Prop :=
  ∀ (r s t : ℕ) (x : Coordinates r s) (b : Fin t → RealBlock)
    (h : 2 * r + s = ∑ i, blockSizes b i) (d : Fin r → ComplexCharacterData)
    (a : Fin s → RealCharacterData), (List.ofFn b).Perm (ofBlockData d a) →
    (∀ i, 0 < (d i).weight) →
    angularProduct x * placementSum b h x = numerator (blockParameters d a) x

theorem realCartanPlacementNumerator : RealCartanPlacementNumeratorStatement := by
  intro r s t x b h d a hp hpos
  rw [placementSum_eq_windowSum b h x d a hp]
  exact angularProduct_mul_cartanWindowSum (blockParameters d a) hpos x

end Langlands.Archimedean.RealCartanPlacementNumerator
