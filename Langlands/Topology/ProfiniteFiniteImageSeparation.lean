import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # Finite image prescription in profinite abelian groups -/

noncomputable section

universe u v

namespace Langlands.Topology

/-- A subgroup of a finite subgroup of a profinite abelian group can be cut out
by an open subgroup of the ambient group. -/
theorem exists_open_subgroup_inf_eq
    {Q : Type v} [CommGroup Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [T2Space Q] [CompactSpace Q] [TotallyDisconnectedSpace Q]
    (H D : Subgroup Q) [Finite H] (hDH : D ≤ H) :
    ∃ M : Subgroup Q, IsOpen (M : Set Q) ∧ M.FiniteIndex ∧ H ⊓ M = D := by
  classical
  have hbad : ((H : Set Q) \ (D : Set Q)).Finite := (Set.toFinite (H : Set Q)).sdiff
  have hone : (1 : Q) ∈ ((H : Set Q) \ (D : Set Q))ᶜ := by
    intro h
    exact h.2 D.one_mem
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    hbad.isClosed.isOpen_compl hone
  let M : Subgroup Q := D ⊔ W.toSubgroup
  have hM : IsOpen (M : Set Q) := Subgroup.isOpen_mono le_sup_right W.isOpen
  have hfin : Finite (Q ⧸ M) := Subgroup.quotient_finite_of_isOpen M hM
  let := hfin
  refine ⟨M, hM, Subgroup.finiteIndex_of_finite_quotient, ?_⟩
  apply le_antisymm
  · intro x hx
    obtain ⟨d, hd, w, hw, hdw⟩ := Subgroup.mem_sup_of_normal_right.mp hx.2
    have hwH : w ∈ H := by
      have hx' : d * w ∈ H := hdw.symm ▸ hx.1
      exact (H.mul_mem_cancel_left (hDH hd)).mp hx'
    have hwD : w ∈ D := by
      by_contra h
      exact hW hw ⟨hwH, h⟩
    exact hdw ▸ D.mul_mem hd hwD
  · exact le_inf hDH le_sup_left

/-- A finite-image homomorphism into a profinite abelian group admits an open
ambient subgroup with prescribed preimage, provided its kernel is contained in
that preimage. The source needs no topology. -/
theorem exists_open_subgroup_comap_eq_of_finite_range
    {A : Type u} [Group A]
    {Q : Type v} [CommGroup Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [T2Space Q] [CompactSpace Q] [TotallyDisconnectedSpace Q]
    (g : A →* Q) [Finite g.range] (U : Subgroup A) (hker : g.ker ≤ U) :
    ∃ M : Subgroup Q, IsOpen (M : Set Q) ∧ M.FiniteIndex ∧ M.comap g = U := by
  obtain ⟨M, hM, hfin, hcut⟩ :=
    exists_open_subgroup_inf_eq g.range (U.map g) (Subgroup.map_le_range _ _)
  refine ⟨M, hM, hfin, ?_⟩
  have hpre : (U.map g).comap g = U := Subgroup.comap_map_eq_self hker
  ext a
  change g a ∈ M ↔ a ∈ U
  constructor
  · intro ha
    have hx : g a ∈ g.range ⊓ M := ⟨⟨a, rfl⟩, ha⟩
    rw [hcut] at hx
    have hx' : a ∈ (U.map g).comap g := hx
    simpa only [hpre] using hx'
  · intro ha
    have hx : g a ∈ U.map g := ⟨a, ha, rfl⟩
    rw [← hcut] at hx
    exact hx.2

/-- Pull back finite-image prescription from a profinite quotient. In particular,
the resulting open finite-index subgroup contains the subgroup being divided
out. -/
theorem exists_open_subgroup_through_profinite_quotient
    {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    {C : Type v} [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    (f : A →ₜ* C) (P : Subgroup C)
    [T2Space (C ⧸ P)] [CompactSpace (C ⧸ P)] [TotallyDisconnectedSpace (C ⧸ P)]
    [Finite ((QuotientGroup.mk' P).comp f.toMonoidHom).range]
    (U : Subgroup A) (hker : P.comap f.toMonoidHom ≤ U) :
    ∃ N : Subgroup C, IsOpen (N : Set C) ∧ N.FiniteIndex ∧ P ≤ N ∧
      N.comap f.toMonoidHom = U := by
  let g : A →* C ⧸ P := (QuotientGroup.mk' P).comp f.toMonoidHom
  have hgker : g.ker ≤ U := by
    intro a ha
    apply hker
    exact (QuotientGroup.eq_one_iff (f a)).mp (MonoidHom.mem_ker.mp ha)
  obtain ⟨M, hM, hfin, hpre⟩ :=
    exists_open_subgroup_comap_eq_of_finite_range g U hgker
  let := hfin
  let N : Subgroup C := M.comap (QuotientGroup.mk' P)
  refine ⟨N, hM.preimage QuotientGroup.continuous_mk, inferInstance, ?_, ?_⟩
  · intro x hx
    change (QuotientGroup.mk x : C ⧸ P) ∈ M
    rw [(QuotientGroup.eq_one_iff x).mpr hx]
    exact M.one_mem
  · exact hpre

/-- Finite source power index, a profinite target power quotient and a power
intersection bound imply the open finite quotient needed for prescription. -/
theorem exists_open_subgroup_from_power_intersection
    {A : Type u} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    {C : Type v} [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    (f : A →ₜ* C) (m n : ℕ)
    [(powMonoidHom m : A →* A).range.FiniteIndex]
    [T2Space (C ⧸ (powMonoidHom m : C →* C).range)]
    [CompactSpace (C ⧸ (powMonoidHom m : C →* C).range)]
    [TotallyDisconnectedSpace (C ⧸ (powMonoidHom m : C →* C).range)]
    (U : Subgroup A) (hU : ∀ a : A, a ^ n ∈ U)
    (hintersection : (powMonoidHom m : C →* C).range.comap f.toMonoidHom ≤
      (powMonoidHom n : A →* A).range) :
    ∃ N : Subgroup C, IsOpen (N : Set C) ∧ N.FiniteIndex ∧
      (∀ x : C, x ^ m ∈ N) ∧ N.comap f.toMonoidHom = U := by
  let P : Subgroup C := (powMonoidHom m : C →* C).range
  let g : A →* C ⧸ P := (QuotientGroup.mk' P).comp f.toMonoidHom
  have hgker : (powMonoidHom m : A →* A).range ≤ g.ker := by
    rintro a ⟨b, rfl⟩
    change (QuotientGroup.mk (f (b ^ m)) : C ⧸ P) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨f b, (map_pow f b m).symm⟩
  let : g.ker.FiniteIndex := Subgroup.finiteIndex_of_le hgker
  let : Finite g.range := Finite.of_equiv (A ⧸ g.ker)
    (QuotientGroup.quotientKerEquivRange g).toEquiv
  have hker : P.comap f.toMonoidHom ≤ U := by
    intro a ha
    obtain ⟨b, hb⟩ := hintersection ha
    exact hb ▸ hU b
  obtain ⟨N, hN, hfin, hPN, hpre⟩ :=
    exists_open_subgroup_through_profinite_quotient f P U hker
  exact ⟨N, hN, hfin, fun x => hPN ⟨x, rfl⟩, hpre⟩

end Langlands.Topology
