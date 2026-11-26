import Langlands.BaseChange.UnramifiedWeylJacquetSupport.Characters
import Langlands.BaseChange.UnramifiedWeylJacquetSupport.Weights
import Langlands.Representation.CuspidalSupport.AssociatedProof

/-! The Borel geometric filtration counts Weyl tuples with their multiplicities. -/

noncomputable section

namespace Langlands.BaseChange.WeylJacquet

open GeneralLinear Correspondence Unramified Unramified.SphericalExistence
open CuspidalSupport Geometric CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {r : ℕ}

attribute [local instance] heckeFieldTopology heckeGeneralLinearTopology
  heckeGeneralLinearTopologicalGroup

set_option hygiene false in
local notation "B" => borelShape r
set_option hygiene false in
local notation "M" => (borelShape r).Levi F.Carrier
set_option hygiene false in
local notation "K" => borelIntegralDiagonal F r

set_option backward.isDefEq.respectTransparency false in
private theorem finrank_weight_of_character {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ M V) (e : V ≃ₗ[ℂ] ℂ) (z y : Fin (r + 1) → ℂˣ)
    (h : ∀ m v, ρ m v = (borelCharacter F z m : ℂ) • v) :
    Module.finrank ℂ (torusWeightSpace F ρ y) = if y = z then 1 else 0 := by
  classical
  have hfixed : fixedVectors ρ K = ⊤ := by
    refine eq_top_iff.mpr fun v _ k => ?_
    change ρ k.val v = v
    rw [h, borelCharacter_eq_one_of_mem_integral F z k.property, Units.val_one, one_smul]
  have hscalar (i : Fin (r + 1)) : torusUniformizerAction F ρ i = (z i : ℂ) • 1 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ρ (borelUniformizerLevi F r i) v.val = (z i : ℂ) • v.val
    rw [h, borelCharacter_uniformizer]
  by_cases hy : y = z
  · subst y
    have htop : torusWeightSpace F ρ z = ⊤ := by
      refine eq_top_iff.mpr fun v _ => ?_
      change v ∈ ⨅ i, (torusUniformizerAction F ρ i).maxGenEigenspace (z i : ℂ)
      rw [Submodule.mem_iInf]
      intro i
      rw [hscalar, Module.End.mem_maxGenEigenspace]
      exact ⟨1, by simp⟩
    rw [htop, finrank_top, hfixed, finrank_top, e.finrank_eq, Module.finrank_self]
    simp
  · have hbot : torusWeightSpace F ρ y = ⊥ := by
      obtain ⟨i, hi⟩ : ∃ i, y i ≠ z i := by
        by_contra! hall
        exact hy (funext hall)
      have hn : (z i : ℂ) - (y i : ℂ) ≠ 0 :=
        sub_ne_zero.mpr (fun h' => hi (Units.ext h'.symm))
      refine eq_bot_iff.mpr fun v hv => ?_
      rw [Submodule.mem_bot]
      have hvi : v ∈ (torusUniformizerAction F ρ i).maxGenEigenspace (y i : ℂ) :=
        iInf_le (fun i => (torusUniformizerAction F ρ i).maxGenEigenspace (y i : ℂ)) i hv
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hvi
      let I : Module.End ℂ (fixedVectors ρ K) := 1
      have hshift : (z i : ℂ) • I - (y i : ℂ) • I = ((z i : ℂ) - (y i : ℂ)) • I :=
        (sub_smul _ _ _).symm
      change ((torusUniformizerAction F ρ i - (y i : ℂ) • I) ^ k) v = 0 at hk
      rw [hscalar i, show (1 : Module.End ℂ (fixedVectors ρ K)) = I from rfl, hshift] at hk
      dsimp only [I] at hk
      rw [smul_pow, one_pow, LinearMap.smul_apply, Module.End.one_apply] at hk
      exact (smul_eq_zero.mp hk).resolve_left (pow_ne_zero k hn)
    simp only [hy, ite_false]
    exact (congrArg (fun S : Submodule ℂ (fixedVectors ρ K) => Module.finrank ℂ S) hbot).trans
      (finrank_bot ℂ _)

private theorem finrank_weight_eq_sum {A : Rep.{uV} ℂ M} (hA : IsAdmissible A.ρ)
    {m : ℕ} (s : ObjectRepFiltration A m) (y : Fin (r + 1) → ℂˣ) :
    Module.finrank ℂ (torusWeightSpace F A.ρ y) =
      ∑ i : Fin m, Module.finrank ℂ (torusWeightSpace F (s.gradedRepresentation i).ρ y) := by
  classical
  let d : Fin (m + 1) → ℕ := fun i =>
    Module.finrank ℂ (torusWeightSpace F (s.subrepresentation i).toRepresentation y)
  have hz : d 0 = 0 := by
    dsimp only [d]
    rw [s.subrepresentation_zero]
    let : Subsingleton (⊥ : Subrepresentation A.ρ).toSubmodule :=
      inferInstanceAs (Subsingleton (⊥ : Submodule ℂ A))
    exact Module.finrank_zero_of_subsingleton
  have ht : d (Fin.last m) = Module.finrank ℂ (torusWeightSpace F A.ρ y) := by
    dsimp only [d]
    rw [s.subrepresentation_last]
    let e : (⊤ : Subrepresentation A.ρ).toRepresentation.Equiv A.ρ :=
      Representation.Equiv.mk Submodule.topEquiv (fun _ => rfl)
    exact finrank_torusWeightSpace_equiv F e y
  have hstep (i : Fin m) : d i.succ =
      d i.castSucc + Module.finrank ℂ (torusWeightSpace F (s.gradedRepresentation i).ρ y) := by
    let C := s.subrepresentation i.castSucc
    let D := s.subrepresentation i.succ
    have hCD : C ≤ D := s.monotone_subrepresentation (Nat.le_succ i.val)
    let f : C.toRepresentation.IntertwiningMap D.toRepresentation :=
      ⟨Submodule.inclusion hCD, fun _ => rfl⟩
    let q := (s.gradedProjection i).hom
    let L := (s.step i.castSucc).lowerInUpper (s.step i.succ) (Discrete.mk PUnit.unit)
    have hex : LinearMap.range f.toLinearMap = LinearMap.ker q.toLinearMap := by
      apply Submodule.ext
      intro v
      rw [LinearMap.mem_range, LinearMap.mem_ker]
      change (∃ w : C.toSubmodule, Submodule.inclusion hCD w = v) ↔
        (Submodule.Quotient.mk v : _ ⧸ L.toSubmodule) = 0
      exact ⟨fun ⟨w, hw⟩ => (Submodule.Quotient.mk_eq_zero L.toSubmodule).mpr (hw ▸ w.property),
        fun hv => ⟨⟨v.val, (Submodule.Quotient.mk_eq_zero L.toSubmodule).mp hv⟩, rfl⟩⟩
    let j : D.toRepresentation.IntertwiningMap A.ρ := ⟨D.toSubmodule.subtype, fun _ => rfl⟩
    have hD : IsAdmissible D.toRepresentation := isAdmissible_of_injective j Subtype.val_injective hA
    let : FiniteDimensional ℂ (fixedVectors D.toRepresentation K) := hD.2 (borelIntegralDiagonalOpen F r)
    exact finrank_torusWeightSpace_exact F hD.1 f q (Submodule.inclusion_injective hCD)
      (s.gradedProjection_surjective i) hex y
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hstep i)
  rw [Finset.sum_add_distrib] at hs
  have hc := (Fin.sum_univ_succ d).symm.trans (Fin.sum_univ_castSucc d)
  omega

set_option maxHeartbeats 1000000 in
/-- The Weyl multiset records every permutation, including every permutation that gives
 an already occurring tuple. -/
theorem principalSeries_borelJacquetMultiset (z : Fin (r + 1) → ℂˣ) :
    borelJacquetMultiset F (principalSeriesOfTuple F z) = weylTupleMultiset z := by
  classical
  let T := F.canonicalTopologicalData
  let := T.leviTopologicalGroup B
  let σ := (B).blockTensor (blockCharacters F z)
  let A : SmoothRep.{0, uF, 0} ℂ M := SmoothRep.of σ
    (FiniteTensor.isAdmissible_external _ (blockCharacters_isAdmissible F z)).1
  have ha : LevisAssociated (F := F.Carrier) B B :=
    ⟨1, singleton_conjugatesLevi F 1⟩
  obtain ⟨_, m, e, s, hs⟩ := associatedJacquetFiltration.{uF, 0} F T (r + 1)
    B B A (singleton_isLeviQuasicuspidal F σ) ha
  let perm : MinimalConjugatingPermutations (F := F.Carrier) B B ≃ Equiv.Perm (Fin (r + 1)) :=
    { toFun := fun w => w.val.val
      invFun := fun w => ⟨⟨w, singleton_minimal w⟩, singleton_conjugatesLevi F w⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ => rfl }
  let enum : Fin m ≃ Equiv.Perm (Fin (r + 1)) := e.trans (perm.trans (Equiv.inv _))
  let J := (T.normalizedJacquetFunctor B).obj ((T.normalizedParabolicInductionFunctor B).obj A)
  have hJ : IsAdmissible J.representation :=
    Parabolic.isAdmissible_normalizedJacquet F T B (principalSeriesOfTuple F z)
    (principalSeriesOfTuple_isAdmissible F z)
  apply Multiset.ext.mpr
  intro y
  rw [count_borelJacquetMultiset_principalSeriesOfTuple]
  change Module.finrank ℂ (torusWeightSpace F J.representation y) = _
  have he (i : Fin m) : Module.finrank ℂ (torusWeightSpace F (s.gradedRepresentation i).ρ y) =
      if y = z ∘ enum i then 1 else 0 := by
    obtain ⟨f⟩ := hs i
    refine (finrank_torusWeightSpace_equiv F f y).trans ?_
    exact finrank_weight_of_character F _ (PiTensorProduct.constantBaseRingEquiv (Fin (B).length) ℂ)
      (z ∘ enum i) y (transport_blockTensor_eq_smul F z (perm (e i)))
  calc
    _ = ∑ i : Fin m, Module.finrank ℂ (torusWeightSpace F (s.gradedRepresentation i).ρ y) :=
      finrank_weight_eq_sum (A := Rep.of J.representation) F hJ s y
    _ = ∑ i : Fin m, (if y = z ∘ enum i then 1 else 0 : ℕ) :=
      Finset.sum_congr rfl (fun i _ => he i)
    _ = ∑ w : Equiv.Perm (Fin (r + 1)), (if y = z ∘ w then 1 else 0 : ℕ) :=
      Fintype.sum_equiv enum _ _ (fun _ => rfl)
    _ = (weylTupleMultiset z).count y := by
      rw [Finset.sum_boole, weylTupleMultiset, Multiset.count_map, ← Finset.filter_val]
      rfl

/-- Reindexing the inducing tuple preserves the full Weyl multiset. -/
theorem weylTupleMultiset_reindex {n : ℕ} (z : Fin n → ℂˣ) (e : Equiv.Perm (Fin n)) :
    weylTupleMultiset (z ∘ e) = weylTupleMultiset z := by
  classical
  unfold weylTupleMultiset
  rw [show (fun w : Equiv.Perm (Fin n) => (z ∘ e) ∘ w) =
    (fun w : Equiv.Perm (Fin n) => z ∘ w) ∘ Equiv.mulLeft e from rfl,
    ← Multiset.map_map, Multiset.map_univ_val_equiv]

end Langlands.BaseChange.WeylJacquet
