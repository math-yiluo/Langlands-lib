import Langlands.Representation.FiniteGeneralLinear.HarishChandraSupport
import Langlands.Representation.Geometric.StandardIntersectionsProof
import Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof

/-! Nonzero cuspidal Mackey terms conjugate the two Levi subgroups. -/

noncomputable section

open Module Representation
open scoped BigOperators TensorProduct

namespace Langlands.FiniteGeneralLinear

open FiniteRep GeneralLinear Geometric CuspidalSupport

variable {k : Type*} [Field k] [Finite k] {n : ℕ}

/-- The intertwining dimension for the two cuspidal data on one parabolic double coset. -/
def harishChandraMackeyTerm (D E : HarishChandraDatum n k)
    (w : MinimalRepresentatives D.shape E.shape) : ℕ :=
  mackeyTerm (E.shape.parabolic k) (D.shape.parabolic k)
    (pullbackRep (D.shape.leviProjection k) D.leviRep)
    (pullbackRep (E.shape.leviProjection k) E.leviRep)
    (permutation n k w.val)⁻¹

omit [Finite k] in
private theorem cuspidal_radical_sum_eq_zero (V : FDRep ℂ (GeneralLinear n k))
    (hV : IsCuspidal V.ρ) (B : BlockShape n) (hB : B.parabolic k ≠ ⊤)
    [Fintype (B.unipotentSubgroup k)] (v : V) :
    ∑ g : B.unipotentSubgroup k, V.ρ g.val v = 0 := by
  apply hV B hB
  intro g hg
  rw [map_sum]
  simp_rw [← Module.End.mul_apply, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : B.unipotentSubgroup k)) _ _ fun _ => rfl

omit [Finite k] in
private theorem leviRep_radical_sum_eq_zero (D : HarishChandraDatum n k)
    (i : Fin D.shape.length) (C : BlockShape (D.shape.size i)) (hC : C.parabolic k ≠ ⊤)
    [Fintype (C.unipotentSubgroup k)] (v : D.leviRep) :
    ∑ g : C.unipotentSubgroup k, D.leviRep.ρ (Pi.mulSingle i g.val) v = 0 := by
  classical
  let V (j : Fin D.shape.length) := VirtualCharacter.rep (D.label j).val
  let ρ := FiniteTensor.external (fun j => (V j).ρ)
  let A : Module.End ℂ _ := ∑ g : C.unipotentSubgroup k, ρ (Pi.mulSingle i g.val)
  have hA : A = 0 := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change A (PiTensorProduct.tprod ℂ x) = 0
    change (∑ g : C.unipotentSubgroup k, ρ (Pi.mulSingle i g.val))
      (PiTensorProduct.tprod ℂ x) = 0
    rw [LinearMap.sum_apply]
    have he (g : C.unipotentSubgroup k) :
        ρ (Pi.mulSingle i g.val) (PiTensorProduct.tprod ℂ x) =
          PiTensorProduct.tprod ℂ (Function.update x i ((V i).ρ g.val (x i))) := by
      rw [FiniteTensor.external_tprod]
      apply congrArg (PiTensorProduct.tprod ℂ)
      funext j
      by_cases hj : j = i
      · subst j
        rw [Pi.mulSingle_eq_same, Function.update_self]
      · rw [Pi.mulSingle_eq_of_ne hj, Function.update_of_ne hj, map_one, Module.End.one_apply]
    simp_rw [he]
    rw [← (PiTensorProduct.tprod ℂ).map_update_sum,
      cuspidal_radical_sum_eq_zero (V i) (D.label i).property C hC,
      (PiTensorProduct.tprod ℂ).map_update_zero]
  let v' : ⨂[ℂ] j, V j := v
  change (∑ g : C.unipotentSubgroup k, ρ (Pi.mulSingle i g.val) v') = 0
  rw [← LinearMap.sum_apply]
  change A v' = 0
  rw [hA, LinearMap.zero_apply]

/-- A surviving source term has its whole Levi mapped into the target Levi. -/
theorem sourceLevi_eq_top_of_mackeyTerm_ne_zero (D E : HarishChandraDatum n k)
    (w : MinimalRepresentatives D.shape E.shape) (h : harishChandraMackeyTerm D E w ≠ 0) :
    sourceLevi k D.shape E.shape w.val = ⊤ := by
  classical
  let B := D.shape
  let C := E.shape
  let P := C.parabolic k
  let Q := B.parabolic k
  let r := (permutation n k w.val)⁻¹
  let I := orbitStabilizer P Q r
  let V := pullbackRep (B.leviProjection k) D.leviRep
  let W := pullbackRep (C.leviProjection k) E.leviRep
  change finrank ℂ (MackeyIntertwining P Q V W r) ≠ 0 at h
  obtain ⟨T, hT⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (Nat.pos_of_ne_zero h)
  have hTInv (m : B.Levi k) (hm : m ∈ sourceUnipotent k B C w.val) (v : V) :
      T (D.leviRep.ρ m v) = T v := by
    let p : Q := B.leviInParabolic k m
    have hu : conjugatedLeviMap k B w.val m ∈ C.unipotentSubgroup k := hm
    obtain ⟨hpar, hdiag⟩ := (C.mem_unipotentSubgroup_iff k _).mp hu
    let q : I := ⟨p, by
      change (MulAut.conj r⁻¹) p.val ∈ P
      rwa [inv_inv]⟩
    let a := stabilizerToInducing P Q r q
    have ha : a.val = conjugatedLeviMap k B w.val m := by
      rw [stabilizerToInducing_apply]
      change r⁻¹ * (B.leviEmbedding k m) * r = _
      rw [inv_inv]
      rfl
    have ha₀ : C.leviProjection k a = 1 := by
      apply (C.mem_unipotentRadical_iff k a).mpr
      rw [ha]
      exact hdiag
    have he := IntertwiningMap.isIntertwining _ _ T q v
    change T (D.leviRep.ρ (B.leviProjection k p) v) =
      E.leviRep.ρ (C.leviProjection k a) (T v) at he
    rw [BlockShape.leviProjection_section, ha₀, map_one] at he
    exact he
  have hex (i : Fin B.length) := monotoneBlockShape (B.size i) C.length
    (fun a => blockIndex C (w.val (B.index i a)))
    ((blockIndex_monotone C).comp (w.property.1 i).monotone)
  choose S hS using hex
  obtain ⟨_, hLev, hUnip⟩ := standardIntersections_of_comparisons k B C w.val S hS
  have hS_top (i : Fin B.length) : (S i).parabolic k = ⊤ := by
    by_contra hSi
    let H := (S i).unipotentSubgroup k
    let : Fintype H := Fintype.ofFinite H
    have hmul (u : H) : Pi.mulSingle i u.val ∈ sourceUnipotent k B C w.val := by
      rw [hUnip, mem_refinedUnipotent]
      intro j
      by_cases hj : j = i
      · subst j
        simpa only [Pi.mulSingle_eq_same] using u.property
      · rw [Pi.mulSingle_eq_of_ne hj]
        exact Subgroup.one_mem _
    apply hT
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change T x = 0
    let x' : D.leviRep := x
    let action (g : H) : V := D.leviRep.ρ (Pi.mulSingle i g.val) x'
    let F : V →ₗ[ℂ] W := T.toLinearMap
    have hz : (∑ g : H, action g) = 0 := leviRep_radical_sum_eq_zero D i (S i) hSi x'
    have he := congrArg F hz
    rw [map_sum, map_zero] at he
    have hsum : (∑ g : H, F (action g)) =
        Fintype.card H • T x := calc
      _ = ∑ _g : H, T x := Finset.sum_congr rfl (fun u _ => hTInv _ (hmul u) x)
      _ = _ := by simp
    rw [hsum] at he
    have hc : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact (smul_eq_zero.mp (by simpa only [Nat.cast_smul_eq_nsmul] using he)).resolve_left hc
  rw [hLev, refinedLevi]
  have hAll (i : Fin B.length) : (S i).leviSubgroup k = ⊤ := by
    let : Subsingleton (Fin (S i).length) :=
      block_indices_subsingleton_of_parabolic_eq_top (S i) (hS_top i)
    rw [eq_top_iff]
    intro g _
    rw [levi_mem_iff]
    intro a b hab
    exact (hab (Subsingleton.elim _ _)).elim
  simp only [hAll, Subgroup.pi_top]

private def swapStabilizer {G : Type*} [Group G] (P Q : Subgroup G) (r : G) :
    orbitStabilizer P Q r ≃* orbitStabilizer Q P r⁻¹ where
  toFun q := ⟨stabilizerToInducing P Q r q, by
    change (MulAut.conj r⁻¹⁻¹) (stabilizerToInducing P Q r q).val ∈ Q
    rw [inv_inv, MulAut.conj_apply, stabilizerToInducing_apply]
    simp [mul_assoc, q.val.property]⟩
  invFun p := ⟨stabilizerToInducing Q P r⁻¹ p, by
    change (MulAut.conj r⁻¹) (stabilizerToInducing Q P r⁻¹ p).val ∈ P
    rw [MulAut.conj_apply, stabilizerToInducing_apply]
    simp [mul_assoc, p.val.property]⟩
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    change (stabilizerToInducing Q P r⁻¹ _).val = q.val.val
    simp [stabilizerToInducing_apply, mul_assoc]
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    change (stabilizerToInducing P Q r _).val = p.val.val
    simp [stabilizerToInducing_apply, mul_assoc]
  map_mul' q t := Subtype.ext (map_mul (stabilizerToInducing P Q r) q t)

private theorem mackeyTerm_swap {G : Type*} [Group G] [Finite G] (P Q : Subgroup G)
    (V : FDRep ℂ Q) (W : FDRep ℂ P) (r : G) :
    mackeyTerm P Q V W r = mackeyTerm Q P W V r⁻¹ := by
  let e := swapStabilizer P Q r
  let : Fintype (orbitStabilizer P Q r) := Fintype.ofFinite _
  let : Fintype (orbitStabilizer Q P r⁻¹) := Fintype.ofFinite _
  apply Nat.cast_injective (R := ℂ)
  unfold mackeyTerm MackeyIntertwining
  rw [← FiniteCharacter.card_inv_mul_sum_eq_finrank, ← FiniteCharacter.card_inv_mul_sum_eq_finrank,
    Fintype.card_congr e.toEquiv]
  congr 1
  apply Fintype.sum_equiv (e.toEquiv.trans (Equiv.inv _))
  intro s
  change V.character s⁻¹.val * W.character (stabilizerToInducing P Q r s) =
    W.character (((e s)⁻¹)⁻¹).val * V.character (stabilizerToInducing Q P r⁻¹ (e s)⁻¹)
  rw [inv_inv, map_inv]
  have he : stabilizerToInducing Q P r⁻¹ (e s) = s.val := by
    apply Subtype.ext
    simp [e, swapStabilizer, stabilizerToInducing_apply, mul_assoc]
  rw [he]
  exact mul_comm _ _

/-- Every surviving term in the parabolic Mackey sum conjugates the source Levi onto the target. -/
theorem conjugatesLevi_of_mackeyTerm_ne_zero (D E : HarishChandraDatum n k)
    (w : MinimalRepresentatives D.shape E.shape) (h : harishChandraMackeyTerm D E w ≠ 0) :
    ConjugatesLevi (F := k) D.shape E.shape w.val := by
  let B := D.shape
  let C := E.shape
  let w' : MinimalRepresentatives C B := ⟨w.val⁻¹, w.property.2, w.property.1⟩
  have hswap : harishChandraMackeyTerm E D w' ≠ 0 := by
    have hE := mackeyTerm_swap (C.parabolic k) (B.parabolic k)
      (pullbackRep (B.leviProjection k) D.leviRep)
      (pullbackRep (C.leviProjection k) E.leviRep) (permutation n k w.val)⁻¹
    have hr : ((permutation n k w.val)⁻¹)⁻¹ = (permutation n k w'.val)⁻¹ := by
      change ((permutation n k w.val)⁻¹)⁻¹ = (permutation n k w.val⁻¹)⁻¹
      rw [permutation_inv]
    rw [hr] at hE
    exact fun hh => h (hE.trans hh)
  have hB := sourceLevi_eq_top_of_mackeyTerm_ne_zero D E w h
  have hC := sourceLevi_eq_top_of_mackeyTerm_ne_zero E D w' hswap
  refine le_antisymm ?_ ?_
  · rintro x ⟨_, ⟨m, rfl⟩, rfl⟩
    have hm : m ∈ sourceLevi k B C w.val := hB ▸ Subgroup.mem_top m
    exact hm
  · rintro _ ⟨m, rfl⟩
    have hm : m ∈ sourceLevi k C B w'.val := hC ▸ Subgroup.mem_top m
    change conjugatedLeviMap k C w'.val m ∈ B.leviSubgroup k at hm
    refine ⟨conjugatedLeviMap k C w'.val m, hm, ?_⟩
    change (MulAut.conj (permutation n k w.val))
      ((MulAut.conj (permutation n k w.val⁻¹)) (C.leviEmbedding k m)) = C.leviEmbedding k m
    rw [← permutation_inv, MulAut.conj_apply, MulAut.conj_apply]
    group

end Langlands.FiniteGeneralLinear
