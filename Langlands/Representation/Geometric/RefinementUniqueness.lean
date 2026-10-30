import Langlands.Representation.Geometric.RefinementDefinitions
import Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof
import Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
import Langlands.Representation.CuspidalSupport.AssociationLawsProof

/-! Actual standard Levi subgroups determine their consecutive block refinements. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CuspidalSupport

universe uF

variable {F : Type uF} [Field F] {n : ℕ}

/-- A standard consecutive block shape is determined by its actual Levi subgroup. -/
theorem blockShape_eq_of_leviSubgroup_eq {B C : BlockShape n}
    (h : B.leviSubgroup F = C.leviSubgroup F) : B = C := by
  have hw : ConjugatesLevi (F := F) B C 1 := by
    unfold ConjugatesLevi
    rw [map_one, map_conj_one]
    exact h
  have hm : StrictMono (blockMap B C 1) := by
    intro i j hij
    have hle : blockMap B C 1 i ≤ blockMap B C 1 j :=
      blockIndex_monotone C (B.index_lt_index_of_block_lt hij
        ⟨0, B.positive i⟩ ⟨0, B.positive j⟩).le
    exact lt_of_le_of_ne hle (fun he => (ne_of_lt hij) ((blockMap_bijective hw).1 he))
  let e : Fin B.length ≃o Fin C.length :=
    { toEquiv := blockEquiv hw
      map_rel_iff' := hm.le_iff_le }
  have he (i : Fin B.length) :
      blockMap B C 1 i = Fin.cast (TotalConjugatingCount.length_eq hw) i :=
    Fin.ext (Fin.coe_orderIso_apply e i)
  apply TotalConjugatingCount.shape_ext (TotalConjugatingCount.length_eq hw)
  intro i
  rw [← he i]
  exact size_blockMap hw i

/-- Equality of actual refined Levi subgroups implies equality of the refinements. -/
theorem blockRefinement_eq_of_refinedLevi_eq (B : BlockShape n)
    {S R : BlockRefinement B} (h : refinedLevi F B S = refinedLevi F B R) : S = R := by
  classical
  funext i
  apply blockShape_eq_of_leviSubgroup_eq (F := F)
  have hle (S' R' : BlockRefinement B)
      (h' : refinedLevi F B S' ≤ refinedLevi F B R') :
      (S' i).leviSubgroup F ≤ (R' i).leviSubgroup F := by
    intro g hg
    have hs : Pi.mulSingle i g ∈ refinedLevi F B S' := by
      change Pi.mulSingle i g ∈ Subgroup.pi Set.univ
        (fun j => (S' j).leviSubgroup F)
      exact (Subgroup.mulSingle_mem_pi (I := Set.univ)
        (H := fun j => (S' j).leviSubgroup F) i g).mpr (fun _ => hg)
    have hr := (mem_refinedLevi F B R' _).mp (h' hs) i
    simpa only [Pi.mulSingle_eq_same] using hr
  exact le_antisymm (hle S R h.le) (hle R S h.ge)

end Langlands.Geometric
