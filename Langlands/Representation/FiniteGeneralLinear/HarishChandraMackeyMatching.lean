import Langlands.Representation.FiniteGeneralLinear.HarishChandraMackeyVanishing
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Group.GL.RankReindex

/-! The cuspidal factors attached to surviving Mackey terms. -/

noncomputable section

open Module Representation
open scoped BigOperators

namespace Langlands.FiniteGeneralLinear

open FiniteRep GeneralLinear Geometric CuspidalSupport

/-- A cuspidal class with its positive rank. -/
abbrev PositiveCuspidalLabel (k : Type*) [Field k] :=
  Σ d : {d : ℕ // 0 < d}, CuspidalModelClass d.val k

/-- The weight of a cuspidal label is its rank. -/
def cuspidalLabelRank {k : Type*} [Field k] (a : PositiveCuspidalLabel k) : ℕ := a.1.val

variable {k : Type*} [Field k] {n : ℕ}

/-- The positive-rank class of a single Levi factor. -/
def HarishChandraDatum.blockLabel (D : HarishChandraDatum n k) (i : Fin D.shape.length) :
    PositiveCuspidalLabel k := ⟨⟨D.shape.size i, D.shape.positive i⟩, D.label i⟩

/-- The unordered cuspidal factors, with multiplicity. -/
def HarishChandraDatum.labels (D : HarishChandraDatum n k) : Multiset (PositiveCuspidalLabel k) :=
  (Finset.univ : Finset (Fin D.shape.length)).val.map D.blockLabel

/-- The weights of the cuspidal factors sum to the rank. -/
theorem HarishChandraDatum.sum_labelRanks (D : HarishChandraDatum n k) :
    (D.labels.map cuspidalLabelRank).sum = n := by
  rw [HarishChandraDatum.labels, Multiset.map_map]
  exact D.shape.sum_eq

private theorem cardIndex_of_label_eq {r s : {d : ℕ // 0 < d}}
    (h : r.val = s.val) (a : CuspidalModelClass r.val k) (b : CuspidalModelClass s.val k) :
    (⟨r, a⟩ : PositiveCuspidalLabel k) = ⟨s, b⟩ ↔
      Nonempty (Representation.Equiv (VirtualCharacter.rep a.val).ρ
        (pullbackRep (reindex (R := k) (finCongr h)).toMonoidHom (VirtualCharacter.rep b.val)).ρ) := by
  obtain rfl : r = s := Subtype.ext h
  have hr : h = rfl := Subsingleton.elim _ _
  rw [hr, reindex_finCongr_rfl]
  change (⟨r, a⟩ : PositiveCuspidalLabel k) = ⟨r, b⟩ ↔
    Nonempty (Representation.Equiv (VirtualCharacter.rep a.val).ρ (VirtualCharacter.rep b.val).ρ)
  simp only [Sigma.mk.injEq, heq_iff_eq, true_and]
  have ha : a = b ↔ a.val.val = b.val.val :=
    ⟨fun e => congrArg (fun x : CuspidalModelClass r.val k => x.val.val) e,
      fun e => Subtype.ext (Subtype.ext e)⟩
  rw [ha, ← VirtualCharacter.classOf_rep a.val, ← VirtualCharacter.classOf_rep b.val, classOf_eq_iff]
  exact ⟨fun ⟨e⟩ => ⟨FiniteRep.equivOfIso e⟩, fun ⟨e⟩ => ⟨FiniteRep.isoOfEquiv e⟩⟩

section Match

variable {B C : BlockShape n} (w : MinimalRepresentatives B C)
    (hW : ConjugatesLevi (F := k) B C w.val)

private theorem inverse_index (i : Fin B.length) (a : Fin (C.size (blockMap B C w.val i))) :
    w.val⁻¹ (C.index (blockMap B C w.val i) a) =
      B.index i (Fin.cast (size_blockMap hW i).symm a) := by
  apply w.val.injective
  rw [Equiv.Perm.coe_inv, Equiv.apply_symm_apply, apply_index_eq w.property hW]
  simp

private theorem leviConjugation_block (m : B.Levi k) (i : Fin B.length) :
    leviConjugation B C w.val hW m (blockMap B C w.val i) =
      reindex (R := k) (finCongr (size_blockMap hW i)) (m i) := by
  apply Units.ext
  ext a b
  rw [reindex_finCongr_apply, ← C.leviEmbedding_apply_same k, leviConjugation_embedding,
    permutation_conjugate_entry, inverse_index w hW, inverse_index w hW, B.leviEmbedding_apply_same]

private theorem leviProjection_conj (p : B.parabolic k) (q : C.parabolic k)
    (hq : q.val = permutation n k w.val * p.val * (permutation n k w.val)⁻¹) :
    C.leviProjection k q = leviConjugation B C w.val hW (B.leviProjection k p) := by
  funext j
  obtain ⟨i, rfl⟩ := (blockMap_bijective hW).2 j
  rw [leviConjugation_block w hW]
  apply Units.ext
  ext a b
  rw [reindex_finCongr_apply, C.leviProjection_apply, B.leviProjection_apply, hq,
    permutation_conjugate_entry, inverse_index w hW, inverse_index w hW]

end Match

section Dimension

variable [Finite k]

private def mackeyLeviEquiv (D E : HarishChandraDatum n k)
    (w : MinimalRepresentatives D.shape E.shape) (hW : ConjugatesLevi (F := k) D.shape E.shape w.val) :
    MackeyIntertwining (E.shape.parabolic k) (D.shape.parabolic k)
      (pullbackRep (D.shape.leviProjection k) D.leviRep)
      (pullbackRep (E.shape.leviProjection k) E.leviRep) (permutation n k w.val)⁻¹ ≃ₗ[ℂ]
    IntertwiningMap D.leviRep.ρ
      (E.leviRep.ρ.comp (leviConjugation D.shape E.shape w.val hW).toMonoidHom) := by
  let B := D.shape
  let C := E.shape
  let P := C.parabolic k
  let Q := B.parabolic k
  let r := (permutation n k w.val)⁻¹
  let S := orbitStabilizer P Q r
  let e := leviConjugation B C w.val hW
  have hproj (q : S) : C.leviProjection k (stabilizerToInducing P Q r q) =
      e (B.leviProjection k q.val) := by
    apply leviProjection_conj w hW
    rw [stabilizerToInducing_apply]
    change r⁻¹ * q.val.val * r = _
    rw [inv_inv]
  let s (m : B.Levi k) : S := ⟨B.leviInParabolic k m, by
    change (MulAut.conj r⁻¹) (B.leviEmbedding k m) ∈ P
    rw [inv_inv, MulAut.conj_apply, ← leviConjugation_embedding B C w.val hW m]
    exact (C.leviInParabolic k (e m)).property⟩
  refine
    { toFun := fun T => ⟨T.toLinearMap, fun m => ?_⟩
      invFun := fun T => ⟨T.toLinearMap, fun q => ?_⟩
      left_inv := fun _ => IntertwiningMap.ext rfl
      right_inv := fun _ => IntertwiningMap.ext rfl
      map_add' := fun _ _ => IntertwiningMap.ext rfl
      map_smul' := fun _ _ => IntertwiningMap.ext rfl }
  · apply LinearMap.ext
    intro v
    have h := IntertwiningMap.isIntertwining _ _ T (s m) v
    change T (D.leviRep.ρ (B.leviProjection k (B.leviInParabolic k m)) v) =
      E.leviRep.ρ (C.leviProjection k (stabilizerToInducing P Q r (s m))) (T v) at h
    rw [hproj, show (s m).val = B.leviInParabolic k m from rfl,
      BlockShape.leviProjection_section] at h
    change T (D.leviRep.ρ m v) = E.leviRep.ρ (e m) (T v)
    exact h
  · apply LinearMap.ext
    intro v
    change T (D.leviRep.ρ (B.leviProjection k q.val) v) =
      E.leviRep.ρ (C.leviProjection k (stabilizerToInducing P Q r q)) (T v)
    rw [hproj]
    exact IntertwiningMap.isIntertwining _ _ T (B.leviProjection k q.val) v

open Classical in
/-- At a conjugating minimal representative the term is one if all block labels match and
zero if some corresponding block representations differ. -/
theorem harishChandraMackeyTerm_eq_ite (D E : HarishChandraDatum n k)
    (w : MinimalRepresentatives D.shape E.shape) (hW : ConjugatesLevi (F := k) D.shape E.shape w.val) :
    harishChandraMackeyTerm D E w =
      if ∀ i, D.blockLabel i = E.blockLabel (blockEquiv hW i) then 1 else 0 := by
  classical
  let B := D.shape
  let C := E.shape
  let e := leviConjugation B C w.val hW
  let V (i : Fin B.length) := VirtualCharacter.rep (D.label i).val
  let W (i : Fin B.length) : FDRep ℂ (GeneralLinear (B.size i) k) :=
    pullbackRep (reindex (R := k) (finCongr (size_blockMap hW i))).toMonoidHom
      (VirtualCharacter.rep (E.label (blockEquiv hW i)).val)
  let : Fintype (B.Levi k) := Fintype.ofFinite _
  let : ∀ i : Fin B.length, Fintype (GeneralLinear (B.size i) k) := fun _ => Fintype.ofFinite _
  have hChar (m : B.Levi k) : E.leviRep.character (e m) = (externalRep W).character m := by
    change (externalRep (fun j => VirtualCharacter.rep (E.label j).val)).character (e m) = _
    rw [character_externalRep, character_externalRep]
    calc
      _ = ∏ i : Fin B.length, (VirtualCharacter.rep (E.label (blockEquiv hW i)).val).character
          (e m (blockEquiv hW i)) := (Equiv.prod_comp (blockEquiv hW) _).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        change _ = (pullbackRep (reindex (R := k) (finCongr (size_blockMap hW i))).toMonoidHom
          (VirtualCharacter.rep (E.label (blockEquiv hW i)).val)).character (m i)
        rw [character_pullbackRep]
        exact congrArg _ (leviConjugation_block w hW m i)
  have hDim : finrank ℂ (IntertwiningMap D.leviRep.ρ (E.leviRep.ρ.comp e.toMonoidHom)) =
      finrank ℂ (IntertwiningMap (externalRep V).ρ (externalRep W).ρ) := by
    apply Nat.cast_injective (R := ℂ)
    rw [← FiniteCharacter.card_inv_mul_sum_eq_finrank, ← FiniteCharacter.card_inv_mul_sum_eq_finrank]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    exact congrArg (fun z => D.leviRep.character m⁻¹ * z) (hChar m)
  change finrank ℂ (MackeyIntertwining (C.parabolic k) (B.parabolic k)
    (pullbackRep (B.leviProjection k) D.leviRep) (pullbackRep (C.leviProjection k) E.leviRep)
    (permutation n k w.val)⁻¹) = _
  rw [(mackeyLeviEquiv D E w hW).finrank_eq, hDim, finrank_intertwiningMap_externalRep]
  have hlocal (i : Fin B.length) : finrank ℂ (IntertwiningMap (V i).ρ (W i).ρ) =
      if D.blockLabel i = E.blockLabel (blockEquiv hW i) then 1 else 0 := by
    have hV : IsIrreducible (V i).ρ := VirtualCharacter.isIrreducible_rep _
    have hU := VirtualCharacter.isIrreducible_rep (E.label (blockEquiv hW i)).val
    have hW' : IsIrreducible (W i).ρ := (isIrreducible_comp_mulEquiv_iff _ _).mpr hU
    have hor := FiniteCharacter.orthogonality (V i).ρ (W i).ρ hV hW'
    have he := cardIndex_of_label_eq
      (r := ⟨B.size i, B.positive i⟩)
      (s := ⟨C.size (blockEquiv hW i), C.positive (blockEquiv hW i)⟩)
      (size_blockMap hW i) (D.label i) (E.label (blockEquiv hW i))
    apply Nat.cast_injective (R := ℂ)
    rw [← FiniteCharacter.card_inv_mul_sum_eq_finrank]
    split_ifs with h
    · exact (hor.1 (he.mp h)).trans Nat.cast_one.symm
    · exact (hor.2 (fun hn => h (he.mpr hn))).trans Nat.cast_zero.symm
  simp_rw [hlocal]
  split_ifs with h
  · exact Finset.prod_eq_one (fun i _ => ite_eq_left (h i))
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

end Dimension

end Langlands.FiniteGeneralLinear
