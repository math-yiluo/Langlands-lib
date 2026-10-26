import Langlands.Representation.Exponents.BlockParameterPermutationRigidityStatement

/-!
# Rigidity of strictly decreasing block parameters

An elementary proof by matching parameter values and counting actual coordinate
fibers. No representation-theoretic comparison is used.
-/

namespace Langlands.Exponents

open GeneralLinear Geometric

/-- Repeated strictly decreasing parameters determine the ordered block sizes
and values, even when the repeated coordinates are matched by an arbitrary
permutation. -/
theorem blockParameterPermutationRigidity :
    BlockParameterPermutationRigidityStatement := by
  intro n B C t s ht hs ⟨w, hw⟩
  let f : Fin B.length → Fin C.length :=
    fun i => blockIndex C (w (B.index i ⟨0, B.positive i⟩))
  have hf (i : Fin B.length) : t i = s (f i) := by
    simpa only [f, blockIndex_index] using hw (B.index i ⟨0, B.positive i⟩)
  let g : Fin C.length → Fin B.length :=
    fun j => blockIndex B (w.symm (C.index j ⟨0, C.positive j⟩))
  have hg (j : Fin C.length) : s j = t (g j) := by
    simpa only [g, Equiv.apply_symm_apply, blockIndex_index] using
      (hw (w.symm (C.index j ⟨0, C.positive j⟩))).symm
  have hgf (i : Fin B.length) : g (f i) = i :=
    ht.injective ((hg (f i)).symm.trans (hf i).symm)
  have hfg (j : Fin C.length) : f (g j) = j :=
    hs.injective ((hf (g j)).symm.trans (hg j).symm)
  let e : Fin B.length ≃ Fin C.length :=
    { toFun := f
      invFun := g
      left_inv := hgf
      right_inv := hfg }
  let b : Fin B.length ≃o Fin C.length :=
    { toEquiv := e
      map_rel_iff' := by
        intro i j
        change f i ≤ f j ↔ i ≤ j
        calc
          f i ≤ f j ↔ s (f j) ≤ s (f i) := hs.le_iff_ge.symm
          _ ↔ t j ≤ t i := by rw [hf i, hf j]
          _ ↔ i ≤ j := ht.le_iff_ge }
  refine ⟨b, fun i => ⟨?_, hf i⟩⟩
  change B.size i = C.size (f i)
  have hcoord (a : Fin n) :
      blockIndex B a = i ↔ blockIndex C (w a) = f i := by
    constructor
    · intro ha
      apply hs.injective
      rw [← hw a, ha, hf i]
    · intro ha
      apply ht.injective
      rw [hw a, ha, ← hf i]
  let eB : {a : Fin n // blockIndex B a = i} ≃ Fin (B.size i) :=
    (B.indexEquiv.symm.subtypeEquiv (p := fun a => blockIndex B a = i)
      (q := fun z : B.Index => z.1 = i) (fun _ => Iff.rfl)).trans
      (Equiv.sigmaSubtype i)
  let eC : {a : Fin n // blockIndex C a = f i} ≃ Fin (C.size (f i)) :=
    (C.indexEquiv.symm.subtypeEquiv (p := fun a => blockIndex C a = f i)
      (q := fun z : C.Index => z.1 = f i) (fun _ => Iff.rfl)).trans
      (Equiv.sigmaSubtype (f i))
  let ew : {a : Fin n // blockIndex B a = i} ≃
      {a : Fin n // blockIndex C a = f i} :=
    w.subtypeEquiv hcoord
  simpa only [Fintype.card_fin] using
    Fintype.card_congr ((eB.symm.trans ew).trans eC)

end Langlands.Exponents
