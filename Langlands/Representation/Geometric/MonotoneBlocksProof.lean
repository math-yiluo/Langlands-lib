import Langlands.Representation.Geometric.MonotoneBlocksStatement
import Langlands.Representation.Geometric.WeylUniquenessProof
import Mathlib.Data.Fintype.Sort

namespace Langlands.Geometric

open GeneralLinear

private theorem blockShape_of_monotone_surjective {k m : ℕ}
    (h : Fin k → Fin m) (hm : Monotone h) (hs : Function.Surjective h) :
    ∃ S : BlockShape k, ∃ e : Fin S.length ≃o Fin m,
      ∀ a, e (blockIndex S a) = h a := by
  classical
  let S : BlockShape k :=
    { length := m
      size := fun i => Fintype.card {a : Fin k // h a = i}
      positive := fun i => by
        obtain ⟨a, ha⟩ := hs i
        exact Fintype.card_pos_iff.mpr ⟨⟨a, ha⟩⟩
      sum_eq := by
        simpa only [Fintype.card_sigma, Fintype.card_fin] using
          Fintype.card_congr (Equiv.sigmaFiberEquiv h) }
  let E : S.Index ≃ Fin k :=
    (Equiv.sigmaCongrRight (fun i =>
      (Fintype.equivFin {a : Fin k // h a = i}).symm)).trans
        (Equiv.sigmaFiberEquiv h)
  let p : Equiv.Perm (Fin k) := S.indexEquiv.symm.trans E
  have hp : h ∘ p = blockIndex S := by
    funext a
    exact ((Fintype.equivFin {x : Fin k // h x = (S.indexEquiv.symm a).1}).symm
      (S.indexEquiv.symm a).2).property
  have heq := Tuple.unique_monotone (σ := Equiv.refl _) (τ := p)
    (show Monotone (h ∘ Equiv.refl _) from hm)
    (show Monotone (h ∘ p) by rw [hp]; exact blockIndex_monotone S)
  refine ⟨S, OrderIso.refl _, ?_⟩
  intro a
  simpa only [hp, Equiv.coe_refl, Function.comp_id, OrderIso.refl_apply] using
    (congrFun heq a).symm

/-- The nonempty fibers of a monotone finite map form positive consecutive blocks. -/
theorem monotoneBlockShape : MonotoneBlockShapeTheorem := by
  classical
  intro k l f hf
  let e := Fintype.orderIsoFinOfCardEq (Set.range f) rfl
  let h : Fin k → Fin (Fintype.card (Set.range f)) :=
    fun a => e.symm (Set.rangeFactorization f a)
  have hm : Monotone h := by
    intro a b hab
    exact e.symm.monotone (hf hab)
  have hs : Function.Surjective h :=
    e.symm.surjective.comp Set.rangeFactorization_surjective
  obtain ⟨S, E, hE⟩ := blockShape_of_monotone_surjective h hm hs
  refine ⟨S, fun a b => ?_⟩
  rw [← E.le_iff_le, hE, hE]
  exact e.symm.le_iff_le

end Langlands.Geometric
