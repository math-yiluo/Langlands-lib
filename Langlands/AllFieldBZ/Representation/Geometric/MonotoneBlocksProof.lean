import Langlands.AllFieldBZ.Representation.Geometric.WeylUniquenessProof
import Langlands.Representation.Geometric.MonotoneBlocksProof

/-!
# All-field port of `Langlands.Representation.Geometric.MonotoneBlocksProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.MonotoneBlocksProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric
open Langlands.GeneralLinear
private theorem _root_.Langlands.Geometric.blockShape_of_monotone_surjective {k m : ℕ}
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

end Langlands.AllFieldBZ.Geometric
