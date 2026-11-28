import Langlands.GroupScheme.Reductive.StarAction
import Langlands.LinearAlgebra.TypeD4WeylInversion

/-! # The ordinary and star actions for D4 opposition -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.RootDatumNegation

namespace Langlands.GroupScheme.GaloisPinningData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (p : GaloisPinningData k E G)

/-- When the ordinary action on a simply connected D4 pinning sends the
chosen base to its negative, the correction to the star action is full inversion. -/
theorem starAction_eq_negAut_mul_of_D4_opposite
    (hspan : p.toSplitPinning.rootDatum.corootSpan ℤ = ⊤) (e : p.toSplitPinning.base.support ≃ Fin 4)
    (hD : ∀ i j : p.toSplitPinning.base.support,
      p.toSplitPinning.rootDatum.pairing i.val j.val = CartanMatrix.D 4 (e i) (e j))
    (σ : E ≃ₐ[k] E)
    (hopp : ∀ a : p.toSplitPinning.rootIndex,
      (p.galoisAction σ).indexEquiv a ∈
          (p.toSplitPinning.base.map (negAut p.toSplitPinning.rootDatum)).support ↔
        a ∈ p.toSplitPinning.base.support) :
    (p.starAction σ).val = negAut p.toSplitPinning.rootDatum * p.galoisAction σ := by
  classical
  let P := p.toSplitPinning
  let δ := negAut p.toSplitPinning.rootDatum * p.galoisAction σ
  have hδ : δ ∈ P.basedRootDatumAut := by
    intro a
    change a ∈ p.toSplitPinning.base.support ↔
      (negAut p.toSplitPinning.rootDatum).indexEquiv ((p.galoisAction σ).indexEquiv a) ∈
        p.toSplitPinning.base.support
    rw [← mem_support_map_negAut]
    exact (hopp a).symm
  let δb : P.basedRootDatumAut := ⟨δ, hδ⟩
  have hinv := negAut_mem_weylGroup_of_D4 p.toSplitPinning.rootDatum p.toSplitPinning.base hspan e hD
  have hone : P.basedRootDatumProjection (negAut p.toSplitPinning.rootDatum) = 1 :=
    (P.basedRootDatumProjection_eq_one_iff _).mpr hinv
  have hh : P.basedRootDatumProjection δ = P.basedRootDatumProjection (p.galoisAction σ) := by
    dsimp only [δ]
    rw [map_mul, hone, one_mul]
  have hb : P.basedRootDatumProjection δ = δb := P.basedRootDatumProjection_of_based δb
  exact congrArg Subtype.val (hh.symm.trans hb)

end Langlands.GroupScheme.GaloisPinningData
