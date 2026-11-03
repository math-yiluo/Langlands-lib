import Langlands.GroupScheme.Dynamic.ActionStability
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Dynamic.LimitMap
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.UnipotentConnected
import Langlands.GroupScheme.Rational.ActionWeightTransport
import Langlands.GroupScheme.Rational.TorusUnipotenceStatement
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # The multiplicative-group action on a dynamic contracting subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section Action

variable {S : Scheme.{u}} {G H : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ G) (j : H ⟶ G)
    (hj : (unipotent χ).IsRepresentedBy j)

/-- The actual conjugation action of the cocharacter on any representative of
its contracting subgroup. -/
def unipotentConjugationAction : AutomorphicAction (Gm S).toGrp H :=
  (AutomorphicAction.conjugation χ).onRepresentedSubgroup j hj (by
    simpa only [Category.id_comp] using
      unipotent_isStable_conjugation χ (𝟙 (Gm S).toGrp))

/-- The inclusion of the contracting subgroup intertwines the restricted
action and ambient conjugation on every scheme test. -/
theorem unipotentConjugationAction_act_comp {T : Over S}
    (t : T ⟶ (Gm S).X) (h : T ⟶ H.X) :
    (unipotentConjugationAction χ j hj).act t h ≫ j.hom.hom =
      (t ≫ χ.hom.hom) * (h ≫ j.hom.hom) * (t ≫ χ.hom.hom)⁻¹ := by
  rw [← AutomorphicAction.conjugation_act χ]
  exact AutomorphicAction.onRepresentedSubgroup_act_comp _ _ _ _ t h

end Action

section Weights

open RelativeRoot

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom H.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (j : H ⟶ G)
    (hj : (unipotent χ).IsRepresentedBy j)

/-- The actual cocharacter action on the contracting subgroup has no zero
Lie weight. This uses the zero-weight centralizer criterion and the trivial
intersection of the centralizer and the contracting subgroup. -/
theorem actionWeightSpace_unipotentConjugationAction_zero :
    actionWeightSpace (unipotentConjugationAction χ j hj) 0 = ⊥ := by
  let : Mono j.hom.hom := hj.1
  apply le_antisymm _ bot_le
  intro X hX
  rw [Submodule.mem_bot]
  apply Lie.targetMapLinear_injective j k
  rw [map_zero]
  have hW := (RelativeRoot.mem_actionWeightSpace_target_iff j hj.1
    (unipotentConjugationAction χ j hj) (AutomorphicAction.conjugation χ)
    (fun _ t h => by
      simpa only [AutomorphicAction.conjugation_act] using
        unipotentConjugationAction_act_comp χ j hj t h) 0 X).mpr hX
  rw [actionWeightSpace_conjugation] at hW
  have hMap : Lie.targetMapLinear j k X =
      Additive.ofMul (Lie.targetMap j k X.toMul) := rfl
  rw [hMap] at hW
  have hZ : (Lie.targetMap j k X.toMul).val ∈ (centralizer χ).carrier _ :=
    ((dynamicLie k G χ (Lie.targetMap j k X.toMul)).1).mpr
      (by simpa only [Gm.powerHom_apply, zero_zsmul] using hW)
  have hU : (Lie.targetMap j k X.toMul).val ∈ (unipotent χ).carrier _ := by
    rw [← hj.2]
    exact SubgroupFunctor.mem_range.mpr ⟨X.toMul.val, rfl⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  exact eq_one_of_mem_centralizer_of_mem_unipotent χ
    (fun _ _ _ _ h h' => h.unique χ h') hZ hU

end Weights

section Unipotence

open RelativeRoot

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)

/-- Specializing the general split-torus unipotence statement to the actual
contracting-subgroup action proves unipotence of any closed representative.
The general structural statement is retained as an explicit hypothesis. -/
theorem isUnipotent_of_torusActionUnipotence
    (hUnip : TorusActionUnipotenceStatement.{u})
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : (unipotent χ).IsRepresentedBy j) (hc : IsClosedSubgroup j) :
    IsUnipotent H := by
  let : IsAffineHom H.X.hom := hc.isAffineHom
  exact hUnip k H ((dynamicSmooth k G χ H j).2.2 hj) inferInstance
    (DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G χ hj)
    (Gm (Spec (CommRingCat.of k))) isSplitTorus_gm
    (unipotentConjugationAction χ j hj)
    (actionWeightSpace_unipotentConjugationAction_zero χ j hj)

end Unipotence

end Langlands.GroupScheme.Dynamic
