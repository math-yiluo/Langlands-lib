/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStageExtensionWithTruncation
import WeilConjectures.AlgebraicGeometry.EtaleHypercover
/-! # Extending a prescribed finite split hypercover skeleton -/
@[expose] public section
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

/-- A finite split étale hypercover skeleton extends to a full hypercover.
Source: Stacks 0DAV, split hypercover induction. Regard the skeleton as a
replacement of the terminal simplicial object. Extend it one degree at a time
with the existing replacement-stage extension theorem. Restrict this tower to
its diagonal stages and assemble it, retaining its prescribed truncation.
(auxiliary; not a blueprint node) -/
theorem exists_extension_of_finite_skeleton
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (r : ℕ) (U : TruncatedFiniteSplitEtaleHypercover X r) :
    ∃ V : FiniteSplitEtaleHypercover X,
      Nonempty ((SimplicialObject.truncation r).obj V.simplicial ≅ U.simplicial) := by
  classical
  let E : X.Etale := Scheme.Etale.mk (𝟙 X)
  let K : SimplicialObject X.Etale := (Functor.const _).obj E
  have hE : IsTerminal ((Scheme.Etale.forget X).obj E) := Over.mkIdTerminal
  have hK : IsEtaleHypercover K := by
    intro n
    refine ⟨E, (fun _ _ _ ↦ 𝟙 E), 𝟙 E, ?_, ?_, ?_, ?_⟩
    · intros
      simp [K]
    · intro T p hp
      refine ⟨hE.from T, ?_, ?_⟩
      · intro Δ h θ
        exact hE.hom_ext _ _
      · intro f hf
        exact hE.hom_ext _ _
    · intros
      simp [K]
    · change Surjective (𝟙 X)
      infer_instance
  let R : FiniteSplitReplacementStage K r :=
    { U := U
      f :=
        { app := fun Δ ↦ MorphismProperty.Over.homMk
            (U.simplicial.obj Δ).hom (Category.comp_id _) trivial
          naturality := by
            intro Δ Δ' α
            apply (Scheme.Etale.forget X).map_injective
            exact hE.hom_ext _ _ } }
  obtain ⟨V, _, e, _⟩ := exists_extension_of_replacement_stage K hK r R
  exact ⟨V, ⟨e⟩⟩

end AlgebraicGeometry.FiniteSplitEtaleHypercover
