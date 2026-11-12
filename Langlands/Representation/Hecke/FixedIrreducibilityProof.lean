import Langlands.Representation.Hecke.FixedVectorCornerStatements
import Langlands.Representation.CompactCoefficient.FixedLevelFiniteness
import Langlands.Representation.CompactCoefficient.SemisimplicityProof
import Langlands.Topology.LocallyProfiniteProof

/-! # Irreducibility detected by compact-open fixed corner modules -/

noncomputable section

namespace Langlands.Hecke

open MeasureTheory
open scoped _root_.Topology

universe u v

/-- Renard III.1.5, Theorem (i), with both zero cases included. -/
theorem irreducibleIffFixedSimple : IrreducibleIffFixedSimpleStatement.{u, v} := by
  classical
  intro G _ _ _ _ _ _ _ _ μ _ A
  constructor
  · rintro (hA | hA) K hK
    · by_cases hK0 : fixedVectors A.representation K.toSubgroup = ⊥
      · exact Or.inr hK0
      · exact Or.inl (CompactCoefficientClass.isSimpleModule_fixedVectors
          μ A.representation A.isSmooth K hK hA hK0)
    · exact Or.inr (eq_bot_iff.mpr fun x _ =>
        (Submodule.mem_bot ℂ).mpr (hA.elim x 0))
  · intro h
    by_cases hA : Subsingleton A
    · exact Or.inr hA
    · let _ : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
      have hsub : Nontrivial (Subrepresentation A.representation) := by
        refine ⟨⟨⊥, ⊤, ?_⟩⟩
        intro heq
        have heq' := congrArg Subrepresentation.toSubmodule heq
        exact (bot_ne_top : (⊥ : Submodule ℂ A) ≠ ⊤) heq'
      let _ := hsub
      refine Or.inl (IsSimpleOrder.of_forall_eq_top fun S hS => ?_)
      have hS' : S.toSubmodule ≠ ⊥ := by
        intro heq
        apply hS
        apply Subrepresentation.ext
        exact heq
      obtain ⟨x, hxS, hx0⟩ := (Submodule.ne_bot_iff _).mp hS'
      apply top_unique
      intro y _
      obtain ⟨U, hxU⟩ := A.isSmooth x
      obtain ⟨V, hyV⟩ := A.isSmooth y
      obtain ⟨K, hK, hKUV⟩ :=
        (Topology.LocallyProfiniteProof.vanDantzig G).mp
          Topology.isLocallyProfinite_of_mathlib |>.2 (U ∩ V : Set G)
            ((U.isOpen.inter V.isOpen).mem_nhds ⟨U.one_mem, V.one_mem⟩)
      have hxK : x ∈ fixedVectors A.representation K.toSubgroup :=
        fun k => hxU ⟨k, (hKUV k.property).1⟩
      have hyK : y ∈ fixedVectors A.representation K.toSubgroup :=
        fun k => hyV ⟨k, (hKUV k.property).2⟩
      let _ := cornerModule μ A.representation A.isSmooth K hK
      have hfix : IsSimpleModule (HeckeAlgebra.Corner μ K hK)
          (fixedVectors A.representation K.toSubgroup) := by
        rcases h K hK with hs | hz
        · exact hs
        · exact False.elim (hx0 ((Submodule.mem_bot ℂ).mp (hz ▸ hxK)))
      let _ := hfix
      let T : Submodule (HeckeAlgebra.Corner μ K hK)
          (fixedVectors A.representation K.toSubgroup) := {
        carrier := {w | (w : A) ∈ S}
        zero_mem' := S.toSubmodule.zero_mem
        add_mem' := fun ha hb => S.toSubmodule.add_mem ha hb
        smul_mem' := fun f w hw => by
          change integratedAction μ A.representation A.isSmooth
            (HeckeAlgebra.toTestFunction μ
              (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK f)) w ∈ S
          exact CompactCoefficientSemisimplicity.integratedAction_mem
            μ A.representation A.isSmooth S _ hw }
      have hT : T ≠ ⊥ := by
        intro hz
        have hxT : (⟨x, hxK⟩ : fixedVectors A.representation K.toSubgroup) ∈ T := hxS
        rw [hz, Submodule.mem_bot] at hxT
        exact hx0 (congrArg Subtype.val hxT)
      have hTtop : T = ⊤ := (eq_bot_or_eq_top T).resolve_left hT
      have hyT : (⟨y, hyK⟩ : fixedVectors A.representation K.toSubgroup) ∈ T := by
        rw [hTtop]
        exact Submodule.mem_top
      exact hyT

end Langlands.Hecke
