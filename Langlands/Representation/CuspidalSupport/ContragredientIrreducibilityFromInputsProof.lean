import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.CuspidalSupport.ContragredientIrreducibilityFromInputsStatement
import Langlands.Representation.LanglandsClassification.OppositeLeviParabolic
import Langlands.GroupScheme.Rational.FullParabolicLevi
import Langlands.GroupScheme.Rational.MaximalLeviDynamicReduction
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # Proof of `ContragredientIrreducibilityFromInputsStatement`

Renard 2026, VI.2.2, Corollary, follows from Jacquet's theorem
(`Aubert.General.RationalPointsIrreducibleAdmissibleStatement`) and the second Theorem of
VI.9.6 (`Aubert.General.RepresentedParabolic.LeviJacquetContragredientStatement`).

Irreducibility passes to the contragredient by admissibility and Renard III.1.7, and back
by smooth separation. Supercuspidality passes to the contragredient because, for a proper
parabolic `P = MU` with actual opposite `P̄ = MŪ` (also proper), VI.9.6 gives
`r_P^G(π̃) ≅ (r_{P̄}^G π)~`; it passes back through the bidual isomorphism of admissible
representations.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe u v uΓ uG uV

open GroupScheme Aubert.General Aubert.General.RepresentedParabolic

/-- The smooth contragredient of a representation on a subsingleton space is carried by a
subsingleton space. -/
theorem subsingleton_contragredient {Γ : Type uG} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] (X : SmoothRep.{0, uG, uV} ℂ Γ) (hX : Subsingleton X) :
    Subsingleton X.contragredient := by
  have h : Subsingleton (SmoothDual X.representation) := by
    refine ⟨fun a b => Subtype.ext (LinearMap.ext fun x => ?_)⟩
    rw [Subsingleton.elim x 0, map_zero, map_zero]
  exact h

/-- The actual opposite parabolic of a proper parabolic is proper: if the opposite were the
whole group, its Levi `M` would be the whole group, hence so would `P ⊇ M`. -/
theorem not_isIso_oppositeLeviParabolic_inclusion {k : Type u} [Field k]
    {G P M : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {p : P ⟶ G} {l : M ⟶ P} (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hproper : ¬ IsIso p) :
    ¬ IsIso (oppositeLeviParabolic hG p l hp hl).inclusion := by
  intro hiso
  have hlevi : IsIso (oppositeLeviParabolic hG p l hp hl).levi :=
    (oppositeLeviParabolic hG p l hp hl).isLevi.isIso_of_isIso_parabolic
      (p := (oppositeLeviParabolic hG p l hp hl).inclusion) hG
  have hcomp : IsIso (l ≫ p) := by
    rw [← (oppositeLeviParabolic hG p l hp hl).levi_comp]
    infer_instance
  apply hproper
  apply isIso_of_full_range p hp.isClosedSubgroup.mono_overHom
  refine le_antisymm (SubgroupFunctor.le_def.mpr fun T => ?_) ?_
  · rw [SubgroupFunctor.top_carrier]
    exact le_top
  rw [← full_range_of_isIso (l ≫ p)]
  exact SubgroupFunctor.range_comp_le l p

section Supercuspidal

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance contragredientFromInputsPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Supercuspidality is invariant under isomorphism: the normalized Jacquet functors carry
an isomorphism to an isomorphism of Jacquet modules. -/
theorem isSupercuspidal_of_iso {A B : SmoothRep.{0, u, v} ℂ (rationalPoints G)} (e : A ≅ B)
    (hB : IsSupercuspidal B) : IsSupercuspidal A := by
  intro P M U p l r hp hl hr hmul hproper
  have := hB P M U p l r hp hl hr hmul hproper
  exact (SmoothRep.equivOfIso
    ((jacquetFunctor p l r hp hr hl hmul).mapIso e)).toLinearEquiv.toEquiv.subsingleton

/-- Renard VI.9.6 (second Theorem) implies that the smooth contragredient of a supercuspidal
representation is supercuspidal. For a proper parabolic `P = MU`, the isomorphism
`r_P^G(π̃) ≅ (r_{P̄}^G π)~` for the actual opposite `P̄ = M Ū` (proper as well) and the
vanishing of `r_{P̄}^G π` give the vanishing of `r_P^G(π̃)`. -/
theorem isSupercuspidal_contragredient_of_leviJacquetContragredient
    [ValuativeRel k] [IsNonarchimedeanLocalField k]
    (hCas : LeviJacquetContragredientStatement.{u, v}) (hG : IsConnectedReductive G)
    {A : SmoothRep.{0, u, v} ℂ (rationalPoints G)} (hA : IsSupercuspidal A) :
    IsSupercuspidal A.contragredient := by
  intro P M U p l r hp hl hr hmul hproper
  have hO := not_isIso_oppositeLeviParabolic_inclusion hG hp hl hproper
  obtain ⟨e⟩ := hCas k G hG (oppositeLeviParabolic hG p l hp hl).parabolic P M
    (oppositeLeviParabolic hG p l hp hl).radical U
    (oppositeLeviParabolic hG p l hp hl).inclusion (oppositeLeviParabolic hG p l hp hl).levi
    (oppositeLeviParabolic hG p l hp hl).unipotent
    (oppositeLeviParabolic hG p l hp hl).isParabolic (oppositeLeviParabolic hG p l hp hl).isLevi
    (oppositeLeviParabolic hG p l hp hl).isRadical
    (oppositeLeviParabolic hG p l hp hl).multiplication
    p l r hp hl hr hmul (oppositeLeviParabolic hG p l hp hl).levi_comp.symm
    (by
      rw [inf_comm, (oppositeLeviParabolic hG p l hp hl).levi_comp]
      exact (oppositeLeviParabolic hG p l hp hl).intersection)
  have h0 := hA _ _ _ _ _ _ (oppositeLeviParabolic hG p l hp hl).isParabolic
    (oppositeLeviParabolic hG p l hp hl).isLevi (oppositeLeviParabolic hG p l hp hl).isRadical
    (oppositeLeviParabolic hG p l hp hl).multiplication hO
  let : TopologicalSpace (rationalPoints M) :=
    leviPointTopology (oppositeLeviParabolic hG p l hp hl).levi
      (oppositeLeviParabolic hG p l hp hl).isLevi
  have : NonarchimedeanGroup (rationalPoints M) :=
    leviPoints_nonarchimedeanGroup (oppositeLeviParabolic hG p l hp hl).inclusion
      (oppositeLeviParabolic hG p l hp hl).levi (oppositeLeviParabolic hG p l hp hl).isParabolic
      (oppositeLeviParabolic hG p l hp hl).isLevi
  have h1 := subsingleton_contragredient
    ((leviJacquetFunctor.{u, v} (oppositeLeviParabolic hG p l hp hl).inclusion
      (oppositeLeviParabolic hG p l hp hl).levi (oppositeLeviParabolic hG p l hp hl).unipotent
      (oppositeLeviParabolic hG p l hp hl).isParabolic
      (oppositeLeviParabolic hG p l hp hl).isRadical
      (oppositeLeviParabolic hG p l hp hl).isLevi
      (oppositeLeviParabolic hG p l hp hl).multiplication).obj A) h0
  exact (SmoothRep.equivOfIso
    (e.app (Opposite.op A))).toLinearEquiv.toEquiv.subsingleton_congr.mpr h1

end Supercuspidal

/-- **Renard VI.2.2, Corollary, from Jacquet's theorem and VI.9.6.** Jacquet's theorem
`RationalPointsIrreducibleAdmissibleStatement` and the Jacquet modules of contragredients
`LeviJacquetContragredientStatement` imply `ContragredientIrreducibilityStatement`. -/
theorem contragredientIrreducibilityFromInputs :
    ContragredientIrreducibilityFromInputsStatement.{u, v} := by
  intro hAdm hCas k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ A
  have hcof : CompactOpenCofinal (rationalPoints G) :=
    Aubert.General.compactOpenCofinal_of_nonarchimedean (rationalPoints G)
  have hirr : A.IsIrreducible ↔ A.contragredient.IsIrreducible := by
    constructor
    · intro h
      exact (SmoothRep.isIrreducible_contragredient_iff hcof A (hAdm k G hG A h)).mpr h
    · intro h
      exact isIrreducible_of_smoothContragredient
        (fun _ _ _ σ hσ => smoothBidual_injective_of_compact_cofinal hcof σ hσ)
        A.representation A.isSmooth h
  refine ⟨hirr, ⟨fun h => ⟨hirr.mp h.1, ?_⟩, fun h => ⟨hirr.mpr h.1, ?_⟩⟩⟩
  · exact isSupercuspidal_contragredient_of_leviJacquetContragredient hCas hG h.2
  · have hadm : A.IsAdmissible := hAdm k G hG A (hirr.mpr h.1)
    exact isSupercuspidal_of_iso (SmoothRep.bidualIso hcof A hadm)
      (isSupercuspidal_contragredient_of_leviJacquetContragredient hCas hG h.2)

end Langlands.CuspidalSupport
