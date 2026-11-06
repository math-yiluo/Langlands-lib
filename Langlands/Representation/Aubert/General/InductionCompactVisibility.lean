import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Induction.CompactQuotientProof

/-! # Compact visibility of the inducing representation

Evaluation on a finite double-coset cover detects fixed vectors of actual
normalized induction in finitely many compact open Levi fixed spaces.
The detecting subgroups are chosen before the inducing representation.
-/

noncomputable section

open CategoryTheory Topology

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}

/-- An open Levi neighborhood on which both the evaluation covariance and the
normalizing scalar reduce to the original Levi action. -/
def inducingEvaluationNeighborhood (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (K : OpenSubgroup G) (x : G) : OpenSubgroup M :=
  Induction.conjOpenSubgroup M K x ⊓
    (⟨(HaarModulus.closedHalfCharacter U hU P h.le_normalizer).ker,
      HaarModulus.isOpen_ker_closedHalfCharacter U hU P h.le_normalizer⟩ :
        OpenSubgroup P).comap (Subgroup.inclusion h.levi_le)
      (continuous_subtype_val.subtype_mk _)

/-- A subgroup of the evaluation neighborhood fixes the original inducing
value of every fixed normalized induced function. -/
theorem normalizedInduction_eval_mem_fixedVectors
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (K : OpenSubgroup G) (x : G) (L : OpenSubgroup M)
    (hL : L ≤ inducingEvaluationNeighborhood h hU K x)
    (A : SmoothRep.{0, uG, uV} ℂ M)
    (f : (normalizedInductionFunctor h hU).obj A)
    (hf : f ∈ fixedVectors
      ((normalizedInductionFunctor h hU).obj A).representation K.toSubgroup) :
    Induction.eval P (inducingRepresentation h hU A) f x ∈
      fixedVectors A.representation L.toSubgroup := by
  intro m
  have hm := hL m.property
  have hmK : (m : M) ∈ Induction.conjOpenSubgroup M K x := hm.1
  have hmχ : HaarModulus.closedHalfCharacter U hU P h.le_normalizer
      (Subgroup.inclusion h.levi_le (m : M)) = 1 := hm.2
  have hpK : Subgroup.inclusion h.levi_le (m : M) ∈
      Induction.conjOpenSubgroup P K x :=
    Induction.mem_conjOpenSubgroup.mpr (Induction.mem_conjOpenSubgroup.mp hmK)
  have he := Induction.eval_mem_fixedVectors P (inducingRepresentation h hU A)
    K x hf ⟨Subgroup.inclusion h.levi_le (m : M), hpK⟩
  change ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer
      (Subgroup.inclusion h.levi_le (m : M)) : ℂˣ) : ℂ) •
    A.representation (h.projection (Subgroup.inclusion h.levi_le (m : M)))
      (Induction.eval P (inducingRepresentation h hU A) f x) =
    Induction.eval P (inducingRepresentation h hU A) f x at he
  rw [hmχ, Units.val_one, one_smul] at he
  have hproj : h.projection (Subgroup.inclusion h.levi_le (m : M)) = (m : M) :=
    h.projection_levi (m : M)
  rw [hproj] at he
  exact he

/-- The evaluation neighborhood contains a compact open subgroup whenever the
Levi subgroup is closed in the locally compact ambient group. -/
theorem exists_compactOpen_inducingEvaluation_subgroup
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hM : IsClosed (M : Set G)) (K : OpenSubgroup G) (x : G) :
    ∃ L : OpenSubgroup M, IsCompact (L : Set M) ∧
      L ≤ inducingEvaluationNeighborhood h hU K x := by
  let := hM.locallyCompactSpace
  exact compactOpenSubgroupBasis M (inducingEvaluationNeighborhood h hU K x)
    ((inducingEvaluationNeighborhood h hU K x).isOpen.mem_nhds
      (inducingEvaluationNeighborhood h hU K x).one_mem)

/-- One finite family of compact open Levi subgroups detects nonzero fixed
vectors of normalized induction, for every inducing representation. -/
def FiniteInductionFixedVectorVisibility
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (K : OpenSubgroup G) : Prop :=
  ∃ (t : Finset G) (L : t → OpenSubgroup M),
    (∀ x, IsCompact (L x : Set M)) ∧
    ∀ A : SmoothRep.{0, uG, uV} ℂ M,
      Nontrivial (fixedVectors
        ((normalizedInductionFunctor h hU).obj A).representation K.toSubgroup) →
      ∃ x : t, Nontrivial (fixedVectors A.representation (L x).toSubgroup)

/-- Compactness of the actual left quotient gives finite compact visibility
without admissibility or finite generation of the inducing representation. -/
theorem finiteInductionFixedVectorVisibility
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hM : IsClosed (M : Set G)) [CompactSpace (Induction.LeftQuotient P)]
    (K : OpenSubgroup G) :
    FiniteInductionFixedVectorVisibility.{uG, uV} h hU K := by
  classical
  obtain ⟨t, ht⟩ := Induction.exists_finset_doubleCoset_cover P K
  choose L hLc hL using
    (fun x : t => exists_compactOpen_inducingEvaluation_subgroup h hU hM K (x : G))
  refine ⟨t, L, hLc, fun A hA => ?_⟩
  let ev : fixedVectors
      ((normalizedInductionFunctor h hU).obj A).representation K.toSubgroup →ₗ[ℂ]
      ((x : t) → fixedVectors A.representation (L x).toSubgroup) :=
    { toFun := fun f x => ⟨Induction.eval P (inducingRepresentation h hU A) f.val x,
        normalizedInduction_eval_mem_fixedVectors h hU K x (L x) (hL x) A f.val f.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    intro f g he
    apply Induction.fixedEvaluation_injective P (inducingRepresentation h hU A) K t ht
    funext x
    apply Subtype.ext
    exact congrArg (fun z => (z x).val) he
  have := hA
  obtain ⟨f, hf⟩ := exists_ne (0 : fixedVectors
    ((normalizedInductionFunctor h hU).obj A).representation K.toSubgroup)
  have hne : ev f ≠ 0 := fun he => hf (hev (he.trans ev.map_zero.symm))
  have hex : ∃ x : t, ev f x ≠ 0 := by
    by_contra hn
    apply hne
    funext x
    exact not_ne_iff.mp (not_exists.mp hn x)
  obtain ⟨x, hx⟩ := hex
  exact ⟨x, ⟨⟨ev f x, 0, hx⟩⟩⟩

end Langlands.Aubert.General
