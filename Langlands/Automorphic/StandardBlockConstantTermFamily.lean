import Langlands.Automorphic.GeneralLinearBlockConstantTermOperator
import Langlands.Automorphic.FullOperatorAction
import Langlands.GroupScheme.GeneralLinearBlockUnipotentCoordinates
import Langlands.Representation.Geometric.BlockShapeCuts
import Mathlib.Data.List.Sort

/-! # The finite family of standard block constant terms of `GL_n` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

/-- The block containing coordinate `i` is numbered by the cuts strictly before `i`.
Negating the number gives the upper standard parabolic convention. -/
def standardBlockWeight {n : ℕ} (s : Finset (Fin (n - 1))) (i : Fin n) : ℤ :=
  -((s.filter fun c => c.val < i.val).card : ℤ)

private theorem standardBlockWeight_le_iff {n : ℕ} (s : Finset (Fin (n - 1))) (i j : Fin n) :
    standardBlockWeight s i ≤ standardBlockWeight s j ↔
      s.filter (fun c => c.val < j.val) ⊆ s.filter (fun c => c.val < i.val) := by
  have hsub {a b : Fin n} (hab : a ≤ b) :
      s.filter (fun c => c.val < a.val) ⊆ s.filter (fun c => c.val < b.val) := by
    intro c hc
    obtain ⟨hcs, hca⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr ⟨hcs, hca.trans_le hab⟩
  rw [standardBlockWeight, standardBlockWeight, neg_le_neg_iff, Int.ofNat_le]
  constructor
  · intro h
    rcases le_total j i with hji | hij
    · exact hsub hji
    · exact (Finset.eq_of_subset_of_card_le (hsub hij) h).symm.le
  · exact Finset.card_le_card

/-- Adding cuts refines the parabolic in the sense required for the split-radical
constant-term formula. -/
theorem standardBlockWeight_refines {n : ℕ} {s t : Finset (Fin (n - 1))} (hst : s ⊆ t)
    (i j : Fin n) (hij : standardBlockWeight t i ≤ standardBlockWeight t j) :
    standardBlockWeight s i ≤ standardBlockWeight s j := by
  apply (standardBlockWeight_le_iff s i j).mpr
  intro c hc
  obtain ⟨hcs, hcj⟩ := Finset.mem_filter.mp hc
  have hci := (standardBlockWeight_le_iff t i j).mp hij
    (Finset.mem_filter.mpr ⟨hst hcs, hcj⟩)
  exact Finset.mem_filter.mpr ⟨hcs, (Finset.mem_filter.mp hci).2⟩

/-- Enumerate all standard cut sets by nondecreasing number of cuts. -/
def standardBlockCuts (n : ℕ) : List (Finset (Fin (n - 1))) :=
  (Finset.univ : Finset (Finset (Fin (n - 1)))).toList.mergeSort
    (fun s t => decide (s.card ≤ t.card))

theorem mem_standardBlockCuts {n : ℕ} (s : Finset (Fin (n - 1))) :
    s ∈ standardBlockCuts n := by
  change s ∈ List.mergeSort _ _
  rw [(List.mergeSort_perm _ _).mem_iff, Finset.mem_toList]
  exact Finset.mem_univ _

theorem standardBlockCuts_pairwise (n : ℕ) :
    (standardBlockCuts n).Pairwise fun s t => s.card ≤ t.card := by
  unfold standardBlockCuts
  simpa only [decide_eq_true_eq] using
    List.pairwise_mergeSort (le := fun s t : Finset (Fin (n - 1)) => decide (s.card ≤ t.card))
      (fun _ _ _ h₁ h₂ => decide_eq_true (le_trans (of_decide_eq_true h₁) (of_decide_eq_true h₂)))
      (fun s t => by simpa only [Bool.or_eq_true, decide_eq_true_eq] using le_total s.card t.card) _

open GroupScheme.GeneralLinear AdelicSubgroupPoints

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}

local notation "RF" => CommRingCat.of F
local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) RF
local notation "N₀" => blockUnipotent (Fin n) RF (standardBlockWeight ∅)

local instance blockTermFamilyAffine : IsAffine (GLG).X.left := isAffine_groupScheme (Fin n) RF

local instance blockTermFamilySmooth : Smooth (GLG).X.hom := smoothStatement (Fin n) RF

local instance blockTermFamilyRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _

local instance blockTermFamilyContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _

local instance blockTermFamilyFiniteSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

/-- The constant term with no cuts is the original function at corresponding points. -/
theorem finiteSmoothBlockConstantTerm_empty
    (f : FiniteSmoothRationalFunctions F n) (g : AdelicGroupPoints F GLG) :
    finiteSmoothBlockConstantTerm F (standardBlockWeight ∅) f g =
      ContinuousRationalFunctions.evaluate F n f.val (GeneralLinearGroupPoints.adelicEquiv F n g) := by
  let : IsClosed (adelicPoints F GLG N₀ : Set (AdelicGroupPoints F GLG)) :=
    GeneralLinearBlockSemidirect.isClosed_adelicPoints_blockUnipotent F (standardBlockWeight ∅)
  let : CompactSpace (RationalQuotient F GLG N₀) :=
    GroupSchemeFunctions.blockUnipotentRationalQuotientCompactSpace F (standardBlockWeight ∅)
  let := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F GLG N₀
  have htrivial (z : adelicPoints F GLG N₀) : z.val = 1 := by
    have hz := (mem_blockUnipotent_affinePoints_iff (CommRingCat.of F)
      (CommAlgCat.of F (Adeles F)) (standardBlockWeight ∅) z.val).mp z.property
    apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
    rw [map_one]
    apply Units.ext
    ext i j
    exact hz i j (by simp [standardBlockWeight])
  let a := (GroupSchemeFunctions.continuousGeneralLinearEquiv F n).symm f.val
  have hconst :
      GroupSchemeFunctions.constantTermIntegrand F GLG N₀ a g =
        fun _ => GroupSchemeFunctions.evaluate F GLG a g := by
    funext q
    obtain ⟨z, rfl⟩ := LeftCosetSpace.mk_surjective (rationalSubgroup F GLG N₀) q
    rw [GroupSchemeFunctions.constantTermIntegrand_mk, htrivial z, one_mul]
  rw [finiteSmoothBlockConstantTerm_apply, GroupSchemeFunctions.normalizedBlockConstantTerm,
    GroupSchemeFunctions.constantTerm]
  change (∫ q, GroupSchemeFunctions.constantTermIntegrand F GLG N₀ a g q
    ∂normalizedRationalQuotientHaarMeasure F GLG N₀) = _
  rw [hconst, integral_const, probReal_univ, one_smul]
  rfl

local instance blockTermFamilyFormsAddCommGroup : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

local instance blockTermFamilyStableAddCommGroup : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

local instance blockTermFamilyRealizationAddCommGroup (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

private def realizedAmbientInclusion (S : OperatorRealization F n) :
    S.representation.IntertwiningMap (automorphicOperatorAction F n) :=
  (fullAutomorphicFiniteSmoothInclusion F n).comp
    ((stableAutomorphicOperatorEquiv F n).toIntertwiningMap.comp S.inclusion)

/-- The block constant-term kernel pulled back to the realization, as a module
over the monoid algebra of the concrete operators. -/
def realizedBlockConstantTermKernel (S : OperatorRealization F n) (e : Fin n → ℤ) :
    Submodule (MonoidAlgebra ℂ (automorphicOperatorAlgebra F n)) S.representation.asModule :=
  (blockConstantTermKernel F e).asSubmodule.comap
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (realizedAmbientInclusion F S))

theorem mem_realizedBlockConstantTermKernel (S : OperatorRealization F n) (e : Fin n → ℤ)
    (x : S.representation.asModule) :
    x ∈ realizedBlockConstantTermKernel F S e ↔
      ∀ g, finiteSmoothBlockConstantTerm F e (S.ambient x) g = 0 :=
  mem_blockConstantTermKernel F e (S.ambient x)

theorem eq_zero_of_mem_realizedBlockConstantTermKernel_empty (S : OperatorRealization F n)
    {x : S.representation.asModule} (hx : x ∈ realizedBlockConstantTermKernel F S
      (standardBlockWeight ∅)) : x = 0 := by
  apply S.toContinuous_injective
  apply Subtype.ext
  apply Subtype.ext
  funext d
  obtain ⟨g, rfl⟩ := (GeneralLinearGroupPoints.adelicEquiv F n).surjective d
  have h := (mem_realizedBlockConstantTermKernel F S _ x).mp hx g
  rw [finiteSmoothBlockConstantTerm_empty] at h
  exact h

end Langlands.Automorphic
