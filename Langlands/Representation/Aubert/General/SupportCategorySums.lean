import Langlands.Representation.Aubert.General.SupportCategory
import Langlands.Representation.Category.SubrepresentationSums

/-!
# Arbitrary invariant sums in the full smooth support category

The supported sum is the largest actual invariant submodule whose smooth
representation belongs to the specified support category.
-/

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {ι : Type uI}
variable {P M U : Finset ι → Subgroup G}
  {h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I)}
  {hU : ∀ I, IsClosed (U I : Set G)}
  {IsAssociate : Finset ι → Finset ι → G → Prop} {I : Finset ι}
  {hM : IsClosed (M I : Set G)}
  {hI : ∀ K : Finset I, IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
    ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I))}
  {E : SmoothRep.{0, uG, max uG uV} ℂ G}

/-- The full smooth support category is closed under arbitrary invariant sums. -/
theorem IsInSupportCategory.iSup {J : Type uJ}
    (S : J → Subrepresentation E.representation)
    (hS : ∀ j, IsInSupportCategory P M U h hU IsAssociate I hM hI
      (SmoothRep.subrepresentation E (S j))) :
    IsInSupportCategory P M U h hU IsAssociate I hM hI
      (SmoothRep.subrepresentation E (⨆ j, S j)) := by
  intro π hπ hπS
  obtain ⟨j, hj⟩ := SmoothRep.irreducibleSubquotient_iSup hπ S hπS
  exact hS j π hπ hj

/-- Membership of an invariant sum is equivalent to membership of all summands. -/
theorem isInSupportCategory_iSup_iff {J : Type uJ}
    (S : J → Subrepresentation E.representation) :
    IsInSupportCategory P M U h hU IsAssociate I hM hI
        (SmoothRep.subrepresentation E (⨆ j, S j)) ↔
      ∀ j, IsInSupportCategory P M U h hU IsAssociate I hM hI
        (SmoothRep.subrepresentation E (S j)) := by
  constructor
  · intro hS j
    exact hS.of_isSubquotient
      (SmoothRep.IsSubrepresentation.isSubquotient
        ⟨SmoothRep.subrepresentationInclusion (le_iSup S j),
          SmoothRep.subrepresentationInclusion_injective _⟩)
  · exact IsInSupportCategory.iSup S

/-- The actual invariant sum of all subrepresentations in the specified
full smooth support category. -/
noncomputable def supportSubrepresentationSum
    (P M U : Finset ι → Subgroup G)
    (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
    (hU : ∀ I, IsClosed (U I : Set G))
    (IsAssociate : Finset ι → Finset ι → G → Prop) (I : Finset ι)
    (hM : IsClosed (M I : Set G))
    (hI : ∀ K : Finset I, IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I)))
    (E : SmoothRep.{0, uG, max uG uV} ℂ G) : Subrepresentation E.representation :=
  ⨆ S : {S : Subrepresentation E.representation //
    IsInSupportCategory P M U h hU IsAssociate I hM hI (SmoothRep.subrepresentation E S)}, S.val

/-- The supported sum is itself in the full smooth support category. -/
theorem isInSupportCategory_supportSubrepresentationSum :
    IsInSupportCategory P M U h hU IsAssociate I hM hI
      (SmoothRep.subrepresentation E
        (supportSubrepresentationSum P M U h hU IsAssociate I hM hI E)) :=
  IsInSupportCategory.iSup _ (fun S => S.property)

/-- Every supported invariant submodule is contained in the supported sum. -/
theorem le_supportSubrepresentationSum {S : Subrepresentation E.representation}
    (hS : IsInSupportCategory P M U h hU IsAssociate I hM hI
      (SmoothRep.subrepresentation E S)) :
    S ≤ supportSubrepresentationSum P M U h hU IsAssociate I hM hI E := by
  unfold supportSubrepresentationSum
  exact le_iSup (fun T : {T : Subrepresentation E.representation //
    IsInSupportCategory P M U h hU IsAssociate I hM hI
      (SmoothRep.subrepresentation E T)} => T.val) ⟨S, hS⟩

/-- The universal property of the supported sum as a largest supported
invariant submodule, stated without a splitting assertion. -/
theorem supportSubrepresentationSum_le_iff (T : Subrepresentation E.representation) :
    supportSubrepresentationSum P M U h hU IsAssociate I hM hI E ≤ T ↔
      ∀ S : Subrepresentation E.representation,
        IsInSupportCategory P M U h hU IsAssociate I hM hI
          (SmoothRep.subrepresentation E S) → S ≤ T := by
  constructor
  · intro hT S hS
    exact (le_supportSubrepresentationSum hS).trans hT
  · intro hT
    exact iSup_le fun S => hT S.val S.property

end Langlands.Aubert.General
