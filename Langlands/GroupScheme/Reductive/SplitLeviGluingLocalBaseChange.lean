import Langlands.GroupScheme.Reductive.SplitLeviGluingSimpleGraph
import Langlands.GroupScheme.Reductive.SplitLeviGluingGraphBaseChange
import Langlands.GroupScheme.Torus.RootSupportBaseChange

/-! # Actual local Levi comparisons and simple directions after field extension -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LeviGluing

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]

local notation "b" => algebraBaseMap k K
local notation "B" => GroupScheme.baseChange b
local notation "C" => CommGroupScheme.baseChange b

local instance affine_baseChange {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] : IsAffineHom ((B).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom b)
  infer_instance

local instance finiteType_baseChange {G : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom] : LocallyOfFiniteType ((B).obj G).X.hom := by
  change LocallyOfFiniteType (pullback.snd G.X.hom b)
  infer_instance

local instance smooth_baseChange {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] : Smooth ((B).obj G).X.hom := by
  change Smooth (pullback.snd G.X.hom b)
  infer_instance

variable {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i₁ : T.toGrp ⟶ G₁} {i₂ : T.toGrp ⟶ G₂}

/-- The actual cocharacter in an ambient group commutes with pullback. -/
theorem baseChange_groupHom_comp (ν : cocharacterLattice T) (i : T.toGrp ⟶ G₁) :
    Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom ν ≫ i) =
      CommGroupScheme.groupHom (cocharacterLattice.baseChange b T ν) ≫ (B).map i := by
  rw [cocharacterLattice.groupHom_baseChange_dynamic]
  simp only [Dynamic.baseChangeCocharacter, Functor.map_comp, Category.assoc]

/-- The actual supplied local comparison, including its common-torus square,
pulls back to the comparison for the actual pulled-back cocharacter. -/
def LocalComparison.baseChange {ν : cocharacterLattice T} (L : LocalComparison i₁ i₂ ν) :
    LocalComparison (T := (C).obj T) ((B).map i₁) ((B).map i₂)
      (cocharacterLattice.baseChange b T ν) where
  left := (B).obj L.left
  right := (B).obj L.right
  leftInclusion := (B).map L.leftInclusion
  rightInclusion := (B).map L.rightInclusion
  leftClosed := L.leftClosed.baseChange b
  rightClosed := L.rightClosed.baseChange b
  leftRep := by
    have h := Dynamic.isRepresentedBy_centralizer_baseChange b _ L.leftRep
    rw [baseChange_groupHom_comp K] at h
    exact h
  rightRep := by
    have h := Dynamic.isRepresentedBy_centralizer_baseChange b _ L.rightRep
    rw [baseChange_groupHom_comp K] at h
    exact h
  leftTorus := (B).map L.leftTorus
  rightTorus := (B).map L.rightTorus
  leftTorusComp := by rw [← Functor.map_comp, L.leftTorusComp]
  rightTorusComp := by rw [← Functor.map_comp, L.rightTorusComp]
  iso := (B).mapIso L.iso
  torusIsoComp := by
    change (B).map L.leftTorus ≫ (B).map L.iso.hom = (B).map L.rightTorus
    rw [← Functor.map_comp, L.torusIsoComp]

section Directions

variable [IsAffineHom G₁.X.hom] [LocallyOfFiniteType G₁.X.hom]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G₁)

include hT

/-- Positivity of an actual root is preserved and reflected by lattice pullback. -/
theorem mem_positiveRelativeRoots_baseChange_iff (ν : cocharacterLattice T)
    (α : characterLattice T) :
    characterLattice.baseChange b T α ∈ positiveRelativeRoots (T := (C).obj T) ((B).map i)
      (cocharacterLattice.baseChange b T ν) ↔ α ∈ positiveRelativeRoots i ν := by
  change (_ ∧ _) ↔ (_ ∧ _)
  exact and_congr (mem_roots_baseChange_iff (K := K) G₁ T hT i α)
    (by rw [latticePairing_baseChange])

/-- Positive indecomposability of the actual roots survives every field extension. -/
theorem mem_simpleRelativeRoots_baseChange_iff (ν : cocharacterLattice T)
    (α : characterLattice T) :
    characterLattice.baseChange b T α ∈ simpleRelativeRoots (T := (C).obj T) ((B).map i)
      (cocharacterLattice.baseChange b T ν) ↔ α ∈ simpleRelativeRoots i ν := by
  let e := characterLattice.baseChangeEquiv b T hT
  constructor
  · intro h
    refine ⟨(mem_positiveRelativeRoots_baseChange_iff K hT i ν α).mp h.1, ?_⟩
    rintro ⟨β, hβ, δ, hδ, he⟩
    apply h.2
    refine ⟨e β, (mem_positiveRelativeRoots_baseChange_iff K hT i ν β).mpr hβ,
      e δ, (mem_positiveRelativeRoots_baseChange_iff K hT i ν δ).mpr hδ, ?_⟩
    change e α = e β + e δ
    rw [he, map_add]
  · intro h
    refine ⟨(mem_positiveRelativeRoots_baseChange_iff K hT i ν α).mpr h.1, ?_⟩
    rintro ⟨β', hβ, δ', hδ, he⟩
    obtain ⟨β, rfl⟩ := e.surjective β'
    obtain ⟨δ, rfl⟩ := e.surjective δ'
    apply h.2
    refine ⟨β, (mem_positiveRelativeRoots_baseChange_iff K hT i ν β).mp hβ,
      δ, (mem_positiveRelativeRoots_baseChange_iff K hT i ν δ).mp hδ, ?_⟩
    apply e.injective
    rw [map_add]
    exact he

/-- The actual simple-root index equivalence for the pulled-back chamber. -/
def simpleRootsBaseChangeEquiv (ν : cocharacterLattice T) :
    simpleRelativeRoots i ν ≃ simpleRelativeRoots (T := (C).obj T) ((B).map i)
      (cocharacterLattice.baseChange b T ν) :=
  (characterLattice.baseChangeEquiv b T hT).toEquiv.subtypeEquiv
    (fun α => (mem_simpleRelativeRoots_baseChange_iff K hT i ν α).symm)

include hT in
/-- Genericity is preserved by every field extension of a split torus. -/
theorem IsGenericCocharacter.baseChange {ν : cocharacterLattice T}
    (hν : IsGenericCocharacter i ν) :
    IsGenericCocharacter (T := (C).obj T) ((B).map i) (cocharacterLattice.baseChange b T ν) := by
  intro α hα
  obtain ⟨β, rfl⟩ := (characterLattice.baseChangeEquiv b T hT).surjective α
  have hβ := (mem_roots_baseChange_iff (K := K) G₁ T hT i β).mp hα
  rw [characterLattice.baseChangeEquiv_apply, latticePairing_baseChange]
  exact hν β hβ

include hT in
/-- The rank-one kernel-direction condition survives lattice pullback. -/
theorem IsRankOneDirection.baseChange {ν : cocharacterLattice T}
    (hν : IsRankOneDirection i ν) :
    IsRankOneDirection (T := (C).obj T) ((B).map i) (cocharacterLattice.baseChange b T ν) := by
  intro α hα β hβ hαν hβν
  rw [roots_baseChange G₁ T hT i] at hα hβ
  obtain ⟨α₀, hα₀, rfl⟩ := hα
  obtain ⟨β₀, hβ₀, rfl⟩ := hβ
  rw [latticePairing_baseChange] at hαν hβν
  intro hli
  apply hν α₀ hα₀ β₀ hβ₀ hαν hβν
  let e := (characterLattice.baseChangeEquiv b T hT).toIntLinearEquiv.toLinearMap
  apply LinearIndependent.of_comp e
  have he : e ∘ ![α₀, β₀] =
      ![characterLattice.baseChange b T α₀, characterLattice.baseChange b T β₀] := by
    funext j
    fin_cases j <;> rfl
  rw [he]
  exact hli

/-- Actual generic chamber and all its indexed kernel directions after extension. -/
def SimpleRootDirections.baseChange (S : SimpleRootDirections i) :
    SimpleRootDirections (T := (C).obj T) ((B).map i) := by
  let e := simpleRootsBaseChangeEquiv K hT i S.chamber
  refine
    { chamber := cocharacterLattice.baseChange b T S.chamber
      generic := IsGenericCocharacter.baseChange K hT i S.generic
      direction := fun a => cocharacterLattice.baseChange b T (S.direction (e.symm a))
      annihilates := ?_
      rankOne := fun a => IsRankOneDirection.baseChange K hT i (S.rankOne (e.symm a)) }
  intro a
  have ha : characterLattice.baseChange b T (e.symm a).val = a.val :=
    congrArg Subtype.val (e.apply_symm_apply a)
  rw [← ha, latticePairing_baseChange]
  exact S.annihilates (e.symm a)

end Directions

end Langlands.GroupScheme.LeviGluing
