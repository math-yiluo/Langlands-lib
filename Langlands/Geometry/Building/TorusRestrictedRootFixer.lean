import Langlands.Geometry.Building.GenericPointSharpExchange
import Langlands.Geometry.Building.SelectedRootDepthIntersection
import Langlands.Geometry.Building.RootValueTorusRestriction
import Langlands.GroupScheme.Absolute.RegularPerturbation

/-! # Full point fixers on roots restricted between split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

namespace KPApartmentData

variable {ω : kˣ → ℝ} (D : KPApartmentData i ω)

omit [Mono i.hom.hom.left] in
/-- A generic direction can preserve every selected positive root pairing. -/
private theorem exists_generic_positive_on_selected
    [LocallyOfFiniteType G.X.hom] (hT : IsSplitTorus T.toGrp)
    (A : AddSubsemigroup (characterLattice T)) (ξ : cocharacterLattice T)
    (hpos : ∀ a ∈ relativeRoots i, a ∈ A → 0 < latticePairing T a ξ) :
    ∃ ν : cocharacterLattice T, IsGenericCocharacter i ν ∧
      ∀ a ∈ relativeRoots i, a ∈ A → 0 < latticePairing T a ν := by
  classical
  obtain ⟨eta, heta⟩ := hT.exists_genericCocharacter i
  let hr := hT.finite_relativeRoots i
  let q := fun a : characterLattice T => (latticePairing T a).toAddMonoidHom
  let s := hr.toFinset
  let N := IntegralPerturbation.bound q s eta
  have hgeneric :=
    (IntegralPerturbation.regular_and_nonneg q s ξ eta
      (fun a ha => heta a (hr.mem_toFinset.mp ha)) (N := N) le_rfl).1
  refine ⟨N • ξ + eta, fun a ha => hgeneric a (hr.mem_toFinset.mpr ha), ?_⟩
  intro a ha hA
  exact (IntegralPerturbation.signs q s ξ eta (N := N) le_rfl
    (hr.mem_toFinset.mpr ha)).1.mpr (Or.inl (hpos a ha hA))

/-- A positive selected semigroup meets a full point fixer in precisely its
actual depth-zero root subgroup. No apartment root-system axioms are needed. -/
theorem semigroupPoints_inf_reducedFixer_eq_selectedRootDepth
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hE : RelativeRoot.HasOppositeFactorPairs i)
    (A : AddSubsemigroup (characterLattice T)) (hA : 0 ∉ A)
    (ξ : cocharacterLattice T)
    (hpos : ∀ a ∈ relativeRoots i, a ∈ A → 0 < latticePairing T a ξ)
    (x : D.Apartment) :
    (RelativeRoot.semigroupSubgroup (AutomorphicAction.conjugation i) A).carrier
        (Over.mk (𝟙 _)) ⊓ D.reducedFixer (D.apartmentMap x) =
      selectedRootDepthSubgroup x.isValuation A 0 := by
  let : Smooth G.X.hom := hG.smooth
  have hT := hi.isSplitSubtorus.1
  obtain ⟨ν, hν, hνpos⟩ := exists_generic_positive_on_selected hT A ξ hpos
  let P := RelativeRoot.positiveSemigroup ν
  have hP : 0 ∉ P := by
    change ¬ 0 < latticePairing T 0 ν
    simp
  apply le_antisymm
  · intro g hg
    have hU : g ∈ (Dynamic.unipotent
        (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) := by
      have hle : (RelativeRoot.semigroupSubgroup
          (AutomorphicAction.conjugation i) A).carrier (Over.mk (𝟙 _)) ≤
          (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier
            (Over.mk (𝟙 _)) := by
        rw [RelativeRoot.semigroupSubgroup_carrier_eq_iSup_selectedRoots
          i hT hE A hA]
        exact iSup_le fun a =>
          RelativeRoot.subgroup_le_dynamicUnipotent i ν
            (hνpos a.val a.property.1 a.property.2) (Over.mk (𝟙 _))
      exact hle hg.1
    have hdepth : g ∈ selectedRootDepthSubgroup x.isValuation P 0 := by
      exact D.mem_positiveRootGroups_of_mem_unipotent_of_smul_apartmentMap_eq
        hG hi x ν hν hU (D.mem_reducedFixer.mp hg.2)
    have hsemP := selectedRootDepthSubgroup_le_semigroupSubgroup hT
      x.isValuation P 0 hdepth
    have hsemPA : g ∈ (RelativeRoot.semigroupSubgroup
        (AutomorphicAction.conjugation i) (P ⊓ A)).carrier (Over.mk (𝟙 _)) := by
      rw [← RelativeRoot.semigroupSubgroup_inf_eq hT
        (AutomorphicAction.conjugation i) P A hP]
      exact ⟨hsemP, hg.1⟩
    have hselected : g ∈ selectedRootDepthSubgroup x.isValuation (P ⊓ A) 0 := by
      rw [← selectedRootDepthSubgroup_inf_semigroup_eq hT hE x.isValuation
        P (P ⊓ A) hP inf_le_left ν (fun _ _ ha => ha) 0]
      exact ⟨hdepth, hsemPA⟩
    have hle : selectedRootDepthSubgroup x.isValuation (P ⊓ A) 0 ≤
        selectedRootDepthSubgroup x.isValuation A 0 := by
      refine iSup_le fun a => ?_
      exact le_iSup (fun b : {b : characterLattice T |
        b ∈ relativeRoots i ∧ b ∈ A} =>
          x.isValuation.filtrationSubgroup b.val 0)
        ⟨a.val, a.property.1, a.property.2.2⟩
    exact hle hselected
  · apply le_inf
    · exact selectedRootDepthSubgroup_le_semigroupSubgroup hT x.isValuation A 0
    · refine iSup_le fun a => ?_
      exact (D.filtration_le_sharpFixer x a.property.1).trans
        (D.sharpFixer_le_reducedFixer x)

/-- A full apartment-point fixer intersects an actual coarser root group in
the canonical restricted depth-zero subgroup. -/
theorem restrictedRootGroupPoints_inf_reducedFixer_eq_depthZero
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    (f : S ⟶ T) (a : characterLattice S) (ha : a ≠ 0)
    (x : D.Apartment) :
    rootGroupPoints (CommGroupScheme.groupHom f ≫ i) a ⊓
        D.reducedFixer (D.apartmentMap x) =
      torusRestrictedRootDepthSubgroup x.isValuation f a 0 := by
  let : Smooth G.X.hom := hG.smooth
  have hT := hi.isSplitSubtorus.1
  obtain ⟨n, hn, ν, hν⟩ := hS.exists_pairing_eq_pos ha
  have hνpos : 0 < latticePairing S a ν := by
    rw [hν]
    exact_mod_cast hn
  rw [show rootGroupPoints (CommGroupScheme.groupHom f ≫ i) a =
    (RelativeRoot.semigroupSubgroup (AutomorphicAction.conjugation i)
      (RelativeRoot.characterSemigroupPreimage f
        (RelativeRoot.cyclicTail a 1))).carrier (Over.mk (𝟙 _)) by
      exact congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _)))
        (RelativeRoot.subgroup_comp_torusHom_eq_semigroupSubgroup hS hT f i a ha)]
  rw [D.semigroupPoints_inf_reducedFixer_eq_selectedRootDepth hG hi hE _
    (RelativeRoot.zero_notMem_characterSemigroupPreimage_cyclicTail hS f a ha)
    (ν ≫ f) (fun χ _ hχ =>
      latticePairing_pos_of_mem_torusRestriction f a ν hνpos hχ) x]
  rw [torusRestrictedRootDepthSubgroup_eq_selectedRootDepthSubgroup
    x.isValuation f a ν (ne_of_gt hνpos) 0]
  congr 1
  ext χ
  simp [torusRestrictionDepth]

/-- The comparison as a multiplicative equivalence of the original point
subgroups, preserving each ambient group element. -/
def restrictedRootFixerEquivDepthZero
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    (f : S ⟶ T) (a : characterLattice S) (ha : a ≠ 0)
    (x : D.Apartment) :
    (rootGroupPoints (CommGroupScheme.groupHom f ≫ i) a ⊓
      D.reducedFixer (D.apartmentMap x) : Subgroup (rationalPoints G)) ≃*
      torusRestrictedRootDepthSubgroup x.isValuation f a 0 :=
  MulEquiv.subgroupCongr
    (D.restrictedRootGroupPoints_inf_reducedFixer_eq_depthZero hG hi hS hE f a ha x)

@[simp] theorem restrictedRootFixerEquivDepthZero_coe
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    (f : S ⟶ T) (a : characterLattice S) (ha : a ≠ 0)
    (x : D.Apartment)
    (g : (rootGroupPoints (CommGroupScheme.groupHom f ≫ i) a ⊓
      D.reducedFixer (D.apartmentMap x) : Subgroup (rationalPoints G))) :
    (D.restrictedRootFixerEquivDepthZero hG hi hS hE f a ha x g :
      rationalPoints G) = g :=
  rfl

end KPApartmentData

end Langlands.Geometry.Building
