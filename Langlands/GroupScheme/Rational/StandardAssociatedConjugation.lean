import Langlands.GroupScheme.Rational.StandardRestrictedConjugation
import Langlands.GroupScheme.Rational.StandardAssociatedParabolicTransportStatement
import Langlands.GroupScheme.Rational.CoxeterStandardCocharacter
import Langlands.GroupScheme.Rational.SimpleReflectionConjugacy

/-! # Associated standard families under actual longest normalizer lifts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  (ν : cocharacterLattice T)
  [Fintype (SimpleRoot i ν)] [Fintype (relativeWeylGroup i)]
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : CoxeterSystem CM (relativeWeylGroup i))
  (h : IsRelativeWeylCoxeterRealization i ν cs)

include h

/-- The associated simple-label equivalence is the actual positive
character action of the longest representative. -/
theorem schemeWeylCharacterAction_associatedSimpleEquiv
    (J : Finset (SimpleRoot i ν)) (a : associatedSubset cs J) :
    schemeWeylCharacterAction i (longestRep cs J) (a : SimpleRoot i ν).val =
      (associatedSimpleEquiv cs J a : SimpleRoot i ν).val := by
  have hpos : schemeWeylCharacterAction i (longestRep cs J)
      (a : SimpleRoot i ν).val ∈ positiveRelativeRoots i ν := by
    apply (h.2.2.1 _ (a : SimpleRoot i ν)).mp
    apply (mem_positiveSimpleSet cs _ _).mp
    rw [positiveSimpleSet_longestRep]
    exact a.property
  exact h.root_eq_of_conj_simple _ _ _ hpos (associatedSimpleEquiv_conj cs J a)

/-- The full associated simple-root set has exactly the expected character image. -/
theorem schemeWeylCharacterAction_image_associatedSubset
    (J : Finset (SimpleRoot i ν)) :
    schemeWeylCharacterAction i (longestRep cs J) '' rootSet i ν (associatedSubset cs J) =
      rootSet i ν J := by
  ext α
  constructor
  · rintro ⟨β, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨associatedSimpleEquiv cs J ⟨a, ha⟩,
      (associatedSimpleEquiv cs J ⟨a, ha⟩).property,
      (schemeWeylCharacterAction_associatedSimpleEquiv i ν cs h J ⟨a, ha⟩).symm⟩
  · rintro ⟨b, hb, rfl⟩
    let a := (associatedSimpleEquiv cs J).symm ⟨b, hb⟩
    refine ⟨(a : SimpleRoot i ν).val, ⟨a, a.property, rfl⟩, ?_⟩
    rw [schemeWeylCharacterAction_associatedSimpleEquiv i ν cs h]
    exact congrArg (fun x : J => (x : SimpleRoot i ν).val)
      ((associatedSimpleEquiv cs J).apply_symm_apply ⟨b, hb⟩)

/-- Every associated finite subset has the exact character image prescribed
by the published finite-subset equivalence. -/
theorem schemeWeylCharacterAction_image_associatedFinsetEquiv
    (J : Finset (SimpleRoot i ν)) (I : Finset (associatedSubset cs J)) :
    schemeWeylCharacterAction i (longestRep cs J) ''
        rootSet i ν (I.map (Function.Embedding.subtype (· ∈ associatedSubset cs J))) =
      rootSet i ν
        ((associatedFinsetEquiv cs J I).map (Function.Embedding.subtype (· ∈ J))) := by
  simp only [rootSet, associatedFinsetEquiv, Equiv.finsetCongr_apply,
    Finset.coe_map, Set.image_image]
  apply Set.image_congr
  intro a _
  exact schemeWeylCharacterAction_associatedSimpleEquiv i ν cs h J a

/-- Both character images use every supplied lift of the specified longest
representative, with no change of normalizer point. -/
theorem weylAction_image_associatedStandardFamily
    (J : Finset (SimpleRoot i ν)) (n : normalizerPoints i)
    (hn : QuotientGroup.mk n = longestRep cs J)
    (I : Finset (associatedSubset cs J)) :
    (weylAction i n ''
        rootSet i ν (I.map (Function.Embedding.subtype (· ∈ associatedSubset cs J))) =
      rootSet i ν
        ((associatedFinsetEquiv cs J I).map (Function.Embedding.subtype (· ∈ J)))) ∧
    (weylAction i n '' rootSet i ν (associatedSubset cs J) = rootSet i ν J) := by
  rw [← schemeWeylCharacterAction_mk i n, hn]
  exact ⟨schemeWeylCharacterAction_image_associatedFinsetEquiv i ν cs h J I,
    schemeWeylCharacterAction_image_associatedSubset i ν cs h J⟩

/-- The two literal restricted standard families conjugate on every test
scheme under the same actual longest normalizer lift. -/
theorem associatedStandardSubgroups_eq_comap
    (J : Finset (SimpleRoot i ν)) (n : normalizerPoints i)
    (hn : QuotientGroup.mk n = longestRep cs J)
    (I : Finset (associatedSubset cs J)) :
    (restrictedStandardParabolic i ν (associatedSubset cs J) I =
      (restrictedStandardParabolic i ν J (associatedFinsetEquiv cs J I)).comap
        (G.innerIso (n : rationalPoints G)).hom) ∧
    (restrictedStandardUnipotent i ν (associatedSubset cs J) I =
      (restrictedStandardUnipotent i ν J (associatedFinsetEquiv cs J I)).comap
        (G.innerIso (n : rationalPoints G)).hom) := by
  obtain ⟨hI, hJ⟩ := weylAction_image_associatedStandardFamily i ν cs h J n hn I
  exact restrictedStandardSubgroups_eq_comap_of_character_images i ν (Set.toFinite _)
    ((rootSet_subset_iff i ν _ _).mpr (fun _ ha => Finset.property_of_mem_map_subtype I ha))
    ((rootSet_subset_iff i ν _ _).mpr
      (fun _ ha => Finset.property_of_mem_map_subtype (associatedFinsetEquiv cs J I) ha))
    (h.exists_standardCocharacter_finset _) (h.exists_standardCocharacter_finset _)
    n hI hJ

/-- Actual conjugation on the associated standard parabolic, over any test scheme. -/
def associatedStandardParabolicConjEquiv
    (J : Finset (SimpleRoot i ν)) (n : normalizerPoints i)
    (hn : QuotientGroup.mk n = longestRep cs J)
    (I : Finset (associatedSubset cs J)) (U : Over (Spec (CommRingCat.of k))) :
    (restrictedStandardParabolic i ν (associatedSubset cs J) I).carrier U ≃*
      (restrictedStandardParabolic i ν J (associatedFinsetEquiv cs J I)).carrier U :=
  restrictedStandardParabolicConjEquiv i ν (Set.toFinite _)
    ((rootSet_subset_iff i ν _ _).mpr (fun _ ha => Finset.property_of_mem_map_subtype I ha))
    ((rootSet_subset_iff i ν _ _).mpr
      (fun _ ha => Finset.property_of_mem_map_subtype (associatedFinsetEquiv cs J I) ha))
    (h.exists_standardCocharacter_finset _) (h.exists_standardCocharacter_finset _) n
    (weylAction_image_associatedStandardFamily i ν cs h J n hn I).1
    (weylAction_image_associatedStandardFamily i ν cs h J n hn I).2 U

/-- Actual conjugation on the associated standard radical, over any test scheme. -/
def associatedStandardUnipotentConjEquiv
    (J : Finset (SimpleRoot i ν)) (n : normalizerPoints i)
    (hn : QuotientGroup.mk n = longestRep cs J)
    (I : Finset (associatedSubset cs J)) (U : Over (Spec (CommRingCat.of k))) :
    (restrictedStandardUnipotent i ν (associatedSubset cs J) I).carrier U ≃*
      (restrictedStandardUnipotent i ν J (associatedFinsetEquiv cs J I)).carrier U :=
  restrictedStandardUnipotentConjEquiv i ν (Set.toFinite _)
    ((rootSet_subset_iff i ν _ _).mpr (fun _ ha => Finset.property_of_mem_map_subtype I ha))
    ((rootSet_subset_iff i ν _ _).mpr
      (fun _ ha => Finset.property_of_mem_map_subtype (associatedFinsetEquiv cs J I) ha))
    (h.exists_standardCocharacter_finset _) (h.exists_standardCocharacter_finset _) n
    (weylAction_image_associatedStandardFamily i ν cs h J n hn I).1
    (weylAction_image_associatedStandardFamily i ν cs h J n hn I).2 U

section Formulas

variable (J : Finset (SimpleRoot i ν)) (n : normalizerPoints i)
  (hn : QuotientGroup.mk n = longestRep cs J)
  (I : Finset (associatedSubset cs J)) (U : Over (Spec (CommRingCat.of k)))

/-- The parabolic equivalence uses the original normalizer point. -/
@[simp] theorem associatedStandardParabolicConjEquiv_apply
    (x : (restrictedStandardParabolic i ν (associatedSubset cs J) I).carrier U) :
    (associatedStandardParabolicConjEquiv i ν cs h J n hn I U x : U ⟶ G.X) =
      G.constantPoint n U * x.1 * (G.constantPoint n U)⁻¹ :=
  comp_innerIso_hom G n U x.1

/-- The radical equivalence uses the original normalizer point. -/
@[simp] theorem associatedStandardUnipotentConjEquiv_apply
    (x : (restrictedStandardUnipotent i ν (associatedSubset cs J) I).carrier U) :
    (associatedStandardUnipotentConjEquiv i ν cs h J n hn I U x : U ⟶ G.X) =
      G.constantPoint n U * x.1 * (G.constantPoint n U)⁻¹ :=
  comp_innerIso_hom G n U x.1

/-- The inverse parabolic equivalence conjugates by the inverse of the same point. -/
@[simp] theorem associatedStandardParabolicConjEquiv_symm_apply
    (x : (restrictedStandardParabolic i ν J (associatedFinsetEquiv cs J I)).carrier U) :
    ((associatedStandardParabolicConjEquiv i ν cs h J n hn I U).symm x : U ⟶ G.X) =
      (G.constantPoint n U)⁻¹ * x.1 * G.constantPoint n U := by
  change x.1 ≫ (G.innerIso (n : rationalPoints G)).inv.hom.hom = _
  rw [← G.innerIso_inv_hom, comp_innerIso_hom, G.constantPoint_inv, inv_inv]

/-- The inverse radical equivalence conjugates by the inverse of the same point. -/
@[simp] theorem associatedStandardUnipotentConjEquiv_symm_apply
    (x : (restrictedStandardUnipotent i ν J (associatedFinsetEquiv cs J I)).carrier U) :
    ((associatedStandardUnipotentConjEquiv i ν cs h J n hn I U).symm x : U ⟶ G.X) =
      (G.constantPoint n U)⁻¹ * x.1 * G.constantPoint n U := by
  change x.1 ≫ (G.innerIso (n : rationalPoints G)).inv.hom.hom = _
  rw [← G.innerIso_inv_hom, comp_innerIso_hom, G.constantPoint_inv, inv_inv]

include hn in
/-- For any target-Levi point, inverse conjugation detects membership in
the corresponding standard parabolic and radical. -/
theorem mem_associatedStandardParabolic_unipotent_inv_conj_iff
    (x : U ⟶ G.X) (hx : x ∈ (standardLevi i ν (rootSet i ν J)).carrier U) :
    (x ∈ (standardParabolic i ν
        (rootSet i ν
          ((associatedFinsetEquiv cs J I).map (Function.Embedding.subtype (· ∈ J))))).carrier U ↔
      (G.constantPoint n U)⁻¹ * x * G.constantPoint n U ∈
        (standardParabolic i ν
          (rootSet i ν (I.map (Function.Embedding.subtype (· ∈ associatedSubset cs J))))).carrier U) ∧
    (x ∈ (standardUnipotent i ν
        (rootSet i ν
          ((associatedFinsetEquiv cs J I).map (Function.Embedding.subtype (· ∈ J))))).carrier U ↔
      (G.constantPoint n U)⁻¹ * x * G.constantPoint n U ∈
        (standardUnipotent i ν
          (rootSet i ν (I.map (Function.Embedding.subtype (· ∈ associatedSubset cs J))))).carrier U) :=
  mem_standardParabolic_unipotent_inv_conj_iff_of_character_images i ν (Set.toFinite _)
    ((rootSet_subset_iff i ν _ _).mpr
      (fun _ ha => Finset.property_of_mem_map_subtype I ha))
    ((rootSet_subset_iff i ν _ _).mpr
      (fun _ ha => Finset.property_of_mem_map_subtype (associatedFinsetEquiv cs J I) ha))
    (h.exists_standardCocharacter_finset _) (h.exists_standardCocharacter_finset _) n
    (weylAction_image_associatedStandardFamily i ν cs h J n hn I).1
    (weylAction_image_associatedStandardFamily i ν cs h J n hn I).2 U x hx

end Formulas

end Langlands.GroupScheme
