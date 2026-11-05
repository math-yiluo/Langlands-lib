import Langlands.GroupScheme.Reductive.RootDatumStatement
import Langlands.GroupScheme.Rational.RelativeWeylChamberGeneration
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Supplied root data and the integral normalizer image -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  {J : Type*} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}

namespace IsRootDatumOf

variable (hP : IsRootDatumOf i P)

include hP

/-- Each reflection of a supplied root datum is realized by an actual rational
normalizing point. -/
theorem exists_reflectionRepresentative (α : J) :
    ∃ n : normalizerPoints i, weylAction i n = P.reflection α := by
  obtain ⟨n, σ, hn, hσ⟩ := hP.2.2 α
  let n' : normalizerPoints i := ⟨n, σ, hn⟩
  refine ⟨n', ?_⟩
  change characterAut (normalizingAut i n') = P.reflection α
  have he : normalizingAut i n' = σ :=
    (isNormalizingPoint_normalizingAut i n').unique i hn
  exact (congrArg characterAut he).trans hσ

/-- Choose a rational normalizing representative of an abstract reflection. -/
def reflectionRepresentative (α : J) : normalizerPoints i :=
  Classical.choose (hP.exists_reflectionRepresentative α)

theorem weylAction_reflectionRepresentative (α : J) :
    weylAction i (hP.reflectionRepresentative α) = P.reflection α :=
  Classical.choose_spec (hP.exists_reflectionRepresentative α)

/-- The abstract Weyl image is always contained in the actual integral
normalizer image; no reductivity or finite-root premise is needed. -/
theorem abstractWeylImage_le :
    P.weylGroup.map (RootPairing.Equiv.weightHom P) ≤ weylImage i := by
  rw [← MonoidHom.domRestrict_range, RootPairing.range_weylGroup_weightHom,
    Subgroup.closure_le]
  rintro _ ⟨α, rfl⟩
  exact ⟨hP.reflectionRepresentative α, hP.weylAction_reflectionRepresentative α⟩

/-- Choose the index of an actual root in the supplied datum. -/
def relativeRootIndex (α : relativeRoots i) : J :=
  Classical.choose (show ∃ j : J, P.root j = α.val from by
    rw [← Set.mem_range, hP.2.1]
    exact α.property)

omit [Mono i.hom.hom.left] in
theorem root_relativeRootIndex (α : relativeRoots i) :
    P.root (hP.relativeRootIndex α) = α.val :=
  Classical.choose_spec (show ∃ j : J, P.root j = α.val from by
    rw [← Set.mem_range, hP.2.1]
    exact α.property)

/-- Supplied root-datum witnesses give the integral reflection data on the
actual character-valued roots. This does not assert their existence. -/
def relativeRootReflectionData : RelativeRootReflectionData i where
  coroot α := P.coroot (hP.relativeRootIndex α)
  representative α := hP.reflectionRepresentative (hP.relativeRootIndex α)
  pair_self α := by
    rw [← hP.root_relativeRootIndex α, ← hP.1]
    exact P.root_coroot_two (hP.relativeRootIndex α)
  action α χ := by
    rw [hP.weylAction_reflectionRepresentative, RootPairing.reflection_apply]
    change χ - P.toLinearMap χ (P.coroot (hP.relativeRootIndex α)) •
      P.root (hP.relativeRootIndex α) = _
    rw [hP.1, hP.root_relativeRootIndex]

omit [Mono i.hom.hom.left] in
/-- Finiteness of the actual roots implies finiteness of the supplied datum's
index type, because its root map is an embedding with that exact range. -/
theorem finite_index_of_finite_relativeRoots (hfinite : (relativeRoots i).Finite) : Finite J := by
  let := hfinite.to_subtype
  let f : J → relativeRoots i := fun j =>
    ⟨P.root j, by rw [relativeRoots_eq_roots, ← hP.2.1]; exact Set.mem_range_self j⟩
  exact Finite.of_injective f (fun a b hab => P.root.injective (congrArg Subtype.val hab))

/-- A trivial positive-root stabilizer at one generic cocharacter supplies
equality on the full integral character lattice, via actual quotient generation. -/
theorem weylImage_eq_of_positive_stabilizer
    (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (hstab : HasTrivialPositiveRootStabilizer i ν) :
    weylImage i = P.weylGroup.map (RootPairing.Equiv.weightHom P) := by
  let D := hP.relativeRootReflectionData
  let H := P.weylGroup.map (RootPairing.Equiv.weightHom P)
  have hrep (α : relativeRoots i) :
      relativeWeylCharacterAction i (QuotientGroup.mk (D.representative α)) ∈ H := by
    change weylAction i (hP.reflectionRepresentative (hP.relativeRootIndex α)) ∈ H
    rw [hP.weylAction_reflectionRepresentative]
    exact ⟨RootPairing.Equiv.reflection P (hP.relativeRootIndex α),
      P.reflection_mem_weylGroup _, RootPairing.Equiv.reflection_weightEquiv P _⟩
  have hle : Subgroup.closure (Set.range fun α : relativeRoots i =>
      relativeWeylCharacterAction i (QuotientGroup.mk (D.representative α))) ≤ H := by
    rw [Subgroup.closure_le]
    rintro _ ⟨α, rfl⟩
    exact hrep α
  have hgen := congrArg (Subgroup.map (relativeWeylCharacterAction i))
    (D.closure_representatives_eq_top_of_positive_stabilizer hT hfinite hν hstab)
  rw [MonoidHom.map_closure, ← Set.range_comp, Subgroup.map_top] at hgen
  change Subgroup.closure (Set.range fun α : relativeRoots i =>
    relativeWeylCharacterAction i (QuotientGroup.mk (D.representative α))) = _ at hgen
  rw [hgen] at hle
  apply le_antisymm ?_ hP.abstractWeylImage_le
  rintro _ ⟨n, rfl⟩
  exact hle ⟨QuotientGroup.mk n, rfl⟩

/-- With a supplied positive-root stabilizer theorem, both exact comparison
clauses follow, including the kernel on all characters. -/
theorem weylImage_and_ker_of_positive_stabilizer
    (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (hstab : HasTrivialPositiveRootStabilizer i ν) :
    weylImage i = P.weylGroup.map (RootPairing.Equiv.weightHom P) ∧
      (weylAction i).ker = (centralizerPoints i).subgroupOf (normalizerPoints i) :=
  ⟨hP.weylImage_eq_of_positive_stabilizer hT hfinite hν hstab, hT.weylAction_ker i⟩

end IsRootDatumOf

end Langlands.GroupScheme
