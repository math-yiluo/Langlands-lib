import Langlands.Representation.Smooth.IrreducibleGrothendieckProof
import Langlands.Representation.Filtration.SimpleSubquotientFactorProof
import Langlands.Representation.Classification.SupercuspidalSupport

/-! Actual irreducible constituent support recovered from exact finite-length classes. -/

noncomputable section

namespace Langlands.SmoothRep

open CategoryTheory IrreducibleGrothendieckProof
open scoped BigOperators

universe uR uG uV

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- Every actual irreducible subquotient of `A` is an actual subquotient of `B`. -/
def HasConstituentSupportIn (A B : SmoothRep.{uR,uG,uV} k G) : Prop :=
  ∀ D : SmoothRep.{uR,uG,uV} k G, D.IsIrreducible →
    IsSubquotient D A → IsSubquotient D B

/-- Actual subquotients inherit finite group-algebra length. -/
theorem hasFiniteLength_of_isSubquotient
    {A D : SmoothRep.{uR,uG,uV} k G} (hA : A.HasFiniteLength)
    (hD : IsSubquotient D A) : D.HasFiniteLength := by
  obtain ⟨X, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp hD
  have hX : X.HasFiniteLength := hA.of_injective
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (hom i)) hi
  exact hX.of_surjective
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (hom q)) hq

/-- The actual irreducible subquotients are precisely the positive
natural composition multiplicities. -/
theorem compositionMultiplicity_pos_iff_isSubquotient
    (M : FiniteLengthObject.{uR,uG,uV} k G)
    (D : SmoothRep.{uR,uG,uV} k G) (hD : D.IsIrreducible) :
    0 < compositionMultiplicity M D ↔ IsSubquotient D M.val := by
  classical
  let s := (chosenSeries M).2.val
  have hs : s.HasSimpleFactors := (chosenSeries M).2.property
  change 0 < s.factorMultiplicity D.obj ↔ IsSubquotient D M.val
  constructor
  · intro h
    obtain ⟨⟨i, ⟨e⟩⟩⟩ := (Nat.card_pos_iff.mp h).1
    refine ⟨s.subrepresentation i.succ,
      ((s.step i.castSucc).lowerInUpper (s.step i.succ) (Discrete.mk PUnit.unit)),
      ⟨?_⟩⟩
    exact mkIso e.symm
  · rintro ⟨S, U, ⟨e⟩⟩
    obtain ⟨i, ⟨f⟩⟩ := simpleSubquotientFactor k G M.val _ s hs D S U hD
      ⟨equivOfIso e⟩
    exact Nat.card_pos_iff.mpr ⟨⟨⟨i, ⟨f.symm⟩⟩⟩, inferInstance⟩

/-- Every nonzero finite-length smooth object has an actual irreducible
subquotient in the same carrier universe. -/
theorem exists_irreducible_subquotient
    (A : SmoothRep.{uR,uG,uV} k G) (hA : A.HasFiniteLength) [Nontrivial A] :
    ∃ D : SmoothRep.{uR,uG,uV} k G, D.IsIrreducible ∧ IsSubquotient D A := by
  classical
  obtain ⟨r, s, hs⟩ := MultiplicityAdditivityProof.exists_series hA
  have hi : Nonempty (Fin r) := by
    by_contra h
    let : IsEmpty (Fin r) := not_nonempty_iff.mp h
    have hz : Subsingleton A.obj :=
      objectRepFiltrationSubsingleton k G A.obj r s (fun i => isEmptyElim i)
    exact not_nontrivial_iff_subsingleton.mpr hz inferInstance
  obtain ⟨i⟩ := hi
  refine ⟨gradedSmooth s i, hs i, s.subrepresentation i.succ,
    ((s.step i.castSucc).lowerInUpper (s.step i.succ) (Discrete.mk PUnit.unit)),
    ⟨?_⟩⟩
  exact mkIso (Representation.Equiv.refl _)

/-- A natural multiple identity in the full exact Grothendieck group
implies containment of actual irreducible constituent support. -/
theorem hasConstituentSupportIn_of_class_natural_multiple
    (A B : FiniteLengthObject.{uR,uG,uV} k G) (N : ℕ)
    (h : FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property =
      N • FiniteLengthGrothendieckGroup.ofRepresentation B.val B.property) :
    HasConstituentSupportIn A.val B.val := by
  intro D hD hDA
  have hpos := (compositionMultiplicity_pos_iff_isSubquotient A D hD).mpr hDA
  by_contra hDB
  have hzero : compositionMultiplicity B D = 0 :=
    Nat.eq_zero_of_not_pos (fun hp =>
      hDB ((compositionMultiplicity_pos_iff_isSubquotient B D hD).mp hp))
  have he := congrArg (fun z => factorMap z (irreducibleIsoClass D hD)) h
  simp only [map_nsmul, factorMap_ofRepresentation, Finsupp.smul_apply,
    compositionFactors_apply, hzero, Nat.cast_zero, smul_zero] at he
  exact (Nat.ne_of_gt hpos) (Int.natCast_eq_zero.mp he)

/-- An exact-class finite sum inherits a common bound on actual
irreducible constituent support. -/
theorem hasConstituentSupportIn_of_class_sum
    {ι : Type*} [Fintype ι]
    (A B : FiniteLengthObject.{uR,uG,uV} k G)
    (M : ι → FiniteLengthObject.{uR,uG,uV} k G)
    (hM : ∀ i, HasConstituentSupportIn (M i).val B.val)
    (h : FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property =
      ∑ i, FiniteLengthGrothendieckGroup.ofRepresentation (M i).val (M i).property) :
    HasConstituentSupportIn A.val B.val := by
  intro D hD hDA
  have hpos := (compositionMultiplicity_pos_iff_isSubquotient A D hD).mpr hDA
  by_contra hDB
  have hzero (i : ι) : compositionMultiplicity (M i) D = 0 :=
    Nat.eq_zero_of_not_pos (fun hp => hDB (hM i D hD
      ((compositionMultiplicity_pos_iff_isSubquotient (M i) D hD).mp hp)))
  have he := congrArg (fun z => factorMap z (irreducibleIsoClass D hD)) h
  simp only [map_sum, factorMap_ofRepresentation, Finsupp.finsetSum_apply,
    compositionFactors_apply, hzero, Nat.cast_zero, Finset.sum_const_zero] at he
  exact (Nat.ne_of_gt hpos) (Int.natCast_eq_zero.mp he)

end Langlands.SmoothRep
