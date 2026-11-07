import Langlands.LocalFactor.Ramification.Herbrand.AbsoluteProof
import Langlands.Galois.Local.AbsoluteProof
import Langlands.LocalField.Normalization.Proof

/-!
# Absolute upper ramification: inertia and wild inertia

The absolute upper group of index `0` is the spectral-closure inertia group for
every local-field realization of the base, and the Krull closure of the union of
the absolute upper groups of positive index is the intersection of the
preimages of the first lower groups of all actual finite Galois subfields.
-/

noncomputable section

namespace Langlands.Ramification.HerbrandBridge

open _root_.Langlands.Ramification.Padic

universe u uK uL

section Units

open IsLocalRing

/-- An element of a subring of a field is a unit exactly when it is nonzero with
inverse in the subring. -/
theorem subring_isUnit_iff {K : Type*} [Field K] (A : Subring K) (a : A) :
    IsUnit a ↔ (a : K) ≠ 0 ∧ (a : K)⁻¹ ∈ A := by
  constructor
  · rintro ⟨w, rfl⟩
    have h : ((w : A) : K) * ((w⁻¹ : Aˣ) : A) = 1 := congrArg Subtype.val w.mul_inv
    refine ⟨left_ne_zero_of_mul_eq_one h, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right h]
    exact ((w⁻¹ : Aˣ) : A).property
  · rintro ⟨h0, hi⟩
    exact IsUnit.of_mul_eq_one (⟨_, hi⟩ : A) (Subtype.ext (mul_inv_cancel₀ h0))

/-- The maximal ideal of a local subring of a field, described inside the field. -/
theorem subring_mem_maximalIdeal_iff {K : Type*} [Field K] (A : Subring K) [IsLocalRing A]
    (a : A) : a ∈ maximalIdeal A ↔ (a : K) = 0 ∨ (a : K)⁻¹ ∉ A := by
  rw [mem_maximalIdeal, mem_nonunits_iff, subring_isUnit_iff]
  tauto

/-- The same unit criterion for a valuation subring. -/
theorem valuationSubring_isUnit_iff {K : Type*} [Field K] (A : ValuationSubring K) (a : A) :
    IsUnit a ↔ (a : K) ≠ 0 ∧ (a : K)⁻¹ ∈ A := by
  constructor
  · rintro ⟨w, rfl⟩
    have h : ((w : A) : K) * ((w⁻¹ : Aˣ) : A) = 1 := congrArg Subtype.val w.mul_inv
    refine ⟨left_ne_zero_of_mul_eq_one h, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right h]
    exact ((w⁻¹ : Aˣ) : A).property
  · rintro ⟨h0, hi⟩
    exact IsUnit.of_mul_eq_one (⟨_, hi⟩ : A) (Subtype.ext (mul_inv_cancel₀ h0))

/-- Equality of residues in a valuation subring, described inside the field. -/
theorem valuationSubring_residue_eq_iff {K : Type*} [Field K] (A : ValuationSubring K)
    (a b : A) : residue A a = residue A b ↔ (a : K) - b = 0 ∨ ((a : K) - b)⁻¹ ∉ A := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    valuationSubring_isUnit_iff]
  change ¬(((a : K) - b) ≠ 0 ∧ ((a : K) - b)⁻¹ ∈ A) ↔ _
  tauto

end Units

section Integrality

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- Integrality over the p-adic integers of an element of the fixed algebraic closure. -/
def IsPadicIntegral (x : AlgebraicClosure F.Carrier) : Prop :=
  IsIntegral (ValuativeRel.valuation (Padic p)).integer x

/-- The spectral closure integers of any realization are the p-adic integral elements. -/
theorem mem_closureIntegers_iff (T : F.TopologicalData) (x : AlgebraicClosure F.Carrier) :
    x ∈ F.closureIntegers T ↔ IsPadicIntegral F x := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  change x ∈ LocalGalois.closureIntegers F.Carrier ↔ _
  rw [← LocalGalois.closureIntegers_integral]
  let A := (ValuativeRel.valuation (Padic p)).integer
  let := T.integerAlgebra
  have : Module.Finite A T.Integers := T.integers_finite
  have : IsScalarTower A (ValuativeRel.valuation F.Carrier).integer
      (AlgebraicClosure F.Carrier) := IsScalarTower.of_algebraMap_eq fun a =>
    IsScalarTower.algebraMap_apply (Padic p) F.Carrier (AlgebraicClosure F.Carrier) (a : Padic p)
  constructor
  · intro h
    exact isIntegral_trans (R := A) x h
  · intro h
    exact IsIntegral.tower_top (A := (ValuativeRel.valuation F.Carrier).integer) h

/-- The canonical integers of an actual finite Galois subfield are its p-adic integral
elements. -/
theorem mem_canonicalIntegers_iff
    (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)) (x : L) :
    x ∈ (absoluteFiniteExtension F L).canonicalTopologicalData.Integers ↔
      IsPadicIntegral F (x : AlgebraicClosure F.Carrier) := by
  rw [← (absoluteFiniteExtension F L).canonicalTopologicalData.isIntegral_iff_mem_integers x]
  let A := (ValuativeRel.valuation (Padic p)).integer
  let := Algebra.compHom (absoluteFiniteExtension F L).Carrier (algebraMap A (Padic p))
  let f : (absoluteFiniteExtension F L).Carrier →ₐ[A] AlgebraicClosure F.Carrier :=
    { toRingHom := algebraMap L (AlgebraicClosure F.Carrier)
      commutes' := fun _ => rfl }
  exact (isIntegral_algHom_iff f Subtype.val_injective).symm

/-- Maximal-ideal membership in the canonical integers of a finite Galois subfield,
described by p-adic integrality in the algebraic closure. -/
theorem canonical_mem_maximalIdeal_iff
    (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (a : (absoluteFiniteExtension F L).canonicalTopologicalData.Integers) :
    a ∈ IsLocalRing.maximalIdeal (absoluteFiniteExtension F L).canonicalTopologicalData.Integers ↔
      (((a : L) : AlgebraicClosure F.Carrier)) = 0 ∨
        ¬IsPadicIntegral F ((a : L) : AlgebraicClosure F.Carrier)⁻¹ := by
  rw [subring_mem_maximalIdeal_iff, mem_canonicalIntegers_iff]
  have h0 : ((a : L) : AlgebraicClosure F.Carrier) = 0 ↔ (a : L) = 0 := by
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      rw [h]
      rfl
  rw [h0]
  rfl

/-- Restriction to a finite Galois subfield, read in the algebraic closure. -/
theorem absoluteFiniteRestriction_apply_coe
    (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (σ : Field.absoluteGaloisGroup F.Carrier) (x : L) :
    ((absoluteFiniteRestriction F L σ x : L) : AlgebraicClosure F.Carrier) =
      AlgEquiv.toAlgHom σ x :=
  σ.restrictNormal_commutes L x

/-- Inertia of the spectral closure for any realization, by p-adic integrality. -/
theorem mem_absoluteInertia_iff (T : F.TopologicalData)
    (σ : Field.absoluteGaloisGroup F.Carrier) :
    σ ∈ F.absoluteInertia T ↔ ∀ x : AlgebraicClosure F.Carrier, IsPadicIntegral F x →
      AlgEquiv.toAlgHom σ x - x = 0 ∨ ¬IsPadicIntegral F (AlgEquiv.toAlgHom σ x - x)⁻¹ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  change σ ∈ LocalGalois.absoluteInertia F.Carrier ↔ _
  rw [LocalGalois.absoluteInertia_mem]
  constructor
  · intro h x hx
    have h1 := (valuationSubring_residue_eq_iff _ _ _).mp
      (h ⟨x, (mem_closureIntegers_iff F T x).mpr hx⟩)
    rw [← mem_closureIntegers_iff F T]
    exact h1
  · intro h x
    apply (valuationSubring_residue_eq_iff _ _ _).mpr
    have h1 := h x ((mem_closureIntegers_iff F T x).mp x.property)
    rw [← mem_closureIntegers_iff F T] at h1
    exact h1

/-- Inertia of an actual finite Galois subfield, by p-adic integrality. -/
theorem mem_canonicalInertia_iff
    (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (τ : Gal(L/F.Carrier)) :
    τ ∈ inertia (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier ↔
      ∀ x : L, IsPadicIntegral F (x : AlgebraicClosure F.Carrier) →
        ((τ x : L) : AlgebraicClosure F.Carrier) - x = 0 ∨
          ¬IsPadicIntegral F (((τ x : L) : AlgebraicClosure F.Carrier) - x)⁻¹ := by
  rw [← lowerRamificationGroup_zero,
    _root_.Langlands.Ramification.Padic.mem_lowerRamificationGroup]
  simp only [zero_add, pow_one]
  constructor
  · intro h x hx
    exact (canonical_mem_maximalIdeal_iff F L _).mp (h ⟨x, (mem_canonicalIntegers_iff F L x).mpr hx⟩)
  · intro h x
    exact (canonical_mem_maximalIdeal_iff F L _).mpr
      (h x ((mem_canonicalIntegers_iff F L x).mp x.property))

end Integrality

section Finite

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p} (T : F.TopologicalData)
  (K : Type uK) [Field K] [Algebra (Padic p) K] [Algebra K F.Carrier]
  [IsScalarTower (Padic p) K F.Carrier]

/-- The union of the finite upper groups of positive index is the first lower group. -/
theorem iSup_upperRamificationGroup_pos :
    ⨆ (w : ℝ) (_ : 0 < w), Padic.upperRamificationGroup T K w =
      Padic.lowerRamificationGroup T K 1 := by
  have h1 : lowerRamificationGroupReal T K 1 = Padic.lowerRamificationGroup T K 1 := by
    have h := lowerRamificationGroupReal_nat T K 1
    rwa [Nat.cast_one] at h
  have h2 : lowerRamificationGroupInt T K 1 = Padic.lowerRamificationGroup T K 1 := by
    rw [← h1, ← lowerRamificationGroupReal_int T K 1, Int.cast_one]
  apply le_antisymm
  · refine iSup₂_le fun w hw => ?_
    rw [upperRamificationGroup_eq_lower, ← h2]
    apply lowerRamificationGroupInt_antitone T K
    have := Int.ceil_pos.mpr (herbrandPsi_pos T K hw)
    omega
  · refine le_iSup₂_of_le (herbrandPhi T K 1) (herbrandPhi_pos T K one_pos) ?_
    rw [upperRamificationGroup_phi, h1]

end Finite

section Absolute

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- A closed subgroup of the absolute Galois group is the intersection of the preimages
of its images in all actual finite Galois quotients. -/
theorem iInf_comap_map_absoluteFiniteRestriction
    (H : Subgroup (Field.absoluteGaloisGroup F.Carrier))
    (hH : IsClosed (H : Set (Field.absoluteGaloisGroup F.Carrier))) :
    ⨅ L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier),
      (H.map (absoluteFiniteRestriction F L).toMonoidHom).comap
        (absoluteFiniteRestriction F L).toMonoidHom = H := by
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  apply le_antisymm _ (le_iInf fun L => Subgroup.le_comap_map _ H)
  intro σ hσ
  have hfix : (IntermediateField.fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField
      (⟨H, hH⟩ : ClosedSubgroup Gal(AlgebraicClosure F.Carrier/F.Carrier))
  rw [← hfix]
  apply (IntermediateField.mem_fixingSubgroup_iff _ σ).mpr
  intro x hx
  let L := FiniteGaloisIntermediateField.adjoin F.Carrier ({x} : Set (AlgebraicClosure F.Carrier))
  have hxL : x ∈ L.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin F.Carrier _ rfl
  obtain ⟨τ, hτ, he⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp (Subgroup.mem_iInf.mp hσ L))
  have h1 := absoluteFiniteRestriction_apply_coe F L σ ⟨x, hxL⟩
  have h2 := absoluteFiniteRestriction_apply_coe F L τ ⟨x, hxL⟩
  have he' : absoluteFiniteRestriction F L τ = absoluteFiniteRestriction F L σ := he
  rw [he'] at h2
  have h3 : AlgEquiv.toAlgHom τ x = x := (IntermediateField.mem_fixedField_iff _ _).mp hx τ hτ
  exact h1.symm.trans (h2.trans h3)

/-- The absolute upper group of index zero is the spectral-closure inertia group
of every local-field realization of the base. -/
theorem absoluteUpperInertia (T : F.TopologicalData) : AbsoluteUpperInertia F T := by
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have : IsGalois F.Carrier (AlgebraicClosure F.Carrier) := ⟨⟩
  ext σ
  rw [mem_absoluteUpperRamificationGroup_iff, mem_absoluteInertia_iff F T]
  simp only [canonicalUpperRamificationGroup,
    _root_.Langlands.Ramification.Padic.upperRamificationGroup_zero]
  constructor
  · intro h x hx
    let L := FiniteGaloisIntermediateField.adjoin F.Carrier ({x} : Set (AlgebraicClosure F.Carrier))
    have hxL : x ∈ L.toIntermediateField :=
      FiniteGaloisIntermediateField.subset_adjoin F.Carrier _ rfl
    have h1 := (mem_canonicalInertia_iff F L _).mp (h L) ⟨x, hxL⟩ hx
    rwa [absoluteFiniteRestriction_apply_coe] at h1
  · intro h L
    apply (mem_canonicalInertia_iff F L _).mpr
    intro x hx
    rw [absoluteFiniteRestriction_apply_coe]
    exact h x hx

/-- The canonical specialization of the inertia clause. -/
theorem absoluteUpperCanonicalInertia : AbsoluteUpperCanonicalInertia F :=
  absoluteUpperInertia F F.canonicalTopologicalData

/-- The Krull closure of the union of the absolute upper groups of positive index is
the finite-quotient description of wild inertia. -/
theorem absoluteUpperWildInertia : AbsoluteUpperWildInertia F := by
  unfold AbsoluteUpperWildInertia
  rw [← iInf_comap_map_absoluteFiniteRestriction F _ (Subgroup.isClosed_topologicalClosure _)]
  refine iInf_congr fun L => ?_
  rw [absoluteUpperClosedRightImage F L 0 (by norm_num)]
  simp only [canonicalUpperRamificationGroup]
  rw [iSup_upperRamificationGroup_pos]

/-- The complete absolute family: all seven clauses for every prime and every p-adic
field in the universe `u`. -/
theorem absoluteHerbrandArithmetic : AbsoluteHerbrandArithmetic.{u} := fun _ _ F =>
  ⟨absoluteUpperFiniteImage F, absoluteUpperInertia F, absoluteUpperCanonicalInertia F,
    absoluteUpperEndpoint F, absoluteUpperLeftContinuity F, absoluteUpperClosedRightImage F,
    absoluteUpperWildInertia F⟩

end Absolute

end Langlands.Ramification.HerbrandBridge
