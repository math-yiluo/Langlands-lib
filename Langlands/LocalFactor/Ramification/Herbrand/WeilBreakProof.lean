import Langlands.LocalFactor.Ramification.Herbrand.WeilInertiaProof
import Langlands.Weil.Representation.SubquotientContinuity

/-!
# Weil break labels and finite presentations

The fixed space of an actual upper group of the local Weil group is the fixed space of
the corresponding finite upper group in any finite inertia presentation. Consequently
the last break of a continuous representation is the largest finite upper break, and an
irreducible representation has a single finite upper break, of full multiplicity. The
intrinsic label of a basis class agrees with the last break of every representative.
-/

noncomputable section

namespace Langlands.Ramification.HerbrandBridge

open _root_.Langlands.Ramification.Padic Weil.Local
open VirtualRepresentation.LocalWeil.Ramification

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- Fixed spaces of actual upper groups agree with those of a finite presentation. -/
theorem presentationUpperFixedComparison : PresentationUpperFixedComparison.{u, v} F := by
  intro A P hP r hr
  set T := (absoluteFiniteExtension F P.extension).canonicalTopologicalData
  ext v
  rw [mem_upperFixedSpace]
  change _ ↔ ∀ k : ((Padic.upperRamificationGroup T F.Carrier r).subgroupOf
      (inertia T F.Carrier)), P.representation hP (k : inertia T F.Carrier) v = v
  constructor
  · intro h k
    have hk : ((k : inertia T F.Carrier) : Gal(P.extension/F.Carrier)) ∈
        canonicalUpperRamificationGroup (absoluteFiniteExtension F P.extension) F.Carrier r :=
      Subgroup.mem_subgroupOf.mp k.2
    rw [← absoluteUpperFiniteImage F P.extension r (by linarith)] at hk
    obtain ⟨σ, hσ, he⟩ := Subgroup.mem_map.mp hk
    have hσ0 : σ ∈ F.absoluteInertia F.canonicalTopologicalData := by
      rw [← absoluteUpperCanonicalInertia F]
      exact absoluteUpperRamificationGroup_antitone F hr hσ
    set w : localInertia F := (localInertiaEquiv F).symm ⟨σ, hσ0⟩
    have hwσ : localProjection F (w : localWeilGroup F) = σ :=
      congrArg Subtype.val ((localInertiaEquiv F).apply_symm_apply ⟨σ, hσ0⟩)
    have hk' : (k : inertia T F.Carrier) = weilInertiaRestriction F P.extension w := by
      apply Subtype.ext
      rw [weilInertiaRestriction_coe, hwσ]
      exact he.symm
    rw [hk', FiniteInertiaPresentation.representation_apply]
    apply h
    change localProjection F (w : localWeilGroup F) ∈ absoluteUpperRamificationGroup F r
    rw [hwσ]
    exact hσ
  · intro h w hw
    have hw0 : localProjection F w ∈ absoluteUpperRamificationGroup F 0 :=
      absoluteUpperRamificationGroup_antitone F hr hw
    rw [absoluteUpperCanonicalInertia F] at hw0
    have hwI : w ∈ localInertia F := by
      rw [localInertia_eq_comap F]
      exact hw0
    have hL := absoluteUpperRamificationGroup_le_comap F r P.extension hw
    rw [Subgroup.mem_comap] at hL
    have hmem : weilInertiaRestriction F P.extension ⟨w, hwI⟩ ∈
        (Padic.upperRamificationGroup T F.Carrier r).subgroupOf (inertia T F.Carrier) := by
      rw [Subgroup.mem_subgroupOf, weilInertiaRestriction_coe]
      exact hL
    have := h ⟨_, hmem⟩
    rwa [FiniteInertiaPresentation.representation_apply] at this

/-- Two nonnegative reals with the same strict positive upper bounds are equal. -/
theorem eq_of_forall_pos_lt_iff {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ∀ b : ℝ, 0 < b → (x < b ↔ y < b)) : x = y := by
  apply le_antisymm
  · apply le_of_forall_pos_lt_add
    intro ε hε
    exact (h (y + ε) (by linarith)).mpr (by linarith)
  · apply le_of_forall_pos_lt_add
    intro ε hε
    exact (h (x + ε) (by linarith)).mp (by linarith)

/-- The last break is the maximum of the finite upper-break support. -/
theorem weilLastBreakFiniteMaximum : WeilLastBreakFiniteMaximum.{u, v} F := by
  intro A hA hrank P hP
  set T := (absoluteFiniteExtension F P.extension).canonicalTopologicalData
  have hne : (upperBreakSupport T F.Carrier (P.representation hP)).Nonempty :=
    (upperBreakSupport_nonempty_iff T F.Carrier (P.representation hP)).mpr hrank
  refine ⟨hne, eq_of_forall_pos_lt_iff (lastBreak_nonneg F A)
    (maximumUpperBreak_nonneg T F.Carrier (P.representation hP) hne) fun b hb => ?_⟩
  rw [lastBreak_lt_iff_isTrivialAt F A hA hb, ← upperFixedSpace_eq_top_iff F A,
    presentationUpperFixedComparison F A P hP b hb.le,
    maximumUpperBreak_lt_iff_fixed_eq_top T F.Carrier (P.representation hP) hne hb]

/-- An irreducible representation has positive rank. -/
theorem rank_pos_of_irreducible (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F))
    (h : A.IsIrreducible) : 0 < A.rank := by
  have : IsSimpleModule (MonoidAlgebra ℂ (localWeilGroup F)) A.representation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp h
  have : Nontrivial A :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (localWeilGroup F)) A.representation.asModule
  exact Module.finrank_pos

/-- A Weil-irreducible representation has a single finite upper break, of full rank. -/
theorem weilIrreducibleUpperBreak : WeilIrreducibleUpperBreak.{u, v} F := by
  intro A hA hirr P hP
  set T := (absoluteFiniteExtension F P.extension).canonicalTopologicalData
  set ρ := P.representation hP
  have hrank := rank_pos_of_irreducible F A hirr
  obtain ⟨hne, hmax⟩ := weilLastBreakFiniteMaximum F A hA hrank P hP
  have hmin : minimumUpperBreak T F.Carrier ρ hne = lastBreak F A := by
    apply le_antisymm
    · rw [hmax]
      exact minimumUpperBreak_le_maximumUpperBreak T F.Carrier ρ hne
    · rcases (lastBreak_nonneg F A).eq_or_lt with h0 | hpos
      · rw [← h0]
        exact minimumUpperBreak_nonneg T F.Carrier ρ hne
      · rw [le_minimumUpperBreak_iff_fixed_eq_bot T F.Carrier ρ hne hpos,
          ← presentationUpperFixedComparison F A P hP _ hpos.le]
        exact ((weilIrreduciblePositiveThresholds F A hA hirr).1 _ hpos).mp le_rfl
  have hsupp : upperBreakSupport T F.Carrier ρ = {lastBreak F A} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, fun r hr => le_antisymm ?_ ?_⟩
    · rw [hmax]
      exact maximumUpperBreak_mem T F.Carrier ρ hne
    · rw [hmax]
      exact le_maximumUpperBreak T F.Carrier ρ hne hr
    · rw [← hmin]
      exact minimumUpperBreak_le T F.Carrier ρ hne hr
  refine ⟨?_, hsupp⟩
  ext r
  by_cases hr : r = lastBreak F A
  · subst hr
    rw [Finsupp.single_eq_same]
    have hsum := sum_upperBreakSupport T F.Carrier ρ
    rw [hsupp, Finset.sum_singleton] at hsum
    exact hsum
  · rw [Finsupp.single_apply]
    simp only [show ¬(lastBreak F A = r) from Ne.symm hr, ite_false]
    have hns : r ∉ upperBreakSupport T F.Carrier ρ := by
      rw [hsupp, Finset.mem_singleton]
      exact hr
    exact Finsupp.notMem_support_iff.mp hns

/-- An actual representation equivalence preserves irreducibility. -/
theorem isIrreducible_of_equiv {A B : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)}
    (e : A.Equiv B) (h : A.IsIrreducible) : B.IsIrreducible := by
  have hA := (Representation.irreducible_iff_isSimpleModule_asModule _).mp h
  apply (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ e.toIntertwiningMap)
    e.toLinearEquiv.bijective).mp hA

/-- `A` is a representative of the basis class `b`: its genuine isomorphism class is the
underlying class of `b`. -/
def IsBasisRepresentative (b : VirtualRepresentation.LocalWeil.Basis.{u, v} F)
    (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)) : Prop :=
  FiniteRepresentation.classOf A = VirtualRepresentation.Weil.underlyingClass (localWeilGroup F) b

/-- The intrinsic label of a basis class and the threshold descriptions on every
representative of that class. -/
theorem classBreak_basic (b : VirtualRepresentation.LocalWeil.Basis.{u, v} F)
    (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F))
    (h' : IsBasisRepresentative F b A) :
    (trivialityThresholds F A).Nonempty ∧
    lastBreak F A = breakLabel F b ∧
    A.rank = (b.1 : ℕ) ∧
    (∀ a : ℝ, 0 < a → (a ≤ breakLabel F b ↔ upperFixedSpace F A a = ⊥)) ∧
    (∀ c : ℝ, 0 < c → (breakLabel F b < c ↔ upperFixedSpace F A c = ⊤)) ∧
    (breakLabel F b = 0 ↔ ∀ r : ℝ, 0 < r → IsTrivialAt F A r) := by
  have h : FiniteRepresentation.classOf A =
      VirtualRepresentation.Weil.underlyingClass (localWeilGroup F) b := h'
  set R := (Quotient.out b.2.val).val
  have hR := (Quotient.out b.2.val).property
  have hclass : FiniteRepresentation.classOf R =
      VirtualRepresentation.Weil.underlyingClass (localWeilGroup F) b := by
    change Quotient.mk _ R = FiniteRepresentation.forgetPropertyClass _ b.2.val
    conv_rhs => rw [← Quotient.out_eq b.2.val]
    rfl
  obtain ⟨e⟩ := (FiniteRepresentation.classOf_eq_iff A R).mp (h.trans hclass.symm)
  have hA : A.IsContinuous := (FiniteRepresentation.isContinuous_iff_of_equiv e).mpr hR.1
  have hirr : A.IsIrreducible := isIrreducible_of_equiv F e.symm hR.2
  have hlab : lastBreak F A = breakLabel F b := by
    rw [breakLabel, ← h, classLastBreak_classOf]
  have hrank : A.rank = (b.1 : ℕ) := by
    rw [← FiniteRepresentation.classRank_classOf, h]
    exact b.2.property
  refine ⟨weilTrivialityThresholdsNonempty F A hA, hlab, hrank, ?_, ?_, ?_⟩
  · rw [← hlab]
    exact (weilIrreduciblePositiveThresholds F A hA hirr).1
  · rw [← hlab]
    exact (weilIrreduciblePositiveThresholds F A hA hirr).2
  · rw [← hlab]
    exact weilLastBreakZero F A hA

end Langlands.Ramification.HerbrandBridge
