import Langlands.Representation.Geometric.ClosedSubgroupDefinitions
import Langlands.Representation.Geometric.WeylDefinitions

/-! Replacing representatives in an actual ordered orbit decomposition. -/

noncomputable section

namespace Langlands.Geometric

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (P Q : Subgroup G)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem quotientMap_mem_cosetOrbit_iff (w x : G) :
    Induction.quotientMap P x ∈ cosetOrbit P Q w ↔
      DoubleCoset.mk P Q w⁻¹ = DoubleCoset.mk P Q x := by
  constructor
  · rintro ⟨q, hq⟩
    have hp : x * (w⁻¹ * (q : G))⁻¹ ∈ P :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
    apply DoubleCoset.eq.mpr
    exact ⟨_, hp, q, q.property, by simp [mul_assoc]⟩
  · intro h
    obtain ⟨p, hp, q, hq, rfl⟩ := DoubleCoset.eq.mp h
    refine ⟨⟨q, hq⟩, Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)⟩
    simpa [mul_assoc] using hp

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem cosetOrbit_eq_iff_doubleCoset_eq (v w : G) :
    cosetOrbit P Q v = cosetOrbit P Q w ↔
      DoubleCoset.mk P Q v⁻¹ = DoubleCoset.mk P Q w⁻¹ := by
  constructor
  · intro h
    have hv : Induction.quotientMap P v⁻¹ ∈ cosetOrbit P Q v :=
      (quotientMap_mem_cosetOrbit_iff P Q v v⁻¹).mpr rfl
    rw [h] at hv
    exact ((quotientMap_mem_cosetOrbit_iff P Q w v⁻¹).mp hv).symm
  · intro h
    ext x
    induction x using Quotient.inductionOn with
    | h x =>
      change Induction.quotientMap P x ∈ cosetOrbit P Q v ↔
        Induction.quotientMap P x ∈ cosetOrbit P Q w
      rw [quotientMap_mem_cosetOrbit_iff, quotientMap_mem_cosetOrbit_iff, h]

namespace OrderedDoubleCosets

variable {P Q} {m : ℕ}

/-- The given disjoint orbit cover indexes the actual double-coset quotient. -/
def doubleCosetEquiv (s : OrderedDoubleCosets P Q m) :
    Fin m ≃ DoubleCoset.Quotient (P : Set G) (Q : Set G) :=
  Equiv.ofBijective (fun i => DoubleCoset.mk P Q (s.representative i)⁻¹) (by
    constructor
    · intro i j hij
      by_contra hne
      have horbit := (cosetOrbit_eq_iff_doubleCoset_eq P Q _ _).mpr hij
      have hi : Induction.quotientMap P (s.representative i)⁻¹ ∈
          cosetOrbit P Q (s.representative i) :=
        (quotientMap_mem_cosetOrbit_iff P Q _ _).mpr rfl
      have hj := hi
      rw [horbit] at hj
      exact Set.disjoint_left.mp (s.disjoint hne) hi hj
    · intro x
      induction x using Quotient.inductionOn with
      | h x =>
        obtain ⟨i, hi⟩ := s.covers (Induction.quotientMap P x)
        exact ⟨i, (quotientMap_mem_cosetOrbit_iff P Q _ _).mp hi⟩)

omit [IsTopologicalGroup G] in
@[simp]
theorem doubleCosetEquiv_apply (s : OrderedDoubleCosets P Q m) (i : Fin m) :
    s.doubleCosetEquiv i = DoubleCoset.mk P Q (s.representative i)⁻¹ := rfl

/-- Change representatives without changing any ordered orbit or initial union. -/
def replaceRepresentatives (s : OrderedDoubleCosets P Q m) (r : Fin m → G)
    (h : ∀ i, DoubleCoset.mk P Q (r i)⁻¹ =
      DoubleCoset.mk P Q (s.representative i)⁻¹) :
    OrderedDoubleCosets P Q m where
  representative := r
  covers x := by
    obtain ⟨i, hi⟩ := s.covers x
    exact ⟨i, (cosetOrbit_eq_iff_doubleCoset_eq P Q _ _).mpr (h i) ▸ hi⟩
  disjoint := by
    intro i j hij
    rw [(cosetOrbit_eq_iff_doubleCoset_eq P Q _ _).mpr (h i),
      (cosetOrbit_eq_iff_doubleCoset_eq P Q _ _).mpr (h j)]
    exact s.disjoint hij
  initial_open k := by
    simpa only [(fun i => (cosetOrbit_eq_iff_doubleCoset_eq P Q _ _).mpr (h i))]
      using s.initial_open k

/-- Align an ordered cover with any complete, unique classification by representatives. -/
def classifiedRepresentatives {A : Type uA} (s : OrderedDoubleCosets P Q m)
    (r : A → G)
    (h : Function.Bijective (fun a => DoubleCoset.mk P Q (r a)⁻¹)) :
    Σ e : Fin m ≃ A, {t : OrderedDoubleCosets P Q m //
      ∀ i, t.representative i = r (e i)} := by
  let e := s.doubleCosetEquiv.trans (Equiv.ofBijective _ h).symm
  have he : ∀ i, DoubleCoset.mk P Q (r (e i))⁻¹ =
      DoubleCoset.mk P Q (s.representative i)⁻¹ := by
    intro i
    exact (Equiv.ofBijective _ h).apply_symm_apply (s.doubleCosetEquiv i)
  exact ⟨e, s.replaceRepresentatives (fun i => r (e i)) he, fun _ => rfl⟩

end OrderedDoubleCosets

open GeneralLinear

universe uF

/-- Replace an existing parabolic orbit ordering by its actual minimal permutation
matrices, assuming the separately stated Bruhat bijectivity. -/
def minimalPermutationOrdering {F : Type uF} [CommRing F]
    [TopologicalSpace F] [IsTopologicalRing F] {n m : ℕ} (B C : BlockShape n)
    (s : OrderedDoubleCosets (B.parabolic F) (C.parabolic F) m)
    (h : Function.Bijective (parabolicDoubleCoset F B C)) :
    Σ e : Fin m ≃ MinimalRepresentatives B C,
      {t : OrderedDoubleCosets (B.parabolic F) (C.parabolic F) m //
        ∀ i, t.representative i = permutation n F (e i).val} :=
  s.classifiedRepresentatives (fun w : MinimalRepresentatives B C => permutation n F w.val) h

end Langlands.Geometric
