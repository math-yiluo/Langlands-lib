import Langlands.Cohomology.Tate.TowerDefinitions
import Langlands.Cohomology.Tate.ShiftInduction

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]
variable {K H : Subgroup G} (h : K ≤ H)
variable [Fintype K] [Fintype H] [Fintype (K.subgroupOf H)]
variable [Fintype (G ⧸ K)] [Fintype (G ⧸ H)] [Fintype (H ⧸ K.subgroupOf H)]

omit [Fintype H] [Fintype (G ⧸ H)] [Fintype (H ⧸ K.subgroupOf H)] in
lemma towerRestriction_delta (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (n : ℤ) (x : tateCohomology S.X₃ n) :
    (towerReindex h S.X₁ (n + 1)).hom
        (restriction K S.X₁ (n + 1) (TateCohomology.δ (scalarSplit_shortExact S s) n x)) =
      TateCohomology.δ
        (((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype)).map_of_exact
          (Rep.resFunctor (K.subgroupOf H).subtype)) n
        ((towerReindex h S.X₃ n).hom (restriction K S.X₃ n x)) :=
  (congrArg (towerReindex h S.X₁ (n + 1)).hom
    (restriction_scalarSplit_delta K S s n x)).trans
      (towerReindex_delta h S (scalarSplit_shortExact S s) n (restriction K S.X₃ n x))

omit [Fintype K] [Fintype (G ⧸ K)] in
lemma iteratedRestriction_delta (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (n : ℤ) (x : tateCohomology S.X₃ n) :
    restriction (K.subgroupOf H) (Rep.res H.subtype S.X₁) (n + 1)
        (restriction H S.X₁ (n + 1) (TateCohomology.δ (scalarSplit_shortExact S s) n x)) =
      TateCohomology.δ
        (((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor H.subtype)).map_of_exact
          (Rep.resFunctor (K.subgroupOf H).subtype)) n
        (restriction (K.subgroupOf H) (Rep.res H.subtype S.X₃) n
          (restriction H S.X₃ n x)) :=
  (congrArg (restriction (K.subgroupOf H) (Rep.res H.subtype S.X₁) (n + 1))
    (restriction_scalarSplit_delta H S s n x)).trans
      (restriction_scalarSplit_delta (K.subgroupOf H) (S.map (Rep.resFunctor H.subtype))
        (scalarSplitting_restrict (H := H) S s) n (restriction H S.X₃ n x))

/-- Restriction through a subgroup tower equals direct restriction in every integer degree. -/
theorem restriction_trans (A : Rep.{u} R G) (n : ℤ) (x : tateCohomology A n) :
    (towerReindex h A n).hom (restriction K A n x) =
      restriction (K.subgroupOf H) (Rep.res H.subtype A) n (restriction H A n x) := by
  refine tateClass_shift_induction
    (fun A n x => (towerReindex h A n).hom (restriction K A n x) =
      restriction (K.subgroupOf H) (Rep.res H.subtype A) n (restriction H A n x))
    (fun A x => restrictionZero_trans h A x) ?_ ?_ A n x
  · intro A n x ih
    refine (towerRestriction_delta h (shiftUpSequence A)
      (shiftUpSequence_scalarSplitting A) n x).trans ?_
    refine Eq.trans ?_ (iteratedRestriction_delta (K := K) (H := H)
      (shiftUpSequence A) (shiftUpSequence_scalarSplitting A) n x).symm
    exact congrArg
      (TateCohomology.δ
        (((shiftUpSequence_shortExact A).map_of_exact (Rep.resFunctor H.subtype)).map_of_exact
          (Rep.resFunctor (K.subgroupOf H).subtype)) n) ih
  · intro A n x ih
    apply (towerShiftDownIso (K := K) (H := H) A n).toLinearEquiv.injective
    exact (towerRestriction_delta h (shiftDownSequence A)
      (shiftDownSequence_scalarSplitting A) n x).symm.trans
        (ih.trans (iteratedRestriction_delta (K := K) (H := H)
          (shiftDownSequence A) (shiftDownSequence_scalarSplitting A) n x))

omit [Fintype (G ⧸ K)] in
/-- Induction on restricted Tate classes using the shifts of the ambient coefficient module. -/
lemma restrictedTateClass_shift_induction
    (P : (A : Rep.{u} R G) → (n : ℤ) →
      tateCohomology (Rep.res K.subtype A) n → Prop)
    (hz : ∀ A x, P A 0 x)
    (hu : ∀ A n x, P (shiftUp A) n x →
      P A (n + 1) ((restrictedShiftUpIso K A n).hom x))
    (hd : ∀ A n x, P (shiftDown A) (n + 1) ((restrictedShiftDownIso K A n).hom x) → P A n x)
    (A : Rep.{u} R G) (n : ℤ) (x : tateCohomology (Rep.res K.subtype A) n) :
    P A n x := by
  have hpos : ∀ n : ℕ, ∀ A x, P A n x := by
    intro n
    induction n with
    | zero => exact hz
    | succ n ih =>
      intro A x
      obtain ⟨y, rfl⟩ := (restrictedShiftUpIso K A n).toLinearEquiv.surjective x
      exact hu A n y (ih (shiftUp A) y)
  have hneg : ∀ n : ℕ, ∀ A x, P A (-(n : ℤ)) x := by
    intro n
    induction n with
    | zero => exact hz
    | succ n ih =>
      intro A x
      apply hd A (-((n + 1 : ℕ) : ℤ)) x
      have hn : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by omega
      have hh : ∀ y, P (shiftDown A) (-((n + 1 : ℕ) : ℤ) + 1) y := by
        rw [hn]
        exact ih (shiftDown A)
      exact hh _
  cases n with
  | ofNat n => exact hpos n A x
  | negSucc n => exact hneg (n + 1) A x

omit [Fintype (G ⧸ K)] in
lemma iteratedCorestriction_delta (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting)
    (n : ℤ) (x : tateCohomology (Rep.res K.subtype S.X₃) n) :
    corestriction H S.X₁ (n + 1)
        (corestriction (K.subgroupOf H) (Rep.res H.subtype S.X₁) (n + 1)
          ((towerReindex h S.X₁ (n + 1)).hom
            (TateCohomology.δ
              ((scalarSplit_shortExact S s).map_of_exact (Rep.resFunctor K.subtype)) n x))) =
      TateCohomology.δ (scalarSplit_shortExact S s) n
        (corestriction H S.X₃ n
          (corestriction (K.subgroupOf H) (Rep.res H.subtype S.X₃) n
            ((towerReindex h S.X₃ n).hom x))) := by
  rw [towerReindex_delta h S (scalarSplit_shortExact S s)]
  have hj := corestriction_scalarSplit_delta (K.subgroupOf H)
    (S.map (Rep.resFunctor H.subtype)) (scalarSplitting_restrict (H := H) S s) n
    ((towerReindex h S.X₃ n).hom x)
  exact (congrArg (corestriction H S.X₁ (n + 1)) hj).trans
    (corestriction_scalarSplit_delta H S s n
      (corestriction (K.subgroupOf H) (Rep.res H.subtype S.X₃) n
        ((towerReindex h S.X₃ n).hom x)))

/-- Corestriction through a subgroup tower equals direct corestriction in every integer degree. -/
theorem corestriction_trans (A : Rep.{u} R G) (n : ℤ)
    (x : tateCohomology (Rep.res K.subtype A) n) :
    corestriction K A n x =
      corestriction H A n (corestriction (K.subgroupOf H) (Rep.res H.subtype A) n
        ((towerReindex h A n).hom x)) := by
  refine restrictedTateClass_shift_induction
    (fun A n x => corestriction K A n x =
      corestriction H A n (corestriction (K.subgroupOf H) (Rep.res H.subtype A) n
        ((towerReindex h A n).hom x)))
    (fun A x => corestrictionZero_trans h A x) ?_ ?_ A n x
  · intro A n x ih
    refine (corestriction_scalarSplit_delta K (shiftUpSequence A)
      (shiftUpSequence_scalarSplitting A) n x).trans ?_
    refine Eq.trans ?_ (iteratedCorestriction_delta h (shiftUpSequence A)
      (shiftUpSequence_scalarSplitting A) n x).symm
    exact congrArg (shiftUpIso A n).hom ih
  · intro A n x ih
    apply (shiftDownIso A n).toLinearEquiv.injective
    exact (corestriction_scalarSplit_delta K (shiftDownSequence A)
      (shiftDownSequence_scalarSplitting A) n x).symm.trans
        (ih.trans (iteratedCorestriction_delta h (shiftDownSequence A)
          (shiftDownSequence_scalarSplitting A) n x))

end Langlands.Tate
