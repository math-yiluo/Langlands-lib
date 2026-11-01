import Langlands.Geometry.Analytic.StrictTestDomain.IteratedLaurentCover
import Langlands.Geometry.Analytic.StrictTestDomain.StandardRationalCover
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic

/-! # All-unit standard covers refined by finite Laurent covers -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalData

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {P Q : PresentedStrictAffinoidAlgebra K} {n : ℕ}

/-- All ordered ratios, in the order of `finProdFinEquiv`. -/
def allUnitRatios (f : Fin n → P) (a : Fin (n * n)) : P :=
  f (finProdFinEquiv.symm a).1 * Ring.inverse (f (finProdFinEquiv.symm a).2)

@[simp]
theorem allUnitRatios_pair (f : Fin n → P) (i j : Fin n) :
    allUnitRatios f (finProdFinEquiv (i, j)) = f i * Ring.inverse (f j) := by
  simp [allUnitRatios]

/-- Positive tuple lengths retain every Boolean leaf; the index is empty at zero. -/
abbrev AllUnitLaurentIndex (n : ℕ) := {_ε : Fin (n * n) → Bool // 0 < n}

/-- Choose the first candidate for a lower branch, the second for an upper branch. -/
def allUnitLaurentStep (ε : Fin (n * n) → Bool) (i j : Fin n) : Fin n :=
  if ε (finProdFinEquiv (i, j)) then i else j

/-- The running maximum is determined solely by the Boolean choices. -/
def allUnitLaurentIndex (a : AllUnitLaurentIndex n) : Fin n :=
  (List.finRange n).foldl (allUnitLaurentStep a.val) ⟨0, a.property⟩

private theorem foldl_dominates {α : Type*} (v : α → ℝ) (step : α → α → α)
    (hstep : ∀ i j, v i ≤ v (step i j) ∧ v j ≤ v (step i j))
    (l : List α) (a : α) :
    v a ≤ v (l.foldl step a) ∧ ∀ i ∈ l, v i ≤ v (l.foldl step a) := by
  induction l generalizing a with
  | nil => exact ⟨le_rfl, by simp⟩
  | cons b l ih =>
      obtain ⟨hab, hb⟩ := hstep a b
      obtain ⟨hhead, htail⟩ := ih (step a b)
      refine ⟨hab.trans hhead, ?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hb.trans hhead
      · exact htail i hi

/-- A chosen Laurent inequality for a ratio implies the corresponding comparison. -/
theorem allUnitRatio_choice_bound (f : Fin n → P) (hu : ∀ j, IsUnit (f j))
    (ε : Fin (n * n) → Bool) (x : BanachSpectrum P)
    (hε : ∀ a, if ε a then 1 ≤ x (allUnitRatios f a)
      else x (allUnitRatios f a) ≤ 1) (i j : Fin n) :
    x (f i) ≤ x (f (allUnitLaurentStep ε i j)) ∧
      x (f j) ≤ x (f (allUnitLaurentStep ε i j)) := by
  have hmul : x (f i * Ring.inverse (f j)) * x (f j) = x (f i) := by
    rw [← map_mul, mul_assoc, Ring.inverse_mul_cancel _ (hu j), mul_one]
  have h := hε (finProdFinEquiv (i, j))
  rw [allUnitRatios_pair] at h
  cases hb : ε (finProdFinEquiv (i, j)) with
  | false =>
      have hle : x (f i) ≤ x (f j) := by
        have hh := mul_le_mul_of_nonneg_right
          (show x (f i * Ring.inverse (f j)) ≤ 1 by simpa [hb] using h)
          (apply_nonneg x.toMulRingSeminorm (f j))
        simpa only [hmul, one_mul] using hh
      simpa [allUnitLaurentStep, hb] using And.intro hle (le_refl (x (f j)))
  | true =>
      have hle : x (f j) ≤ x (f i) := by
        have hh := mul_le_mul_of_nonneg_right
          (show 1 ≤ x (f i * Ring.inverse (f j)) by simpa [hb] using h)
          (apply_nonneg x.toMulRingSeminorm (f j))
        simpa only [hmul, one_mul] using hh
      simpa [allUnitLaurentStep, hb] using And.intro (le_refl (x (f i))) hle

/-- Units remain units under the actual bounded algebra map. -/
theorem allUnit_tuple_units_pullback (f : Fin n → P) (hu : ∀ i, IsUnit (f i))
    (φ : BoundedAlgHom K P Q) : ∀ i, IsUnit (φ (f i)) :=
  fun i => (hu i).map φ.toAlgHom.toMonoidHom

private theorem map_inverse_of_unit (φ : BoundedAlgHom K P Q) (p : P) (hp : IsUnit p) :
    φ (Ring.inverse p) = Ring.inverse (φ p) := by
  apply (hp.map φ.toAlgHom.toMonoidHom).mul_left_cancel
  change φ p * φ (Ring.inverse p) = φ p * Ring.inverse (φ p)
  rw [← map_mul, Ring.mul_inverse_cancel _ hp, map_one]
  exact (Ring.mul_inverse_cancel (φ p) (hp.map φ.toAlgHom.toMonoidHom)).symm

/-- The ratio tuple commutes with bounded base change when all denominators are units. -/
theorem allUnitRatios_map (f : Fin n → P) (hu : ∀ i, IsUnit (f i))
    (φ : BoundedAlgHom K P Q) :
    (fun k => φ (allUnitRatios f k)) = allUnitRatios (fun i => φ (f i)) := by
  funext k
  simp only [allUnitRatios, map_mul, map_inverse_of_unit φ _ (hu _)]

variable [CompleteSpace K]

/-- The actual rational datum of a retained pairwise-ratio Laurent leaf. -/
abbrev allUnitLaurentLeaf (f : Fin n → P) (a : AllUnitLaurentIndex n) : RationalData K P :=
  iteratedLaurent (allUnitRatios f) a.val

/-- Every leaf is included in the standard domain selected without using a point. -/
def allUnitLaurentInclusion (f : Fin n → P)
    (hf : ∀ x : BanachSpectrum P, ∃ i, x (f i) ≠ 0)
    (hu : ∀ i, IsUnit (f i)) (a : AllUnitLaurentIndex n) :
    allUnitLaurentLeaf f a ⟶ standardRational f hf (allUnitLaurentIndex a) := by
  refine ⟨?_⟩
  intro x hx
  have hε := (mem_locus_iteratedLaurent (allUnitRatios f) a.val x).mp hx
  have hbound := foldl_dominates (fun i => x (f i)) (allUnitLaurentStep a.val)
    (allUnitRatio_choice_bound f hu a.val x hε) (List.finRange n) ⟨0, a.property⟩
  change ∀ i : Fin n, x (f i) ≤ x (f (allUnitLaurentIndex a))
  intro i
  exact hbound.2 i (by simp)

/-- The retained finite Laurent leaves cover the spectrum, including the empty-tuple case. -/
theorem allUnitLaurent_covers (f : Fin n → P)
    (hf : ∀ x : BanachSpectrum P, ∃ i, x (f i) ≠ 0) (x : BanachSpectrum P) :
    ∃ a : AllUnitLaurentIndex n, x ∈ (allUnitLaurentLeaf f a).locus := by
  obtain ⟨i, _⟩ := hf x
  obtain ⟨ε, hε⟩ := iteratedLaurent_covers (allUnitRatios f) x
  exact ⟨⟨ε, (Nat.zero_le i.val).trans_lt i.isLt⟩, hε⟩

/-- There is no refinement index for the empty tuple. -/
theorem allUnitLaurentIndex_zero_empty : IsEmpty (AllUnitLaurentIndex 0) :=
  ⟨fun a => (Nat.not_lt_zero 0 a.property).elim⟩

/-- Absence of common zeros for an empty tuple forces the actual base algebra to be zero. -/
theorem subsingleton_of_empty_tuple (f : Fin 0 → P)
    (hf : ∀ x : BanachSpectrum P, ∃ i, x (f i) ≠ 0) : Subsingleton P := by
  by_contra h
  have : Nontrivial P := not_subsingleton_iff_nontrivial.mp h
  obtain ⟨x⟩ := PresentedStrictAffinoidAlgebra.spectrum_nonempty P
  obtain ⟨i, _⟩ := hf x
  exact Fin.elim0 i

/-- The standard inclusion induces an actual bounded restriction over the base. -/
theorem allUnitLaurentInclusion_comp_baseMap (f : Fin n → P)
    (hf : ∀ x : BanachSpectrum P, ∃ i, x (f i) ≠ 0)
    (hu : ∀ i, IsUnit (f i)) (a : AllUnitLaurentIndex n) :
    (allUnitLaurentInclusion f hf hu a).restriction.comp
      (standardRational f hf (allUnitLaurentIndex a)).baseMap =
    (allUnitLaurentLeaf f a).baseMap :=
  Inclusion.restriction_comp_baseMap _

/-- The finite Laurent refinement in the universe of the rational site. -/
theorem allUnitLaurent_familyCovers (f : Fin n → P)
    (hf : ∀ x : BanachSpectrum P, ∃ i, x (f i) ≠ 0) :
    FamilyCovers (whole K P)
      (fun a : ULift.{u} (AllUnitLaurentIndex n) => allUnitLaurentLeaf f a.down) := by
  intro x _
  obtain ⟨a, ha⟩ := allUnitLaurent_covers f hf x
  exact ⟨⟨a⟩, ha⟩

/-- A mapped all-unit leaf has exactly the actual pulled-back locus. -/
theorem locus_allUnitLaurent_pullback (f : Fin n → P) (hu : ∀ i, IsUnit (f i))
    (a : AllUnitLaurentIndex n) (φ : BoundedAlgHom K P Q) :
    ((allUnitLaurentLeaf f a).pullback φ).locus =
      (allUnitLaurentLeaf (fun i => φ (f i)) a).locus := by
  change ((iteratedLaurent (allUnitRatios f) a.val).pullback φ).locus = _
  rw [locus_iteratedLaurent_pullback, allUnitRatios_map f hu φ]

/-- Equal-locus isomorphism, retaining the chosen rational presentations. -/
def allUnitLaurentPullbackIso (f : Fin n → P) (hu : ∀ i, IsUnit (f i))
    (a : AllUnitLaurentIndex n) (φ : BoundedAlgHom K P Q) :
    (allUnitLaurentLeaf f a).pullback φ ≅ allUnitLaurentLeaf (fun i => φ (f i)) a where
  hom := ⟨(locus_allUnitLaurent_pullback f hu a φ).le⟩
  inv := ⟨(locus_allUnitLaurent_pullback f hu a φ).ge⟩
  hom_inv_id := (inferInstance : Subsingleton (Inclusion _ _)).elim _ _
  inv_hom_id := (inferInstance : Subsingleton (Inclusion _ _)).elim _ _

/-- Actual bounded comparison from the original leaf quotient to the mapped leaf quotient. -/
def allUnitLaurentComparison (f : Fin n → P) (hu : ∀ i, IsUnit (f i))
    (a : AllUnitLaurentIndex n) (φ : BoundedAlgHom K P Q) :
    BoundedAlgHom K (allUnitLaurentLeaf f a).algebra
      (allUnitLaurentLeaf (fun i => φ (f i)) a).algebra :=
  (allUnitLaurentPullbackIso f hu a φ).inv.restriction.comp
    ((allUnitLaurentLeaf f a).comparison φ)

/-- Base-map square for the actual bounded leaf comparison. -/
theorem allUnitLaurentComparison_comp_baseMap (f : Fin n → P)
    (hu : ∀ i, IsUnit (f i)) (a : AllUnitLaurentIndex n) (φ : BoundedAlgHom K P Q) :
    (allUnitLaurentComparison f hu a φ).comp (allUnitLaurentLeaf f a).baseMap =
      (allUnitLaurentLeaf (fun i => φ (f i)) a).baseMap.comp φ := by
  rw [allUnitLaurentComparison, BoundedAlgHom.comp_assoc, comparison_comp_baseMap,
    ← BoundedAlgHom.comp_assoc, Inclusion.restriction_comp_baseMap]

/-- Refinement restrictions commute with the standard quotient comparison after any base change. -/
theorem allUnitLaurentComparison_restriction (f : Fin n → P)
    (hf : ∀ x : BanachSpectrum P, ∃ i, x (f i) ≠ 0)
    (hu : ∀ i, IsUnit (f i)) (a : AllUnitLaurentIndex n) (φ : BoundedAlgHom K P Q) :
    (allUnitLaurentInclusion (fun i => φ (f i)) (tuple_no_common_zero_pullback f hf φ)
      (allUnit_tuple_units_pullback f hu φ) a).restriction.comp
        ((standardRational f hf (allUnitLaurentIndex a)).comparison φ) =
    (allUnitLaurentComparison f hu a φ).comp (allUnitLaurentInclusion f hf hu a).restriction := by
  let d := standardRational f hf (allUnitLaurentIndex a)
  let h : allUnitLaurentLeaf f a ⟶ d := allUnitLaurentInclusion f hf hu a
  let h' : allUnitLaurentLeaf (fun i => φ (f i)) a ⟶ d.pullback φ :=
    allUnitLaurentInclusion (fun i => φ (f i)) (tuple_no_common_zero_pullback f hf φ)
      (allUnit_tuple_units_pullback f hu φ) a
  change h'.restriction.comp (d.comparison φ) =
    (allUnitLaurentComparison f hu a φ).comp h.restriction
  apply d.hom_ext
  calc
    (h'.restriction.comp (d.comparison φ)).comp d.baseMap =
        h'.restriction.comp ((d.comparison φ).comp d.baseMap) :=
      BoundedAlgHom.comp_assoc _ _ _
    _ = h'.restriction.comp ((d.pullback φ).baseMap.comp φ) :=
      congrArg (fun ψ => h'.restriction.comp ψ) (d.comparison_comp_baseMap φ)
    _ = (h'.restriction.comp (d.pullback φ).baseMap).comp φ :=
      (BoundedAlgHom.comp_assoc _ _ _).symm
    _ = (allUnitLaurentLeaf (fun i => φ (f i)) a).baseMap.comp φ :=
      congrArg (fun ψ => ψ.comp φ) h'.restriction_comp_baseMap
    _ = (allUnitLaurentComparison f hu a φ).comp (allUnitLaurentLeaf f a).baseMap :=
      (allUnitLaurentComparison_comp_baseMap f hu a φ).symm
    _ = (allUnitLaurentComparison f hu a φ).comp (h.restriction.comp d.baseMap) :=
      congrArg (fun ψ => (allUnitLaurentComparison f hu a φ).comp ψ)
        h.restriction_comp_baseMap.symm
    _ = ((allUnitLaurentComparison f hu a φ).comp h.restriction).comp d.baseMap :=
      (BoundedAlgHom.comp_assoc _ _ _).symm

end Langlands.Analytic.StrictTestDomain.RationalData
