import Langlands.Representation.Aubert.SignedCutComplex
import Mathlib.LinearAlgebra.Isomorphisms

/-! Subdiagrams and the actual homogeneous quotients of a signed cut diagram. -/

noncomputable section

namespace Langlands.Aubert.CutComplex.Diagram

open scoped BigOperators

universe uI uM

variable {ι : Type uI} [LinearOrder ι] (D : Diagram.{uI,uM} ι)

/-- Coordinate submodules preserved by every transition of the cut diagram. -/
structure Subdiagram where
  obj : ∀ s, Submodule ℂ (D.Obj s)
  map_mem : ∀ {s t : Finset ι} (h : s ⊆ t) (x : D.Obj s),
    x ∈ obj s → D.map h x ∈ obj t

namespace Subdiagram

variable {D} (S U : D.Subdiagram)

/-- The coordinate support condition on total families. -/
def totalSubmodule : Submodule ℂ D.Total where
  carrier := {x | ∀ s, x s ∈ S.obj s}
  zero_mem' s := (S.obj s).zero_mem
  add_mem' hx hy s := (S.obj s).add_mem (hx s) (hy s)
  smul_mem' a _x hx s := (S.obj s).smul_mem a (hx s)

/-- The coordinate support condition on homogeneous families. -/
def degreeSubmodule (k : ℕ) : Submodule ℂ (D.Degree k) where
  carrier := {x | ∀ s, x s ∈ S.obj s.1}
  zero_mem' s := (S.obj s.1).zero_mem
  add_mem' hx hy s := (S.obj s.1).add_mem (hx s) (hy s)
  smul_mem' a _x hx s := (S.obj s.1).smul_mem a (hx s)

theorem step_mem (i : ι) (x : D.Total) (hx : x ∈ S.totalSubmodule) :
    D.step i x ∈ S.totalSubmodule := by
  intro s
  by_cases hi : i ∈ s
  · simpa only [step_apply, hi, ↓reduceIte] using (S.obj s).smul_mem (sign s i)
      (S.map_mem (Finset.erase_subset i s) (x (s.erase i)) (hx _))
  · simpa only [step_apply, hi, ↓reduceIte] using (S.obj s).zero_mem

theorem extend_mem (k : ℕ) (x : D.Degree k) (hx : x ∈ S.degreeSubmodule k) :
    D.extend k x ∈ S.totalSubmodule := by
  intro s
  by_cases hs : s.card = k
  · simpa only [extend_apply, hs, ↓reduceDIte] using hx ⟨s, hs⟩
  · simpa only [extend_apply, hs, ↓reduceDIte] using (S.obj s).zero_mem

theorem restrict_mem (k : ℕ) (x : D.Total) (hx : x ∈ S.totalSubmodule) :
    D.restrict k x ∈ S.degreeSubmodule k :=
  fun s => hx s.1

/-- Extend a homogeneous supported family by zero. -/
def extend (k : ℕ) : S.degreeSubmodule k →ₗ[ℂ] S.totalSubmodule :=
  (D.extend k).restrict (S.extend_mem k)

/-- Restrict a supported total family to one homogeneous degree. -/
def restrict (k : ℕ) : S.totalSubmodule →ₗ[ℂ] S.degreeSubmodule k :=
  (D.restrict k).restrict (S.restrict_mem k)

variable [Fintype ι]

theorem differential_mem (x : D.Total) (hx : x ∈ S.totalSubmodule) :
    D.differential x ∈ S.totalSubmodule := by
  rw [differential_apply]
  exact S.totalSubmodule.sum_mem (fun i _ => S.step_mem i x hx)

theorem degreeDifferential_mem (k : ℕ) (x : D.Degree k)
    (hx : x ∈ S.degreeSubmodule k) :
    D.degreeDifferential k x ∈ S.degreeSubmodule (k + 1) :=
  S.restrict_mem (k + 1) _ (S.differential_mem _ (S.extend_mem k x hx))

/-- The actual signed insertion restricted to supported families. -/
def totalStep (i : ι) : S.totalSubmodule →ₗ[ℂ] S.totalSubmodule :=
  (D.step i).restrict (S.step_mem i)

/-- The actual signed total differential restricted to supported families. -/
def totalDifferential : S.totalSubmodule →ₗ[ℂ] S.totalSubmodule :=
  D.differential.restrict S.differential_mem

theorem totalDifferential_eq_sum : S.totalDifferential = ∑ i, S.totalStep i := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [LinearMap.sum_apply, Submodule.coe_sum]
  change D.differential x.1 = ∑ i, D.step i x.1
  exact D.differential_apply x.1

/-- The actual homogeneous differential restricted to supported families. -/
def degreeDifferential (k : ℕ) :
    S.degreeSubmodule k →ₗ[ℂ] S.degreeSubmodule (k + 1) :=
  (D.degreeDifferential k).restrict (S.degreeDifferential_mem k)

theorem degreeDifferential_eq (k : ℕ) :
    S.degreeDifferential k =
      S.restrict (k + 1) ∘ₗ S.totalDifferential ∘ₗ S.extend k := rfl

omit [Fintype ι] in
/-- The lower coordinate submodule pulled back to the upper coordinate. -/
def denominator (s : Finset ι) : Submodule ℂ (U.obj s) :=
  (S.obj s).comap (U.obj s).subtype

omit [Fintype ι] in
/-- The diagram of actual upper support quotients, with descended transitions. -/
def quotientDiagram : Diagram.{uI,uM} ι where
  Obj s := U.obj s ⧸ S.denominator U s
  add _ := inferInstance
  module _ := inferInstance
  map {s t} h := (S.denominator U s).mapQ (S.denominator U t)
    ((D.map h).restrict (U.map_mem h))
    (fun x hx => S.map_mem h x.1 hx)
  map_refl s := by
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := (S.denominator U s).mkQ_surjective q
    change (S.denominator U s).mkQ ⟨D.map Finset.Subset.rfl x.1, _⟩ =
      (S.denominator U s).mkQ x
    congr 1
    apply Subtype.ext
    exact LinearMap.congr_fun (D.map_refl s) x.1
  map_comp {s t u} hst htu := by
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := (S.denominator U s).mkQ_surjective q
    change (S.denominator U u).mkQ ⟨D.map htu (D.map hst x.1), _⟩ =
      (S.denominator U u).mkQ ⟨D.map (hst.trans htu) x.1, _⟩
    congr 1
    apply Subtype.ext
    exact D.map_map hst htu x.1

omit [Fintype ι] in
@[simp] theorem quotientDiagram_map_mk {s t : Finset ι} (h : s ⊆ t)
    (x : U.obj s) :
    (S.quotientDiagram U).map h ((S.denominator U s).mkQ x) =
      (S.denominator U t).mkQ ⟨D.map h x.1, U.map_mem h x.1 x.property⟩ := rfl

omit [Fintype ι] in
/-- Project a supported total family to its coordinate support quotients. -/
def totalProjection : U.totalSubmodule →ₗ[ℂ] (S.quotientDiagram U).Total where
  toFun x s := (S.denominator U s).mkQ ⟨x.1 s, x.property s⟩
  map_add' x y := by
    funext s
    exact map_add (S.denominator U s).mkQ ⟨x.1 s, x.property s⟩
      ⟨y.1 s, y.property s⟩
  map_smul' a x := by
    funext s
    exact map_smul (S.denominator U s).mkQ a ⟨x.1 s, x.property s⟩

omit [Fintype ι] in
/-- Project a supported homogeneous family to its coordinate quotients. -/
def degreeProjection (k : ℕ) :
    U.degreeSubmodule k →ₗ[ℂ] (S.quotientDiagram U).Degree k where
  toFun x s := (S.denominator U s.1).mkQ ⟨x.1 s, x.property s⟩
  map_add' x y := by
    funext s
    exact map_add (S.denominator U s.1).mkQ ⟨x.1 s, x.property s⟩
      ⟨y.1 s, y.property s⟩
  map_smul' a x := by
    funext s
    exact map_smul (S.denominator U s.1).mkQ a ⟨x.1 s, x.property s⟩

omit [Fintype ι] in
theorem totalProjection_extend (k : ℕ) (x : U.degreeSubmodule k) :
    S.totalProjection U (U.extend k x) =
      (S.quotientDiagram U).extend k (S.degreeProjection U k x) := by
  funext s
  by_cases hs : s.card = k
  · rw [extend_apply, dite_eq_left hs]
    apply congrArg (S.denominator U s).mkQ
    apply Subtype.ext
    change D.extend k x.1 s = x.1 ⟨s, hs⟩
    simp only [extend_apply, dite_eq_left hs]
  · rw [extend_apply, dite_eq_right hs]
    change (S.denominator U s).mkQ
      (⟨D.extend k x.1 s, U.extend_mem k x.1 x.property s⟩ : U.obj s) = 0
    have hz : (⟨D.extend k x.1 s, U.extend_mem k x.1 x.property s⟩ : U.obj s) = 0 := by
      apply Subtype.ext
      simp only [extend_apply, dite_eq_right hs, ZeroMemClass.coe_zero]
    rw [hz, map_zero]

omit [Fintype ι] in
theorem degreeProjection_restrict (k : ℕ) (x : U.totalSubmodule) :
    S.degreeProjection U k (U.restrict k x) =
      (S.quotientDiagram U).restrict k (S.totalProjection U x) := rfl

omit [Fintype ι] in
theorem totalProjection_step (i : ι) (x : U.totalSubmodule) :
    S.totalProjection U (U.totalStep i x) =
      (S.quotientDiagram U).step i (S.totalProjection U x) := by
  funext s
  by_cases hi : i ∈ s
  · rw [step_apply, ite_eq_left hi]
    change (S.denominator U s).mkQ
      (⟨D.step i x.1 s, U.step_mem i x.1 x.property s⟩ : U.obj s) =
      sign s i • (S.denominator U s).mkQ
        ⟨D.map (Finset.erase_subset i s) (x.1 (s.erase i)), _⟩
    rw [← map_smul]
    apply congrArg (S.denominator U s).mkQ
    apply Subtype.ext
    exact ite_eq_left hi
  · rw [step_apply, ite_eq_right hi]
    change (S.denominator U s).mkQ
      (⟨D.step i x.1 s, U.step_mem i x.1 x.property s⟩ : U.obj s) = 0
    have hz : (⟨D.step i x.1 s, U.step_mem i x.1 x.property s⟩ : U.obj s) = 0 := by
      apply Subtype.ext
      exact ite_eq_right hi
    rw [hz, map_zero]

theorem totalProjection_differential (x : U.totalSubmodule) :
    S.totalProjection U (U.totalDifferential x) =
      (S.quotientDiagram U).differential (S.totalProjection U x) := by
  rw [U.totalDifferential_eq_sum]
  simp only [LinearMap.sum_apply, map_sum, totalProjection_step, differential_apply]

/-- Projecting to coordinate support quotients preserves the exterior signs. -/
theorem degreeProjection_differential (k : ℕ) (x : U.degreeSubmodule k) :
    S.degreeProjection U (k + 1) (U.degreeDifferential k x) =
      (S.quotientDiagram U).degreeDifferential k (S.degreeProjection U k x) := by
  rw [U.degreeDifferential_eq]
  change S.degreeProjection U (k + 1)
    (U.restrict (k + 1) (U.totalDifferential (U.extend k x))) = _
  rw [degreeProjection_restrict, totalProjection_differential, totalProjection_extend]
  rfl

omit [Fintype ι] in
theorem degreeProjection_surjective (k : ℕ) :
    Function.Surjective (S.degreeProjection U k) := by
  intro y
  choose x hx using fun s : {s : Finset ι // s.card = k} =>
    (S.denominator U s.1).mkQ_surjective (y s)
  exact ⟨⟨fun s => (x s).1, fun s => (x s).property⟩, funext hx⟩

omit [Fintype ι] in
/-- The lower homogeneous support pulled back to the upper homogeneous support. -/
def degreeDenominator (k : ℕ) : Submodule ℂ (U.degreeSubmodule k) :=
  (S.degreeSubmodule k).comap (U.degreeSubmodule k).subtype

omit [Fintype ι] in
theorem degreeProjection_ker (k : ℕ) :
    LinearMap.ker (S.degreeProjection U k) = S.degreeDenominator U k := by
  ext x
  change S.degreeProjection U k x = 0 ↔ ∀ s, x.1 s ∈ S.obj s.1
  constructor
  · intro hx s
    exact (Submodule.Quotient.mk_eq_zero (S.denominator U s.1)).mp
      (congrFun hx s)
  · intro hx
    funext s
    exact (Submodule.Quotient.mk_eq_zero (S.denominator U s.1)).mpr (hx s)

omit [Fintype ι] in
/-- The quotient of the actual homogeneous supports is the homogeneous product
of their coordinate quotients. -/
def degreeQuotientEquiv (k : ℕ) :
    (U.degreeSubmodule k ⧸ S.degreeDenominator U k) ≃ₗ[ℂ]
      (S.quotientDiagram U).Degree k :=
  (Submodule.quotEquivOfEq _ _ (S.degreeProjection_ker U k).symm).trans
    ((S.degreeProjection U k).quotKerEquivOfSurjective
      (S.degreeProjection_surjective U k))

omit [Fintype ι] in
@[simp] theorem degreeQuotientEquiv_mk (k : ℕ) (x : U.degreeSubmodule k) :
    S.degreeQuotientEquiv U k ((S.degreeDenominator U k).mkQ x) =
      S.degreeProjection U k x := rfl

/-- The differential descended to the actual quotient of homogeneous supports. -/
def degreeQuotientDifferential (k : ℕ) :
    (U.degreeSubmodule k ⧸ S.degreeDenominator U k) →ₗ[ℂ]
      (U.degreeSubmodule (k + 1) ⧸ S.degreeDenominator U (k + 1)) :=
  (S.degreeDenominator U k).mapQ (S.degreeDenominator U (k + 1))
    (U.degreeDifferential k)
    (fun x hx => S.degreeDifferential_mem k x.1 hx)

@[simp] theorem degreeQuotientDifferential_mk (k : ℕ) (x : U.degreeSubmodule k) :
    S.degreeQuotientDifferential U k ((S.degreeDenominator U k).mkQ x) =
      (S.degreeDenominator U (k + 1)).mkQ (U.degreeDifferential k x) := rfl

/-- The actual quotient-degree equivalence intertwines the actual descended
differential with the signed coordinate-quotient differential. -/
theorem degreeQuotientEquiv_differential (k : ℕ)
    (x : U.degreeSubmodule k ⧸ S.degreeDenominator U k) :
    S.degreeQuotientEquiv U (k + 1) (S.degreeQuotientDifferential U k x) =
      (S.quotientDiagram U).degreeDifferential k (S.degreeQuotientEquiv U k x) := by
  obtain ⟨y, rfl⟩ := (S.degreeDenominator U k).mkQ_surjective x
  rw [degreeQuotientDifferential_mk, degreeQuotientEquiv_mk, degreeQuotientEquiv_mk]
  exact S.degreeProjection_differential U k y

end Subdiagram
end Langlands.Aubert.CutComplex.Diagram
