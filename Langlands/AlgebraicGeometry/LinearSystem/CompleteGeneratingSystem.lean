import Langlands.AlgebraicGeometry.ClosedRationalPoints
import Langlands.AlgebraicGeometry.LinearSystem.AmpleFinite
import Langlands.AlgebraicGeometry.LinearSystemMorphismProof

/-! # Complete generated linear systems over a field -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard
  Langlands.AlgebraicGeometry.Modules.DerivedSections

noncomputable section

namespace Langlands.AlgebraicGeometry.LinearSystem

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of K)) (L : LineBundle X)

/-- A basis of all global sections of an actual line bundle, indexed by a nonempty
finite set, with no common zero anywhere on the scheme. -/
structure CompleteGeneratingSystem where
  /-- Dimension of the projective space. -/
  n : ℕ
  /-- Basis of the entire section space, with its scalars from `p`. -/
  basis : Module.Basis (Fin (n + 1)) K ((relativeGlobalSections p).obj L.obj)
  /-- At each scheme point at least one basis section has nonzero residue. -/
  generates : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (basis i)

namespace CompleteGeneratingSystem

variable {p L} (C : CompleteGeneratingSystem p L)

/-- The actual projective linear-system map of the complete generating basis. -/
def map : X ⟶ ProjectiveSpace K C.n := linearSystemMap p C.generates

lemma map_toSpec : C.map ≫ projectiveSpaceToSpec K C.n = p :=
  linearSystemMap_toSpec p C.generates

/-- The finite morphism of an ample complete linear system on a proper field scheme. -/
lemma isFinite_map_of_isAmple [IsProper p] (hL : L.IsAmple) : IsFinite C.map :=
  isFinite_linearSystemMap_of_isAmple p hL C.generates

/-- Two rational points have the same image if every section vanishing at the first
also vanishes at the second. -/
lemma comp_map_eq_of_rational_vanishing
    {x y : Spec (CommRingCat.of K) ⟶ X} (hx : IsRationalPoint p x) (hy : IsRationalPoint p y)
    (h : ∀ s : GlobalSections L.obj, VanishesAlong L x s → VanishesAlong L y s) :
    x ≫ C.map = y ≫ C.map := by
  obtain ⟨j, hj⟩ := exists_mem_trivializationOpen C.generates (x (IsLocalRing.closedPoint K))
  have hxj := forall_mem_of_mem hj
  obtain ⟨α, hα⟩ := exists_vanishesAlong_basisDiff p hx hxj
  have hyα := fun i ↦ h _ (hα i)
  have hyj := forall_mem_of_mem (mem_of_vanishesAlong_basisDiff p C.generates hyα)
  refine comp_eq_of_sectionRatio_eq p C.generates hxj hyj (hx.trans hy.symm) fun i ↦ ?_
  rw [(vanishesAlong_linComb_basisDiff_iff p _ hxj i (α i)).mp (hα i),
    (vanishesAlong_linComb_basisDiff_iff p _ hyj i (α i)).mp (hyα i), hx, hy]

/-- A dual-number point has constant projective image if every section vanishing at
its rational reduction pulls back to zero on the entire dual-number point. -/
lemma comp_map_eq_of_dualNumber_vanishing
    {x : Spec (CommRingCat.of K) ⟶ X} {t : Spec (CommRingCat.of (DualNumber K)) ⟶ X}
    (hx : IsRationalPoint p x) (ht : IsTangentVectorAt p x t)
    (h : ∀ s : GlobalSections L.obj, VanishesAlong L x s → VanishesAlong L t s) :
    t ≫ C.map = (dualNumberProjection K ≫ x) ≫ C.map := by
  obtain ⟨j, hj⟩ := exists_mem_trivializationOpen C.generates (x (IsLocalRing.closedPoint K))
  have hxj := forall_mem_of_mem hj
  have htj := forall_mem_of_augmentation_comp ht.2 hj
  have hx'j : ∀ τ, (dualNumberProjection K ≫ x) τ ∈ trivializationOpen L.obj (C.basis j) :=
    fun τ ↦ by rw [Scheme.Hom.comp_apply]; exact hxj _
  have hp : t ≫ p = (dualNumberProjection K ≫ x) ≫ p := by
    rw [ht.1, Category.assoc, hx, Category.comp_id]
  obtain ⟨α, hα⟩ := exists_vanishesAlong_basisDiff p hx hxj
  refine comp_eq_of_sectionRatio_eq p C.generates htj hx'j hp fun i ↦ ?_
  rw [(vanishesAlong_linComb_basisDiff_iff p _ htj i (α i)).mp (h _ (hα i)),
    (vanishesAlong_linComb_basisDiff_iff p _ hx'j i (α i)).mp
      (vanishesAlong_comp _ (hα i)), hp]

end CompleteGeneratingSystem

variable [IsAlgClosed K] [LocallyOfFiniteType p]

/-- A basis of all global sections generates everywhere provided some global section
is nonzero at each rational point. -/
lemma basis_generates_of_rational_generation {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) K ((relativeGlobalSections p).obj L.obj))
    (h : ∀ (y : Spec (CommRingCat.of K) ⟶ X), IsRationalPoint p y →
      ∃ s : GlobalSections L.obj, ¬ VanishesAlong L y s) :
    ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (b i) := by
  classical
  let U := ⨆ i, trivializationOpen L.obj (b i)
  suffices H : U = ⊤ by
    intro x
    have hx : x ∈ U := by rw [H]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    refine ⟨i, ?_⟩
    rw [lineBundleResidueOpenComparison X L (b i)]
    exact hi
  by_contra hU
  have hne : ((U : Set X)ᶜ).Nonempty := by
    simpa only [Set.nonempty_compl, Ne, ← Opens.coe_top, SetLike.coe_set_eq] using hU
  let B := Over.mk p
  have : LocallyOfFiniteType B.hom := inferInstanceAs (LocallyOfFiniteType p)
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨z, hz, hz'⟩ := nonempty_inter_closedPoints hne U.isOpen.isClosed_compl.isLocallyClosed
  obtain ⟨y, hy⟩ := ClosedRationalPoints.exists_rationalPoint_of_isClosed (X := B) z hz'
  obtain ⟨s, hs⟩ := h y.left (Over.w y)
  have hsU : ∀ τ, y.left τ ∈ trivializationOpen L.obj s :=
    forall_mem_of_mem ((not_iff_not.mpr (vanishesAlong_iff_not_mem y.left s)).mp hs |> not_not.mp)
  have hzero (i : Fin (n + 1)) : sectionRatio L y.left (b i) s = 0 := by
    apply (vanishesAlong_iff_sectionRatio_eq_zero hsU _).mp
    apply (vanishesAlong_iff_not_mem y.left (b i)).mpr
    intro hi
    apply hz
    rw [← hy]
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  have hrepr : linComb p (fun i ↦ b i) (b.equivFun s) = s := by
    exact b.sum_equivFun s
  have hlin : sectionRatio L y.left (linComb p (fun i ↦ b i) (b.equivFun s)) s = 0 := by
    erw [sectionRatio_linComb p (fun i ↦ b i) hsU]
    simp only [hzero, mul_zero, Finset.sum_const_zero]
  rw [hrepr] at hlin
  exact hs ((vanishesAlong_iff_sectionRatio_eq_zero hsU _).mpr hlin)

/-- Rational generation of a finite-dimensional section space on a nonempty scheme
provides a complete generating system. -/
lemma exists_completeGeneratingSystem [Nonempty X]
    [FiniteDimensional K ((relativeGlobalSections p).obj L.obj)]
    (h : ∀ (y : Spec (CommRingCat.of K) ⟶ X), IsRationalPoint p y →
      ∃ s : GlobalSections L.obj, ¬ VanishesAlong L y s) :
    Nonempty (CompleteGeneratingSystem p L) := by
  let B := Over.mk p
  have : LocallyOfFiniteType B.hom := inferInstanceAs (LocallyOfFiniteType p)
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨y, _⟩ := ClosedRationalPoints.exists_rationalPoint_mem (X := B) ⊤ ⟨x, by trivial⟩
  obtain ⟨s, hs⟩ := h y.left (Over.w y)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs (pullbackSection_zero _ _)
  have : Nontrivial ((relativeGlobalSections p).obj L.obj) := ⟨⟨s, 0, hs0⟩⟩
  let d := Module.finrank K ((relativeGlobalSections p).obj L.obj)
  have hd : 0 < d := Module.finrank_pos
  let b := Module.finBasisOfFinrankEq K ((relativeGlobalSections p).obj L.obj)
    (show d = (d - 1) + 1 by omega)
  exact ⟨⟨d - 1, b, basis_generates_of_rational_generation p L b h⟩⟩

end Langlands.AlgebraicGeometry.LinearSystem
