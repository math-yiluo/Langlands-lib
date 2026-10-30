import Langlands.AlgebraicGeometry.Picard.FiniteSectionAvoidanceStatement
import Langlands.AlgebraicGeometry.Picard.AlgebraicExtensionAmpleExistenceSpreadingProof
import Langlands.AlgebraicGeometry.Modules.SectionResidueComparison
import Mathlib.Topology.Specialization

/-! # Finite-set section avoidance from a basis of section generation opens

Membership in the generation open of a section of a tensor power of a line bundle is detected
by its residue-field value, which is additive in the section. Two sections are combined by
raising them to a common positive degree and adding them; an induction on the number of points
then removes, at each step, a point that is not a proper specialization of another point. -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

namespace FiniteSectionAvoidance

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The morphism from the structure module attached to a sum of global sections is the sum
of the two morphisms. -/
theorem sectionHom_add (M : X.Modules) (s t : GlobalSections M) :
    sectionHom M (s + t) = sectionHom M s + sectionHom M t := by
  have key : ∀ (φ : structureModule X ⟶ M) (U : X.Opens) (a : Γ(X, U)),
      φ.app U a = a • φ.app U (1 : Γ(X, U)) := by
    intro φ U a
    have hs := φ.app_smul a (1 : Γ(X, U))
    change φ.app U (a * (1 : Γ(X, U))) = a • φ.app U (1 : Γ(X, U)) at hs
    simpa only [mul_one] using hs
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  change Γ(X, U) at a
  rw [key (sectionHom M (s + t)), key (sectionHom M s + sectionHom M t),
    Scheme.Modules.Hom.add_app, AddCommGrpCat.hom_add_apply, sectionHom_app_one,
    sectionHom_app_one, sectionHom_app_one, map_add, smul_add]

set_option backward.isDefEq.respectTransparency false in
/-- The residue-field value of a sum of global sections is the sum of the values. -/
theorem residueSection_add (M : X.Modules) (s t : GlobalSections M) (x : X) :
    residueSection M (s + t) x = residueSection M s x + residueSection M t x := by
  change ((pullbackUnitIso (X.fromSpecResidueField x)).inv ≫
      (Scheme.Modules.pullback (X.fromSpecResidueField x)).map (sectionHom M (s + t))).app ⊤
        (1 : Γ(Spec (X.residueField x), ⊤)) = _
  rw [sectionHom_add, Functor.map_add, Preadditive.comp_add, Scheme.Modules.Hom.add_app,
    AddCommGrpCat.hom_add_apply]
  rfl

/-- The residue-field value at a point, as an additive map on global sections. -/
noncomputable def residueHom (M : X.Modules) (x : X) :
    GlobalSections M →+ GlobalSections (residueFibre M x) :=
  AddMonoidHom.mk' (fun s ↦ residueSection M s x) fun s t ↦ residueSection_add M s t x

/-- A point lies in the generation open of a section of a tensor power of a line bundle
exactly when the section has nonzero residue-field value at the point. -/
theorem mem_sectionOpen_iff (L : LineBundle X) {n : ℕ} (s : L.powSections n) (x : X) :
    x ∈ L.sectionOpen s ↔ residueHom (tensorPow L.obj n) x s ≠ 0 := by
  have h : nonvanishingLocus (tensorPow L.obj n) s =
      (trivializationOpen (tensorPow L.obj n) s : Set X) :=
    lineBundleResidueOpenComparison X ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩ s
  change x ∈ (trivializationOpen (tensorPow L.obj n) s : Set X) ↔ _
  rw [← h]
  exact Iff.rfl

/-- Two sections of positive tensor powers, raised to the common degree `n * m` and added,
give a section whose generation open lies in the union of the two generation opens and
contains every point lying in exactly one of them. -/
theorem exists_combined_section (L : LineBundle X) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (t : L.powSections n) (v : L.powSections m) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ w : L.powSections N,
      (L.sectionOpen w : Set X) ⊆ (L.sectionOpen t : Set X) ∪ L.sectionOpen v ∧
      (∀ x, x ∈ L.sectionOpen t → x ∉ L.sectionOpen v → x ∈ L.sectionOpen w) ∧
      (∀ x, x ∉ L.sectionOpen t → x ∈ L.sectionOpen v → x ∈ L.sectionOpen w) := by
  have hN : 0 < n * m := Nat.mul_pos hn hm
  obtain ⟨t', ht'⟩ := exists_trivializationOpen_eq_of_dvd L hN (dvd_mul_right n m) t
  obtain ⟨v', hv'⟩ := exists_trivializationOpen_eq_of_dvd L hN (dvd_mul_left m n) v
  have hmt : ∀ x, x ∈ L.sectionOpen t ↔ residueHom (tensorPow L.obj (n * m)) x t' ≠ 0 := by
    intro x
    have h : L.sectionOpen t' = L.sectionOpen t := ht'
    rw [← h]
    exact mem_sectionOpen_iff L t' x
  have hmv : ∀ x, x ∈ L.sectionOpen v ↔ residueHom (tensorPow L.obj (n * m)) x v' ≠ 0 := by
    intro x
    have h : L.sectionOpen v' = L.sectionOpen v := hv'
    rw [← h]
    exact mem_sectionOpen_iff L v' x
  refine ⟨n * m, hN, t' + v', ?_, ?_, ?_⟩
  · intro x hx
    rw [SetLike.mem_coe, mem_sectionOpen_iff, map_add] at hx
    by_cases h1 : residueHom (tensorPow L.obj (n * m)) x t' = 0
    · right
      rw [SetLike.mem_coe, hmv]
      rwa [h1, zero_add] at hx
    · left
      rw [SetLike.mem_coe, hmt]
      exact h1
  · intro x hxt hxv
    rw [hmt] at hxt
    rw [hmv, not_not] at hxv
    rw [mem_sectionOpen_iff, map_add, hxv, add_zero]
    exact hxt
  · intro x hxt hxv
    rw [hmt, not_not] at hxt
    rw [hmv] at hxv
    rw [mem_sectionOpen_iff, map_add, hxt, zero_add]
    exact hxv

end FiniteSectionAvoidance

open FiniteSectionAvoidance in
/-- If the generation opens of sections of positive tensor powers of a line bundle form a
basis of the topology, then every finite set of points in an open `W` lies in the generation
open of one section of a positive tensor power, with that generation open contained in `W`. -/
theorem finiteSectionAvoidance : FiniteSectionAvoidanceStatement.{u} := by
  intro X L hbasis
  suffices h : ∀ (k : ℕ) (E : Set X) (W : X.Opens), E.Finite → E.ncard = k →
      E ⊆ (W : Set X) → ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
        E ⊆ (L.sectionOpen s : Set X) ∧ L.sectionOpen s ≤ W by
    intro E W hE hEW
    exact h _ E W hE rfl hEW
  intro k
  induction k with
  | zero =>
    intro E W hE hk _
    have hE0 : E = ∅ := (Set.ncard_eq_zero hE).mp hk
    subst hE0
    refine ⟨1, le_rfl, 0, Set.empty_subset _, fun x hx ↦ ?_⟩
    exact absurd (map_zero _) ((mem_sectionOpen_iff L (0 : L.powSections 1) x).mp hx)
  | succ k ih =>
    intro E W hE hk hEW
    obtain ⟨a, haE, hmax⟩ := Set.Finite.exists_maximalFor
      (Specialization.toEquiv : X → Specialization X) E hE
      (Set.nonempty_of_ncard_ne_zero (by rw [hk]; exact Nat.succ_ne_zero k))
    have hE0 : (E \ {a}).Finite := hE.subset fun y hy ↦ hy.1
    have hk0 : (E \ {a}).ncard = k := by
      rw [Set.ncard_sdiff_singleton_of_mem haE, hk, Nat.add_sub_cancel]
    obtain ⟨n, hn, t, hEt, htW⟩ := ih (E \ {a}) W hE0 hk0 fun y hy ↦ hEW hy.1
    by_cases hat : a ∈ L.sectionOpen t
    · refine ⟨n, hn, t, fun y hy ↦ ?_, htW⟩
      by_cases hya : y = a
      · rw [hya]
        exact hat
      · exact hEt ⟨hy, hya⟩
    · -- The union of the closures of the other points is closed and avoids `a`.
      let C : Set X := ⋃ y ∈ E \ {a}, closure ({y} : Set X)
      have hCc : IsClosed C := hE0.isClosed_biUnion fun y _ ↦ isClosed_closure
      let W' : X.Opens := W ⊓ ⟨Cᶜ, hCc.isOpen_compl⟩
      have haW' : a ∈ W' := by
        refine Opens.mem_inf.mpr ⟨hEW haE, ?_⟩
        intro haC
        obtain ⟨y, hy, hay⟩ := Set.mem_iUnion₂.mp haC
        have hya : y ⤳ a := specializes_iff_mem_closure.mpr hay
        have hay' : a ⤳ y := Specialization.toEquiv_le_toEquiv.mp
          (hmax hy.1 (Specialization.toEquiv_le_toEquiv.mpr hya))
        exact hat (hay'.mem_open (L.sectionOpen t).isOpen (hEt hy))
      obtain ⟨m, hm, v, hav, hvW'⟩ := hbasis W' a haW'
      obtain ⟨N, hN, w, hwsub, hw1, hw2⟩ := exists_combined_section L hn hm t v
      refine ⟨N, hN, w, fun y hy ↦ ?_, fun x hx ↦ ?_⟩
      · by_cases hya : y = a
        · rw [hya]
          exact hw2 a hat hav
        · have hyt : y ∈ L.sectionOpen t := hEt ⟨hy, hya⟩
          refine hw1 y hyt fun hyv ↦ ?_
          have hyC : y ∈ C := Set.mem_iUnion₂.mpr ⟨y, ⟨hy, hya⟩, subset_closure rfl⟩
          exact (Opens.mem_inf.mp (hvW' hyv)).2 hyC
      · rcases hwsub hx with hxt | hxv
        · exact htW hxt
        · exact (Opens.mem_inf.mp (hvW' hxv)).1

end Langlands.AlgebraicGeometry.Picard
