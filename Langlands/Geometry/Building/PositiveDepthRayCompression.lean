import Langlands.Geometry.Building.PositiveDepthCollection
import Langlands.Geometry.Building.ChamberPositiveCollection

/-! # Collection with actual primitive and doubled-root ray factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

/-- Adjacent comparable subgroups can be replaced by their supremum in an
ordered product. The dominant subgroup may be either member of each pair. -/
theorem range_orderedProduct_rayPairs {M : Type*} [Group M] {n : ℕ}
    (H : Fin (n * 2) → Subgroup M) (K : Fin n → Subgroup M)
    (hsup : ∀ j, K j = H (finProdFinEquiv (j, 0)) ⊔
      H (finProdFinEquiv (j, 1)))
    (hcomp : ∀ j, H (finProdFinEquiv (j, 1)) ≤ H (finProdFinEquiv (j, 0)) ∨
      H (finProdFinEquiv (j, 0)) ≤ H (finProdFinEquiv (j, 1))) :
    Set.range (RelativeRoot.CentralExtension.orderedProduct (fun l => (H l).subtype)) =
      Set.range (RelativeRoot.CentralExtension.orderedProduct (fun j => (K j).subtype)) := by
  classical
  have h0 (j) : H (finProdFinEquiv (j, 0)) ≤ K j := by rw [hsup]; exact le_sup_left
  have h1 (j) : H (finProdFinEquiv (j, 1)) ≤ K j := by rw [hsup]; exact le_sup_right
  ext g
  constructor
  · rintro ⟨t, rfl⟩
    let s : ∀ j, K j := fun j =>
      ⟨(t (finProdFinEquiv (j, 0)) : M) * (t (finProdFinEquiv (j, 1)) : M),
        (K j).mul_mem (h0 j (t _).property) (h1 j (t _).property)⟩
    exact ⟨s, (prod_ofFn_pairs (fun l => (t l : M))).symm⟩
  · rintro ⟨s, rfl⟩
    have hsplit (j) : ∃ x : H (finProdFinEquiv (j, 0)),
        ∃ y : H (finProdFinEquiv (j, 1)), (x : M) * y = s j := by
      rcases hcomp j with h | h
      · have hj : K j = H (finProdFinEquiv (j, 0)) := by
          rw [hsup, sup_eq_left.mpr h]
        exact ⟨⟨s j, hj ▸ (s j).property⟩, 1, mul_one _⟩
      · have hj : K j = H (finProdFinEquiv (j, 1)) := by
          rw [hsup, sup_eq_right.mpr h]
        exact ⟨1, ⟨s j, hj ▸ (s j).property⟩, one_mul _⟩
    choose x y hxy using hsplit
    let t : ∀ l, H l := fun l =>
      if h : (finProdFinEquiv.symm l).2 = 0 then
        ⟨x (finProdFinEquiv.symm l).1, by
          have he : finProdFinEquiv ((finProdFinEquiv.symm l).1, 0) = l := by
            rw [← h]
            exact finProdFinEquiv.apply_symm_apply l
          have hh := congrArg H he
          exact hh ▸ (x _).property⟩
      else
        ⟨y (finProdFinEquiv.symm l).1, by
          have h' : (finProdFinEquiv.symm l).2 = 1 := by omega
          have he : finProdFinEquiv ((finProdFinEquiv.symm l).1, 1) = l := by
            rw [← h']
            exact finProdFinEquiv.apply_symm_apply l
          have hh := congrArg H he
          exact hh ▸ (y _).property⟩
    refine ⟨t, ?_⟩
    unfold RelativeRoot.CentralExtension.orderedProduct
    rw [prod_ofFn_pairs]
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext j
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [t, Equiv.symm_apply_apply, h10, dite_true, dite_false,
      Subgroup.subtype_apply]
    exact (congrArg₂ (· * ·)
      (congrArg (fun p : Fin n × Fin 2 => (x p.1 : M))
        (finProdFinEquiv.symm_apply_apply (j, (0 : Fin 2))))
      (congrArg (fun p : Fin n × Fin 2 => (y p.1 : M))
        (finProdFinEquiv.symm_apply_apply (j, (1 : Fin 2))))).trans (hxy j)

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {φ : RootFunctionFamily S G}

/-- The actual factor retained on a root ray. If only the doubled root was
selected, both its root-group membership and its depth are retained. -/
def rootRayDepthSet (i : S.toGrp ⟶ G) (φ : RootFunctionFamily S G)
    (Ψ : Set (characterLattice S)) (f : characterLattice S → ℝ)
    (a : characterLattice S) : Set (rationalPoints G) := by
  classical
  exact if a ∈ Ψ then rootFiltration i φ a (f a)
    else if 2 • a ∈ Ψ then rootFiltration i φ (2 • a) (f (2 • a))
    else {1}

/-- Actual ordered products of the retained ray factors. -/
def orderedRootRayDepthProduct (i : S.toGrp ⟶ G) (φ : RootFunctionFamily S G)
    (Ψ : Set (characterLattice S)) (f : characterLattice S → ℝ)
    {n : ℕ} (a : Fin n → characterLattice S) : Set (rationalPoints G) :=
  {g | ∃ x : ∀ j, rootRayDepthSet i φ Ψ f (a j),
    (List.ofFn fun j => (x j : rationalPoints G)).prod = g}

namespace IsRootDatumValuation

/-- V4 gives the exact arbitrary-depth inclusion for doubled roots. -/
theorem filtrationSubgroup_double_le (hφ : IsRootDatumValuation i φ)
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (h2a : 2 • a ∈ relativeRoots i) {r s : ℝ} (hrs : 2 * r ≤ s) :
    hφ.filtrationSubgroup (2 • a) s ≤ hφ.filtrationSubgroup a r := by
  intro u hu
  refine ⟨RelativeRoot.double_subgroup_le i a (Over.mk (𝟙 _)) hu.1, ?_⟩
  have hd := hu.2
  rw [hφ.double a ha h2a u hu.1, two_nsmul] at hd
  induction hv : φ a u using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
    rw [hv, ← WithTop.coe_add, WithTop.coe_le_coe] at hd
    rw [WithTop.coe_le_coe]
    linarith

/-- A selected filtration subgroup, or the identity subgroup at an unselected
root. This does not replace an unselected primitive root by a selected one. -/
def selectedDepthSubgroup (hφ : IsRootDatumValuation i φ)
    (Ψ : Set (characterLattice S)) (f : characterLattice S → ℝ)
    (a : characterLattice S) : Subgroup (rationalPoints G) := by
  classical
  exact if a ∈ Ψ then hφ.filtrationSubgroup a (f a) else ⊥

/-- The ray factor with subgroup structure from V1. Its literal carrier is
`rootRayDepthSet`, including the doubled-root-only branch. -/
def rootRayDepthSubgroup (hφ : IsRootDatumValuation i φ)
    (Ψ : Set (characterLattice S)) (f : characterLattice S → ℝ)
    (a : characterLattice S) : Subgroup (rationalPoints G) := by
  classical
  exact (if a ∈ Ψ then hφ.filtrationSubgroup a (f a)
    else if 2 • a ∈ Ψ then hφ.filtrationSubgroup (2 • a) (f (2 • a)) else ⊥).copy
      (rootRayDepthSet i φ Ψ f a) (by
        unfold rootRayDepthSet
        split_ifs <;> rfl)

theorem coe_rootRayDepthSubgroup (hφ : IsRootDatumValuation i φ)
    (Ψ : Set (characterLattice S)) (f : characterLattice S → ℝ)
    (a : characterLattice S) :
    (hφ.rootRayDepthSubgroup Ψ f a : Set (rationalPoints G)) =
      rootRayDepthSet i φ Ψ f a := rfl

theorem rootRayDepthSubgroup_le_rootGroupPoints (hφ : IsRootDatumValuation i φ)
    (Ψ : Set (characterLattice S)) (f : characterLattice S → ℝ)
    (a : characterLattice S) :
    hφ.rootRayDepthSubgroup Ψ f a ≤ rootGroupPoints i a := by
  intro g hg
  change g ∈ rootRayDepthSet i φ Ψ f a at hg
  unfold rootRayDepthSet at hg
  split_ifs at hg with ha h2a
  · exact hg.1
  · exact RelativeRoot.double_subgroup_le i a (Over.mk (𝟙 _)) hg.1
  · exact (Set.mem_singleton_iff.mp hg) ▸ (rootGroupPoints i a).one_mem

/-- When both roots are selected, the displayed depth inequality is precisely
what is needed to absorb the doubled-root subgroup into the primitive one. -/
theorem rootRayDepthSubgroup_eq_sup (hφ : IsRootDatumValuation i φ)
    {Ψ : Set (characterLattice S)} {f : characterLattice S → ℝ}
    (hroots : Ψ ⊆ relativeRoots i)
    (hdouble : ∀ a ∈ Ψ, 2 • a ∈ Ψ → 2 * f a ≤ f (2 • a))
    (a : characterLattice S) :
    hφ.rootRayDepthSubgroup Ψ f a =
      hφ.selectedDepthSubgroup Ψ f a ⊔ hφ.selectedDepthSubgroup Ψ f (2 • a) := by
  classical
  simp only [rootRayDepthSubgroup, Subgroup.copy_eq, selectedDepthSubgroup]
  by_cases ha : a ∈ Ψ
  · by_cases h2a : 2 • a ∈ Ψ
    · simp only [ha, h2a, ite_true]
      exact (sup_eq_left.mpr
        (hφ.filtrationSubgroup_double_le (hroots ha) (hroots h2a)
          (hdouble a ha h2a))).symm
    · simp only [ha, h2a, ite_true, ite_false, sup_bot_eq]
  · simp only [ha, ite_false, bot_sup_eq]

end IsRootDatumValuation

variable (hφ : IsRootDatumValuation i φ)
  {ν : cocharacterLattice S} {Ψ : Set (characterLattice S)}
  {f : characterLattice S → ℝ} (hdata : IsClosedPositiveRootDepth i ν Ψ f)

include hφ hdata

/-- Collection allows a finite list containing extra unselected entries,
which contribute the identity subgroup. -/
theorem range_selectedDepthProduct_eq_iSup
    {n : ℕ} (a : Fin n → characterLattice S) (hcover : Ψ ⊆ Set.range a) :
    Set.range (RelativeRoot.CentralExtension.orderedProduct
      (fun j => (hφ.selectedDepthSubgroup Ψ f (a j)).subtype)) =
        ((⨆ c : Ψ, hφ.filtrationSubgroup c (f c) : Subgroup (rationalPoints G)) :
          Set (rationalPoints G)) := by
  classical
  let H := fun j => hφ.selectedDepthSubgroup Ψ f (a j)
  have hcollect : Set.range (RelativeRoot.CentralExtension.orderedProduct
      (fun j => (H j).subtype)) = ((⨆ j, H j : Subgroup (rationalPoints G)) :
        Set (rationalPoints G)) := by
    apply Langlands.GroupTheory.HeightCollection.range_orderedProduct_eq_iSup
      (w := fun j => (latticePairing S (a j) ν).toNat)
    intro j k
    by_cases hj : a j ∈ Ψ
    · by_cases hk : a k ∈ Ψ
      · have hjH : H j = hφ.filtrationSubgroup (a j) (f (a j)) := ite_eq_left hj
        have hkH : H k = hφ.filtrationSubgroup (a k) (f (a k)) := ite_eq_left hk
        rw [hjH, hkH]
        refine (positiveDepth_commutator_height hφ hdata hj hk).trans ?_
        refine iSup_le fun c => iSup_le fun hc => ?_
        obtain ⟨l, hl⟩ := hcover c.2
        exact le_iSup_of_le l (le_iSup_of_le (hl.symm ▸ hc)
          (by dsimp only [H, IsRootDatumValuation.selectedDepthSubgroup]
              rw [hl, ite_eq_left c.2]))
      · simp only [H, IsRootDatumValuation.selectedDepthSubgroup, ite_eq_right hk,
          Subgroup.commutator_bot_right, bot_le]
    · simp only [H, IsRootDatumValuation.selectedDepthSubgroup, ite_eq_right hj,
        Subgroup.commutator_bot_left, bot_le]
  rw [hcollect]
  apply congrArg (fun H : Subgroup (rationalPoints G) => (H : Set (rationalPoints G)))
  apply le_antisymm
  · refine iSup_le fun j => ?_
    dsimp only [H, IsRootDatumValuation.selectedDepthSubgroup]
    split_ifs with hj
    · exact le_iSup_of_le (⟨a j, hj⟩ : Ψ) le_rfl
    · exact bot_le
  · refine iSup_le fun c => ?_
    obtain ⟨j, hj⟩ := hcover c.2
    exact le_iSup_of_le j (by
      dsimp only [H, IsRootDatumValuation.selectedDepthSubgroup]
      rw [hj, ite_eq_left c.2])

/-- Arbitrary-depth collection compressed to the supplied primitive/double
positions. A selected doubled root whose primitive is absent is retained as
an actual doubled-root factor at its original depth. -/
theorem orderedRootRayDepthProduct_eq_iSup
    (hdouble : ∀ a ∈ Ψ, 2 • a ∈ Ψ → 2 * f a ≤ f (2 • a))
    {n : ℕ} (a : Fin n → characterLattice S)
    (hcover : ∀ b ∈ Ψ, ∃ j, b = a j ∨ b = 2 • a j) :
    orderedRootRayDepthProduct i φ Ψ f a =
      ((⨆ c : Ψ, hφ.filtrationSubgroup c (f c) : Subgroup (rationalPoints G)) :
        Set (rationalPoints G)) := by
  classical
  let c : Fin (n * 2) → characterLattice S := fun l =>
    if (finProdFinEquiv.symm l).2 = 0 then a (finProdFinEquiv.symm l).1
      else 2 • a (finProdFinEquiv.symm l).1
  let H := fun l => hφ.selectedDepthSubgroup Ψ f (c l)
  let K := fun j => hφ.rootRayDepthSubgroup Ψ f (a j)
  have hc0 (j : Fin n) : c (finProdFinEquiv (j, 0)) = a j := by
    simp only [c, Equiv.symm_apply_apply, ite_true]
  have hc1 (j : Fin n) : c (finProdFinEquiv (j, 1)) = 2 • a j := by
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [c, Equiv.symm_apply_apply, ite_eq_right h10]
  have hcover' : Ψ ⊆ Set.range c := by
    intro b hb
    obtain ⟨j, hj | hj⟩ := hcover b hb
    · exact ⟨finProdFinEquiv (j, 0), (hc0 j).trans hj.symm⟩
    · exact ⟨finProdFinEquiv (j, 1), (hc1 j).trans hj.symm⟩
  have hsup (j) : K j = H (finProdFinEquiv (j, 0)) ⊔
      H (finProdFinEquiv (j, 1)) := by
    dsimp only [K, H]
    rw [hc0, hc1]
    exact hφ.rootRayDepthSubgroup_eq_sup (fun _ hb => (hdata.positive hb).1)
      hdouble (a j)
  have hcomp (j) :
      H (finProdFinEquiv (j, 1)) ≤ H (finProdFinEquiv (j, 0)) ∨
      H (finProdFinEquiv (j, 0)) ≤ H (finProdFinEquiv (j, 1)) := by
    dsimp only [H]
    rw [hc0, hc1]
    by_cases hj : a j ∈ Ψ
    · left
      by_cases h2j : 2 • a j ∈ Ψ
      · simpa only [IsRootDatumValuation.selectedDepthSubgroup, ite_eq_left hj, ite_eq_left h2j] using
          hφ.filtrationSubgroup_double_le (hdata.positive hj).1
            (hdata.positive h2j).1 (hdouble _ hj h2j)
      · simp only [IsRootDatumValuation.selectedDepthSubgroup, ite_eq_right h2j, bot_le]
    · right
      simp only [IsRootDatumValuation.selectedDepthSubgroup, ite_eq_right hj, bot_le]
  change Set.range (RelativeRoot.CentralExtension.orderedProduct
    (fun j => (K j).subtype)) = _
  rw [← range_orderedProduct_rayPairs H K hsup hcomp]
  exact range_selectedDepthProduct_eq_iSup hφ hdata c hcover'

end Langlands.Geometry.Building
