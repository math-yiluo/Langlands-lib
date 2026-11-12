import Langlands.Geometry.Building.KPMoyPrasadFiltration
import Langlands.Geometry.Building.ChamberFiltration

/-! # Separation of the original constant-depth root blocks -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {omega : kˣ → ℝ} (D : KPApartmentData i omega)
    (x : D.Apartment)

/-- V4 sends the doubled-root filtration at depth `r` into the original
root filtration at half that depth. -/
theorem filtration_double_le_half
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (h2a : 2 • a ∈ relativeRoots i) (r : ℝ) :
    D.filtration x (2 • a) r ≤ D.filtration x a (r / 2) := by
  intro g hg
  refine ⟨RelativeRoot.double_subgroup_le i a (Over.mk (𝟙 _)) hg.1, ?_⟩
  have hd := hg.2
  rw [x.isValuation.double a ha h2a g hg.1, two_nsmul] at hd
  induction hv : x.val a g using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
    rw [hv, ← WithTop.coe_add, WithTop.coe_le_coe] at hd
    rw [WithTop.coe_le_coe]
    linarith

/-- Both factors of a constant nonnegative-depth block lie in the
original root filtration at half the depth. -/
theorem filtrationBlock_subset_filtration_half
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    (r : ℝ) (hr : 0 ≤ r) :
    D.filtrationBlock x (fun _ => r) a ⊆ D.filtration x a (r / 2) := by
  intro g hg
  obtain ⟨v, hv, w, hw, rfl⟩ := D.mem_filtrationBlock.mp hg
  apply Subgroup.mul_mem _ (D.filtration_antitone x a (by linarith) hv)
  by_cases h2a : 2 • a ∈ relativeRoots i
  · rw [D.doubleFiltration_of_mem x a r h2a] at hw
    exact D.filtration_double_le_half x ha h2a r hw
  · rw [D.doubleFiltration_of_not_mem x a r h2a] at hw
    rw [Subgroup.mem_bot.mp hw]
    exact Subgroup.one_mem _

/-- The original block embeds by its unchanged value in the original
root filtration at half depth. -/
def filtrationBlockHalfDepthEmbedding
    {a : characterLattice S} (ha : a ∈ relativeRoots i) (r : NNReal) :
    D.filtrationBlock x (fun _ => (r : ℝ)) a ↪ D.filtration x a ((r : ℝ) / 2) where
  toFun g := ⟨g, D.filtrationBlock_subset_filtration_half x ha r r.coe_nonneg g.property⟩
  inj' := by
    intro g h hgh
    apply Subtype.ext
    exact congrArg
      (fun z : D.filtration x a ((r : ℝ) / 2) => (z : rationalPoints G)) hgh

@[simp]
theorem filtrationBlockHalfDepthEmbedding_val
    {a : characterLattice S} (ha : a ∈ relativeRoots i) (r : NNReal)
    (g : D.filtrationBlock x (fun _ => (r : ℝ)) a) :
    (D.filtrationBlockHalfDepthEmbedding x ha r g : rationalPoints G) = g := rfl

/-- An actual root element of every finite nonnegative depth is trivial. -/
theorem eq_one_of_forall_mem_filtration
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {g : rationalPoints G} (hg : ∀ r : NNReal, g ∈ D.filtration x a r) : g = 1 := by
  have hroot := (hg 0).1
  induction hv : x.val a g using WithTop.recTopCoe with
  | top => exact (x.isValuation.eq_top_iff a ha g hroot).mp hv
  | coe t =>
    let r : NNReal := ⟨max (t + 1) 0, le_max_right _ _⟩
    have hd := (hg r).2
    rw [hv, WithTop.coe_le_coe] at hd
    change max (t + 1) 0 ≤ t at hd
    have hb := le_max_left (t + 1) 0
    exfalso
    linarith

/-- Constant-depth blocks are separated while retaining their doubled
root factors. -/
theorem eq_one_of_forall_mem_filtrationBlock
    {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {g : rationalPoints G}
    (hg : ∀ r : NNReal, g ∈ D.filtrationBlock x (fun _ => (r : ℝ)) a) : g = 1 := by
  apply D.eq_one_of_forall_mem_filtration x ha
  intro r
  have h := D.filtrationBlock_subset_filtration_half x ha
    ((2 * r : NNReal) : ℝ) (2 * r).coe_nonneg (hg (2 * r))
  change g ∈ D.filtration x a (((2 * r : NNReal) : ℝ) / 2) at h
  have heq : ((2 * r : NNReal) : ℝ) / 2 = (r : ℝ) := by
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    ring
  rw [heq] at h
  exact h

/-- Raising the constant depth shrinks both original root-block factors. -/
theorem filtrationBlock_antitone (a : characterLattice S) :
    Antitone (fun r : ℝ => D.filtrationBlock x (fun _ => r) a) := by
  intro r s hrs g hg
  obtain ⟨v, hv, w, hw, rfl⟩ := D.mem_filtrationBlock.mp hg
  refine D.mem_filtrationBlock.mpr
    ⟨v, D.filtration_antitone x a hrs hv, w, ?_, rfl⟩
  by_cases h2a : 2 • a ∈ relativeRoots i
  · rw [D.doubleFiltration_of_mem x a s h2a] at hw
    rw [D.doubleFiltration_of_mem x a r h2a]
    exact D.filtration_antitone x (2 • a) hrs hw
  · rw [D.doubleFiltration_of_not_mem x a s h2a] at hw
    rw [D.doubleFiltration_of_not_mem x a r h2a]
    exact hw

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {P : ParahoricBuildingData G} (Zf : P.CentralizerFiltration)
    (x : P.Apartment)
    {nneg npos : ℕ}
    (aneg : Fin nneg → characterLattice P.S) (apos : Fin npos → characterLattice P.S)

/-- One fixed ordering suffices for separation. Injectivity at depth one
identifies its coordinates across all deeper covering products. -/
theorem iInf_moyPrasad_eq_bot_of_ordered_cover
    (hneg : ∀ j, aneg j ∈ relativeRoots P.i)
    (hpos : ∀ j, apos j ∈ relativeRoots P.i)
    (hinj : Function.Injective (fun p :
      (∀ j, P.apartment.filtrationBlock x (fun _ => (1 : ℝ)) (aneg j)) ×
        Zf.filtration 1 ×
        (∀ j, P.apartment.filtrationBlock x (fun _ => (1 : ℝ)) (apos j)) =>
      P.apartment.orderedFiltrationBlockProduct x (fun _ => (1 : ℝ)) aneg p.1 *
        rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
        P.apartment.orderedFiltrationBlockProduct x (fun _ => (1 : ℝ)) apos p.2.2))
    (hcover : ∀ r : NNReal, 0 < r →
      Set.range (fun p :
        (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (aneg j)) ×
          Zf.filtration r ×
          (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (apos j)) =>
        P.apartment.orderedFiltrationBlockProduct x (fun _ => (r : ℝ)) aneg p.1 *
          rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
          P.apartment.orderedFiltrationBlockProduct x (fun _ => (r : ℝ)) apos p.2.2) =
        (Zf.moyPrasad x r : Set (rationalPoints G))) :
    ⨅ r, Zf.moyPrasad x r = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  apply Subgroup.mem_bot.mpr
  let C (r : NNReal) :=
    (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (aneg j)) ×
      Zf.filtration r ×
      (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (apos j))
  have hgin (r : NNReal) : g ∈ (Zf.moyPrasad x r : Set (rationalPoints G)) :=
    Subgroup.mem_iInf.mp hg r
  have hg1 := hgin 1
  rw [← hcover 1 zero_lt_one] at hg1
  obtain ⟨p0, hp0⟩ := hg1
  have hdeep (r : NNReal) :
      (∀ j, (p0.1 j : rationalPoints G) ∈
        P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (aneg j)) ∧
      (p0.2.1 : rationalPoints P.centralizer.Z) ∈ Zf.filtration r ∧
      (∀ j, (p0.2.2 j : rationalPoints G) ∈
        P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (apos j)) := by
    have hrpos : 0 < r + 1 := by positivity
    have hrone : (1 : NNReal) ≤ r + 1 := by simp
    have hrle : r ≤ r + 1 := by simp
    have hgr := hgin (r + 1)
    rw [← hcover (r + 1) hrpos] at hgr
    obtain ⟨p, hp⟩ := hgr
    let q : C 1 :=
      (fun j => ⟨p.1 j, P.apartment.filtrationBlock_antitone x (aneg j)
        (NNReal.coe_le_coe.mpr hrone) (p.1 j).property⟩,
      ⟨p.2.1, Zf.antitone hrone p.2.1.property⟩,
      fun j => ⟨p.2.2 j, P.apartment.filtrationBlock_antitone x (apos j)
        (NNReal.coe_le_coe.mpr hrone) (p.2.2 j).property⟩)
    have hq : q = p0 := hinj (hp.trans hp0.symm)
    refine ⟨?_, ?_, ?_⟩
    · intro j
      have hj : (p.1 j : rationalPoints G) = (p0.1 j : rationalPoints G) :=
        congrArg (fun t : C 1 => (t.1 j : rationalPoints G)) hq
      rw [← hj]
      exact P.apartment.filtrationBlock_antitone x (aneg j)
        (NNReal.coe_le_coe.mpr hrle) (p.1 j).property
    · have hz : (p.2.1 : rationalPoints P.centralizer.Z) =
          (p0.2.1 : rationalPoints P.centralizer.Z) :=
        congrArg (fun t : C 1 => (t.2.1 : rationalPoints P.centralizer.Z)) hq
      rw [← hz]
      exact Zf.antitone hrle p.2.1.property
    · intro j
      have hj : (p.2.2 j : rationalPoints G) = (p0.2.2 j : rationalPoints G) :=
        congrArg (fun t : C 1 => (t.2.2 j : rationalPoints G)) hq
      rw [← hj]
      exact P.apartment.filtrationBlock_antitone x (apos j)
        (NNReal.coe_le_coe.mpr hrle) (p.2.2 j).property
  have hn (j : Fin nneg) : (p0.1 j : rationalPoints G) = 1 :=
    P.apartment.eq_one_of_forall_mem_filtrationBlock x (hneg j) (fun r => (hdeep r).1 j)
  have hp (j : Fin npos) : (p0.2.2 j : rationalPoints G) = 1 :=
    P.apartment.eq_one_of_forall_mem_filtrationBlock x (hpos j) (fun r => (hdeep r).2.2 j)
  have hzmem : (p0.2.1 : rationalPoints P.centralizer.Z) ∈ ⨅ r, Zf.filtration r :=
    Subgroup.mem_iInf.mpr (fun r => (hdeep r).2.1)
  rw [Zf.separated] at hzmem
  have hz := Subgroup.mem_bot.mp hzmem
  rw [← hp0]
  simp only [KPApartmentData.orderedFiltrationBlockProduct, hn, hp, hz, map_one,
    List.ofFn_const, List.prod_replicate, one_pow, one_mul]

end Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration
