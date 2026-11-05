import Langlands.Geometry.Building.ChamberIwahoriStatement
import Langlands.Geometry.Building.ChamberFiltration
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Extracting one root factor from the chamber Iwahori product -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- Enumerate the positive indivisible relative roots with a prescribed root last. -/
theorem exists_indivisiblePositiveRoots_enumeration_last
    (ν : cocharacterLattice P.S) {a : characterLattice P.S}
    (ha : a ∈ RelativeRoot.indivisiblePositiveRoots P.i ν) :
    ∃ (n : ℕ) (b : Fin (n + 1) → characterLattice P.S),
      Function.Injective b ∧ Set.range b = RelativeRoot.indivisiblePositiveRoots P.i ν ∧
        b (Fin.last n) = a := by
  classical
  have := P.isConnectedReductive.smooth
  have ht : IsSplitTorus P.S.toGrp := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hfinite : (RelativeRoot.indivisiblePositiveRoots P.i ν).Finite :=
    (ht.finite_relativeRoots P.i).subset (fun _ h => h.1.1)
  have hremove : (RelativeRoot.indivisiblePositiveRoots P.i ν \ {a}).Finite :=
    hfinite.sdiff
  obtain ⟨n, b, hbi, hbr⟩ := hremove.fin_param
  have hb (j : Fin n) : b j ∈ RelativeRoot.indivisiblePositiveRoots P.i ν ∧ b j ≠ a := by
    have h := hbr ▸ (Set.mem_range_self j : b j ∈ Set.range b)
    simpa only [Set.mem_sdiff, Set.mem_singleton_iff] using h
  refine ⟨n, Fin.lastCases a b, ?_, ?_, by simp⟩
  · intro j k hjk
    induction j using Fin.lastCases with
    | last =>
      induction k using Fin.lastCases with
      | last => rfl
      | cast k =>
        exact False.elim ((hb k).2 (by simpa using hjk.symm))
    | cast j =>
      induction k using Fin.lastCases with
      | last => exact False.elim ((hb j).2 (by simpa using hjk))
      | cast k =>
        exact congrArg Fin.castSucc (hbi (by simpa using hjk))
  · ext c
    constructor
    · rintro ⟨j, rfl⟩
      induction j using Fin.lastCases with
      | last => simpa using ha
      | cast j => simpa using (hb j).1
    · intro hc
      by_cases hca : c = a
      · exact ⟨Fin.last n, by simpa using hca.symm⟩
      · obtain ⟨j, rfl⟩ := (show c ∈ Set.range b from hbr.symm ▸ ⟨hc, hca⟩)
        exact ⟨j.castSucc, by simp⟩

/-- Ordered root coordinates with a chosen positive root in the final position. -/
def lastRootEnumeration (ν : cocharacterLattice P.S) {a : characterLattice P.S}
    (ha : a ∈ RelativeRoot.indivisiblePositiveRoots P.i ν) :
    Σ n : ℕ, {b : Fin (n + 1) → characterLattice P.S //
      Function.Injective b ∧ Set.range b = RelativeRoot.indivisiblePositiveRoots P.i ν ∧
        b (Fin.last n) = a} :=
  ⟨_, _, (P.exists_indivisiblePositiveRoots_enumeration_last ν ha).choose_spec.choose_spec⟩

/-- Extract the selected final root from the chamber product. All other root
filtrations are absorbed by `K`, and only the selected filtration needs a split. -/
theorem exists_mul_of_chamberIwahoriConclusion
    {C : Set P.Apartment} {x : P.Apartment} {ν : cocharacterLattice P.S}
    (hdec : P.ChamberIwahoriConclusion C x ν)
    {a : characterLattice P.S}
    (ha : a ∈ RelativeRoot.indivisiblePositiveRoots P.i ν)
    (K U : Subgroup (rationalPoints G))
    (hZ : P.centralizerZero.map (rationalPoints.map P.centralizer.j) ≤ K)
    (hother : ∀ c : characterLattice P.S, c ∈ RelativeRoot.indivisibleRoots P.i → c ≠ a →
      P.apartment.filtration x c 0 ≤ K)
    (hsplit : ∀ g ∈ P.apartment.filtration x a 0,
      ∃ k ∈ K, ∃ u ∈ U, g = k * u)
    {g : rationalPoints G} (hg : g ∈ P.parahoric C) :
    ∃ k ∈ K, ∃ u ∈ U, g = k * u := by
  classical
  have := P.isConnectedReductive.smooth
  have ht : IsSplitTorus P.S.toGrp := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hfinite : (RelativeRoot.indivisiblePositiveRoots P.i (-ν)).Finite :=
    (ht.finite_relativeRoots P.i).subset (fun _ h => h.1.1)
  obtain ⟨m, aneg, hni, hnr⟩ := hfinite.fin_param
  obtain ⟨n, apos, hpi, hpr, hlast⟩ :=
    P.exists_indivisiblePositiveRoots_enumeration_last ν ha
  have hnr' (j : Fin m) : aneg j ∈ RelativeRoot.indivisiblePositiveRoots P.i (-ν) :=
    hnr ▸ Set.mem_range_self j
  have hpr' (j : Fin (n + 1)) : apos j ∈ RelativeRoot.indivisiblePositiveRoots P.i ν :=
    hpr ▸ Set.mem_range_self j
  have hblock (c : characterLattice P.S) (hc : c ∈ relativeRoots P.i)
      {v : rationalPoints G} (hv : v ∈ P.apartment.chamberRootBlock x false c) :
      v ∈ P.apartment.filtration x c 0 := by
    rw [P.apartment.chamberRootBlock_eq_rootGroup x false hc] at hv
    exact hv
  have hrange := (hdec.2.2.2.2.2.2 false m (n + 1) aneg apos hni hnr hpi hpr).2.2.2.2.2
  have hg' : g ∈ Set.range (P.orderedIwahoriChamberProduct x false aneg apos) := by
    rw [hrange]
    exact hg
  obtain ⟨p, hp⟩ := hg'
  have hnmem : P.apartment.orderedChamberBlockProduct x false aneg p.1 ∈ K := by
    apply K.list_prod_mem
    intro v hv
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hv
    apply hother _ (hnr' j).1
    · intro hja
      have hpos := ha.2
      have hneg : latticePairing P.S (aneg j) ν < 0 := by
        simpa using (hnr' j).2
      rw [hja] at hneg
      omega
    · exact hblock _ (hnr' j).1.1 (p.1 j).property
  have hpmem : (List.ofFn fun j : Fin n => (p.2.2 j.castSucc : rationalPoints G)).prod ∈ K := by
    apply K.list_prod_mem
    intro v hv
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hv
    apply hother _ (hpr' j.castSucc).1
    · intro hja
      have heq := hpi (hja.trans hlast.symm)
      exact (Fin.castSucc_ne_last j) heq
    · exact hblock _ (hpr' j.castSucc).1.1 (p.2.2 j.castSucc).property
  have hfinal : (p.2.2 (Fin.last n) : rationalPoints G) ∈
      P.apartment.filtration x a 0 := by
    simpa only [hlast] using hblock _ (hpr' (Fin.last n)).1.1
      (p.2.2 (Fin.last n)).property
  obtain ⟨k, hk, u, hu, hku⟩ := hsplit _ hfinal
  refine ⟨P.apartment.orderedChamberBlockProduct x false aneg p.1 *
    rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
      (List.ofFn fun j : Fin n => (p.2.2 j.castSucc : rationalPoints G)).prod * k,
    K.mul_mem (K.mul_mem (K.mul_mem hnmem (hZ (Subgroup.mem_map_of_mem _ p.2.1.property)))
      hpmem) hk, u, hu, ?_⟩
  rw [← hp]
  unfold orderedIwahoriChamberProduct KPApartmentData.orderedChamberBlockProduct
  rw [List.ofFn_succ', List.prod_concat, hku]
  simp only [mul_assoc]

end Langlands.Geometry.Building.ParahoricBuildingData
