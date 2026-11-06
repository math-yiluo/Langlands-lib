import Langlands.Geometry.Building.ChamberPositiveCollection
import Langlands.Geometry.Building.OrderedRootProductFieldDescent

/-! # Collection at arbitrary real depths on closed positive root sets -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  {φ : RootFunctionFamily S G}

/-- Explicit positivity, closure and depth bounds used in collection.
The depths may be arbitrary real numbers. The condition includes equal
input roots and retains all actual roots, including doubled roots. -/
structure IsClosedPositiveRootDepth (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (Ψ : Set (characterLattice S)) (f : characterLattice S → ℝ) : Prop where
  positive : Ψ ⊆ positiveRelativeRoots i ν
  combination : ∀ {a b : characterLattice S}, a ∈ Ψ → b ∈ Ψ →
    ∀ {p q : ℕ}, 0 < p → 0 < q → p • a + q • b ∈ relativeRoots i →
      p • a + q • b ∈ Ψ ∧ f (p • a + q • b) ≤ p * f a + q * f b

namespace IsRootDatumValuation

/-- V3 written as an inclusion between the actual filtration subgroups,
without supplying any apartment data. -/
theorem filtrationSubgroup_commutator_le (hφ : IsRootDatumValuation i φ)
    {a b : characterLattice S} (ha : a ∈ relativeRoots i) (hb : b ∈ relativeRoots i)
    (hnon : ∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] b : Vstar S) ≠
      -(t • (1 : ℝ) ⊗ₜ[ℤ] a)) (r s : ℝ) :
    ⁅hφ.filtrationSubgroup a r, hφ.filtrationSubgroup b s⁆ ≤
      ⨆ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • b ∈ relativeRoots i),
        hφ.filtrationSubgroup (p • a + q • b) (p * r + q * s) := by
  have h := hφ.commutator a ha b hb hnon r s
  change ⁅Subgroup.closure (hφ.filtrationSubgroup a r : Set (rationalPoints G)),
    Subgroup.closure (hφ.filtrationSubgroup b s : Set (rationalPoints G))⁆ ≤
      Subgroup.closure (⋃ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • b ∈ relativeRoots i),
        (hφ.filtrationSubgroup (p • a + q • b) (p * r + q * s) :
          Set (rationalPoints G))) at h
  simpa only [Subgroup.closure_iUnion, Subgroup.closure_eq] using h

end IsRootDatumValuation

variable (hφ : IsRootDatumValuation i φ)
  {ν : cocharacterLattice S} {Ψ : Set (characterLattice S)}
  {f : characterLattice S → ℝ} (hdata : IsClosedPositiveRootDepth i ν Ψ f)

include hφ hdata

/-- V3 and the explicit depth bound force every commutator to have strictly
greater positive-root height than both inputs. -/
theorem positiveDepth_commutator_height
    {a b : characterLattice S} (ha : a ∈ Ψ) (hb : b ∈ Ψ) :
    ⁅hφ.filtrationSubgroup a (f a), hφ.filtrationSubgroup b (f b)⁆ ≤
      ⨆ c : Ψ,
        ⨆ (_ : max (latticePairing S a ν).toNat (latticePairing S b ν).toNat <
          (latticePairing S c ν).toNat), hφ.filtrationSubgroup c (f c) := by
  have hapos := hdata.positive ha
  have hbpos := hdata.positive hb
  refine (hφ.filtrationSubgroup_commutator_le hapos.1 hbpos.1
    (KPApartmentData.positiveRoots_nonopposite ν hapos hbpos) (f a) (f b)).trans ?_
  refine iSup_le fun p => iSup_le fun q => iSup_le fun hp =>
    iSup_le fun hq => iSup_le fun hc => ?_
  obtain ⟨hcΨ, hdepth⟩ := hdata.combination ha hb hp hq hc
  have hheight :=
    (KPApartmentData.positiveRootCombination_height ν hapos hbpos hp hq hc).2
  exact le_iSup_of_le (⟨p • a + q • b, hcΨ⟩ : Ψ)
    (le_iSup_of_le hheight (hφ.filtrationSubgroup_antitone _ hdepth))

/-- Every finite enumeration of a closed positive root set admits collection
at its supplied real depths, in the supplied order. Repetitions are allowed. -/
theorem orderedRootFiltrationProduct_eq_iSup_of_closedPositive
    {n : ℕ} (a : Fin n → characterLattice S) (hrange : Set.range a = Ψ) :
    orderedRootFiltrationProduct i φ a (fun j => f (a j)) =
      ((⨆ c : Ψ, hφ.filtrationSubgroup c (f c) : Subgroup (rationalPoints G)) :
        Set (rationalPoints G)) := by
  have ha (j : Fin n) : a j ∈ Ψ := hrange ▸ Set.mem_range_self j
  have hsup : (⨆ j, hφ.filtrationSubgroup (a j) (f (a j))) =
      ⨆ c : Ψ, hφ.filtrationSubgroup c (f c) := by
    apply le_antisymm
    · exact iSup_le fun j => le_iSup_of_le (⟨a j, ha j⟩ : Ψ) le_rfl
    · refine iSup_le fun c => ?_
      obtain ⟨j, hj⟩ := (show (c : characterLattice S) ∈ Set.range a by
        rw [hrange]; exact c.2)
      exact le_iSup_of_le j (by rw [hj])
  rw [← hsup]
  change Set.range (RelativeRoot.CentralExtension.orderedProduct
    (fun j => (hφ.filtrationSubgroup (a j) (f (a j))).subtype)) = _
  apply Langlands.GroupTheory.HeightCollection.range_orderedProduct_eq_iSup
    (w := fun j => (latticePairing S (a j) ν).toNat)
  intro j k
  refine (positiveDepth_commutator_height hφ hdata (ha j) (ha k)).trans ?_
  refine iSup_le fun c => iSup_le fun hc => ?_
  obtain ⟨l, hl⟩ := (show (c : characterLattice S) ∈ Set.range a by
    rw [hrange]; exact c.2)
  exact le_iSup_of_le l (le_iSup_of_le (hl.symm ▸ hc) (by rw [hl]))

/-- The actual ordered product at the supplied depths, with subgroup
structure derived from V3 and increasing positive-root heights. -/
def positiveDepthProductSubgroup {n : ℕ} (a : Fin n → characterLattice S)
    (hrange : Set.range a = Ψ) : Subgroup (rationalPoints G) :=
  (⨆ c : Ψ, hφ.filtrationSubgroup c (f c)).copy
    (orderedRootFiltrationProduct i φ a (fun j => f (a j)))
    (orderedRootFiltrationProduct_eq_iSup_of_closedPositive hφ hdata a hrange)

@[simp]
theorem mem_positiveDepthProductSubgroup {n : ℕ} (a : Fin n → characterLattice S)
    (hrange : Set.range a = Ψ) (g : rationalPoints G) :
    g ∈ positiveDepthProductSubgroup hφ hdata a hrange ↔
      ∃ x : ∀ j, rootFiltration i φ (a j) (f (a j)),
        (List.ofFn fun j => (x j : rationalPoints G)).prod = g :=
  Iff.rfl

theorem positiveDepthProductSubgroup_eq_iSup {n : ℕ}
    (a : Fin n → characterLattice S) (hrange : Set.range a = Ψ) :
    positiveDepthProductSubgroup hφ hdata a hrange =
      ⨆ c : Ψ, hφ.filtrationSubgroup c (f c) :=
  Subgroup.copy_eq _ _ _

/-- The generated subgroup is the closure of the union of the original
actual filtration sets, with every real bound retained. -/
theorem positiveDepthProductSubgroup_eq_closure {n : ℕ}
    (a : Fin n → characterLattice S) (hrange : Set.range a = Ψ) :
    positiveDepthProductSubgroup hφ hdata a hrange =
      Subgroup.closure (⋃ c : Ψ, rootFiltration i φ c (f c)) := by
  rw [positiveDepthProductSubgroup_eq_iSup, Subgroup.closure_iUnion]
  simp only [← hφ.coe_filtrationSubgroup, Subgroup.closure_eq]

/-- The actual ordered-product set is independent of its complete finite
enumeration, including its length and any repetitions. -/
theorem orderedRootFiltrationProduct_order_independent_of_closedPositive
    {n m : ℕ} (a : Fin n → characterLattice S) (b : Fin m → characterLattice S)
    (ha : Set.range a = Ψ) (hb : Set.range b = Ψ) :
    orderedRootFiltrationProduct i φ a (fun j => f (a j)) =
      orderedRootFiltrationProduct i φ b (fun j => f (b j)) := by
  rw [orderedRootFiltrationProduct_eq_iSup_of_closedPositive hφ hdata a ha,
    orderedRootFiltrationProduct_eq_iSup_of_closedPositive hφ hdata b hb]

end Langlands.Geometry.Building
