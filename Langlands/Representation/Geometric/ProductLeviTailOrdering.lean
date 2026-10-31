import Langlands.Representation.Geometric.ProductLeviSupportCut
import Langlands.Representation.Geometric.OrbitRepresentatives

noncomputable section
namespace Langlands.Geometric
open GeneralLinear
universe uG uF

namespace OrderedDoubleCosets
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {P Q : Subgroup G} {m : ℕ}

omit [IsTopologicalGroup G] in
/-- Representative replacement preserves each initial union as an actual set. -/
theorem initialOrbits_replaceRepresentatives (s : OrderedDoubleCosets P Q m)
    (r : Fin m → G)
    (h : ∀ i, DoubleCoset.mk P Q (r i)⁻¹ =
      DoubleCoset.mk P Q (s.representative i)⁻¹) (k : Fin (m + 1)) :
    (s.replaceRepresentatives r h).initialOrbits k = s.initialOrbits k := by
  ext x
  change (∃ i, i.val < k.val ∧ x ∈ cosetOrbit P Q (r i)) ↔
    ∃ i, i.val < k.val ∧ x ∈ cosetOrbit P Q (s.representative i)
  simp only [(fun i => (cosetOrbit_eq_iff_doubleCoset_eq P Q _ _).mpr (h i))]

omit [IsTopologicalGroup G] in
/-- Disjointness identifies the index of an orbit inside any initial union. -/
theorem mem_initialOrbits_iff (s : OrderedDoubleCosets P Q m) (i : Fin m)
    (k : Fin (m + 1)) {x : Induction.LeftQuotient P}
    (hx : x ∈ cosetOrbit P Q (s.representative i)) :
    x ∈ s.initialOrbits k ↔ i.val < k.val := by
  constructor
  · rintro ⟨j, hj, hxj⟩
    have hji : j = i := by
      by_contra hne
      exact Set.disjoint_left.mp (s.disjoint hne) hxj hx
    simpa only [hji] using hj
  · intro hi
    exact ⟨i, hi, hx⟩
end OrderedDoubleCosets

/-- Minimal permutation representative replacement keeps every support cut. -/
theorem minimalPermutationOrdering_initialOrbits {K : Type uF} [CommRing K]
    [TopologicalSpace K] [IsTopologicalRing K] {n m : ℕ} (D C : BlockShape n)
    (s : OrderedDoubleCosets (D.parabolic K) (C.parabolic K) m)
    (h : Function.Bijective (parabolicDoubleCoset K D C)) (k : Fin (m + 1)) :
    (minimalPermutationOrdering D C s h).2.val.initialOrbits k = s.initialOrbits k := by
  apply OrderedDoubleCosets.initialOrbits_replaceRepresentatives
  intro i
  exact (Equiv.ofBijective _ h).apply_symm_apply (s.doubleCosetEquiv i)

section Padic
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (Q S : BlockRefinement B)

/-- In a minimal ordering with the coarse-complement cut, the closed tail
consists precisely of the permutations preserving the coarse blocks. -/
theorem blockWeyl_iff_tailIndex {a b : ℕ} :
    letI := T.topology
    ∀ (e : Fin (a + b) ≃ MinimalRepresentatives (B.flatten Q) (B.flatten S))
      (s : OrderedDoubleCosets ((B.flatten Q).parabolic F.Carrier)
        ((B.flatten S).parabolic F.Carrier) (a + b)),
      (∀ i, s.representative i = permutation n F.Carrier (e i).val) →
      s.initialOrbits ⟨a, by omega⟩ = (coarseParabolicLocus (F := F) B Q)ᶜ →
      ∀ i, (e i).val ∈ blockWeyl B ↔ a ≤ i.val := by
  let := T.topology
  intro e s hrep hcut i
  let x := Induction.quotientMap ((B.flatten Q).parabolic F.Carrier)
    (s.representative i)⁻¹
  have hx : x ∈ cosetOrbit ((B.flatten Q).parabolic F.Carrier)
      ((B.flatten S).parabolic F.Carrier) (s.representative i) := by
    exact ⟨1, by simp [x]⟩
  have hcoarse : x ∈ coarseParabolicLocus (F := F) B Q ↔
      (e i).val ∈ blockWeyl B := by
    change x ∈ subgroupLocus _ _ ↔ _
    rw [cosetOrbit_mem_subgroupLocus_iff _ _ _
      (flattenedParabolic_le F.Carrier B Q) (flattenedParabolic_le F.Carrier B S)
      (s.representative i) x hx, hrep i, permutation_mem_parabolic_iff]
  have hi := s.mem_initialOrbits_iff i ⟨a, by omega⟩ hx
  rw [hcut] at hi
  have hneg : ¬ (e i).val ∈ blockWeyl B ↔ i.val < a := by
    simpa only [Set.mem_compl_iff, hcoarse] using hi
  simpa only [not_not, not_lt] using not_congr hneg

/-- Increasing tail indices enumerate the block-preserving minimal representatives. -/
def blockTailEquiv {a b : ℕ}
    (e : Fin (a + b) ≃ MinimalRepresentatives (B.flatten Q) (B.flatten S))
    (he : ∀ i, (e i).val ∈ blockWeyl B ↔ a ≤ i.val) :
    Fin b ≃ BlockMinimalRepresentatives B Q S :=
  Equiv.ofBijective
    (fun i => ⟨e ⟨a + i.val, by omega⟩, (he _).mpr (by dsimp; omega)⟩) (by
      constructor
      · intro i j hij
        have h := e.injective (congrArg Subtype.val hij)
        apply Fin.ext
        have := congrArg Fin.val h
        dsimp at this
        omega
      · intro w
        let i := e.symm w.val
        have hi : a ≤ i.val := (he i).mp (by
          simpa only [i, Equiv.apply_symm_apply] using w.property)
        refine ⟨⟨i.val - a, by omega⟩, ?_⟩
        apply Subtype.ext
        change e ⟨a + (i.val - a), _⟩ = w.val
        have hind : (⟨a + (i.val - a), by omega⟩ : Fin (a + b)) = i := by
          apply Fin.ext
          dsimp
          omega
        rw [hind]
        exact e.apply_symm_apply w.val)

@[simp]
theorem blockTailEquiv_val {a b : ℕ}
    (e : Fin (a + b) ≃ MinimalRepresentatives (B.flatten Q) (B.flatten S))
    (he : ∀ i, (e i).val ∈ blockWeyl B ↔ a ≤ i.val) (i : Fin b) :
    (blockTailEquiv B Q S e he i).val = e ⟨a + i.val, by omega⟩ := rfl
end Padic
end Langlands.Geometric
