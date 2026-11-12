import Langlands.Geometry.Building.MoyPrasadDoubleRefinement
import Langlands.Geometry.Building.KPParahoricProduct
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! # Local positive-depth exchange of the original root blocks -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- Four actual constituent exchanges combine into exchange of two
two-factor blocks when the middle subgroup normalizes both blocks. -/
theorem twoFactorBlockExchange {M : Type*} [Group M]
    (A B C D P Q Z : Subgroup M)
    (hP : (P : Set M) = (A : Set M) * B)
    (hQ : (Q : Set M) = (C : Set M) * D)
    (hA : A ≤ P) (hB : B ≤ P) (hC : C ≤ Q)
    (hZP : Z ≤ Subgroup.normalizer (P : Set M))
    (hZQ : Z ≤ Subgroup.normalizer (Q : Set M))
    (hAC : (A : Set M) * C ⊆ (C : Set M) * Z * A)
    (hBC : (B : Set M) * C ⊆ (C : Set M) * Z * P)
    (hAD : (A : Set M) * D ⊆ (Q : Set M) * Z * A)
    (hBD : (B : Set M) * D ⊆ (D : Set M) * Z * B) :
    (P : Set M) * Q ⊆ (Q : Set M) * Z * P := by
  have hPZ : (P : Set M) * Z = (Z : Set M) * P :=
    (Subgroup.set_mul_normalizer_comm (Z : Set M) P hZP).symm
  have hQZ : (Q : Set M) * Z = (Z : Set M) * Q :=
    (Subgroup.set_mul_normalizer_comm (Z : Set M) Q hZQ).symm
  have absorbP (R : Set M) :
      R * Z * P * Z * P = R * Z * P := by
    calc
      R * Z * P * Z * P = R * Z * ((P : Set M) * Z) * P := by
        simp only [mul_assoc]
      _ = R * Z * ((Z : Set M) * P) * P := by rw [hPZ]
      _ = R * ((Z : Set M) * Z) * ((P : Set M) * P) := by
        simp only [mul_assoc]
      _ = R * Z * P := by rw [coe_mul_coe, coe_mul_coe]
  have hPD : (P : Set M) * D ⊆ (Q : Set M) * Z * P := by
    calc
      (P : Set M) * D = (A : Set M) * B * D := by rw [hP]
      _ = (A : Set M) * ((B : Set M) * D) := by rw [mul_assoc]
      _ ⊆ (A : Set M) * ((D : Set M) * Z * B) := Set.mul_subset_mul_left hBD
      _ = (A : Set M) * D * Z * B := by simp only [mul_assoc]
      _ ⊆ (Q : Set M) * Z * A * Z * B :=
        Set.mul_subset_mul_right (Set.mul_subset_mul_right hAD)
      _ ⊆ (Q : Set M) * Z * P * Z * P :=
        Set.mul_subset_mul (Set.mul_subset_mul
          (Set.mul_subset_mul subset_rfl hA) subset_rfl) hB
      _ = (Q : Set M) * Z * P := absorbP _
  calc
    (P : Set M) * Q = ((A : Set M) * B) * ((C : Set M) * D) := by rw [hP, hQ]
    _ = (A : Set M) * ((B : Set M) * C) * D := by simp only [mul_assoc]
    _ ⊆ (A : Set M) * ((C : Set M) * Z * P) * D :=
      Set.mul_subset_mul_right (Set.mul_subset_mul_left hBC)
    _ = (A : Set M) * C * Z * P * D := by simp only [mul_assoc]
    _ ⊆ (C : Set M) * Z * A * Z * P * D :=
      Set.mul_subset_mul_right
        (Set.mul_subset_mul_right (Set.mul_subset_mul_right hAC))
    _ ⊆ (C : Set M) * Z * P * Z * P * D :=
      Set.mul_subset_mul_right
        (Set.mul_subset_mul_right (Set.mul_subset_mul_right
          (Set.mul_subset_mul subset_rfl hA)))
    _ = (C : Set M) * Z * P * D := by rw [absorbP]
    _ = (C : Set M) * Z * ((P : Set M) * D) := by simp only [mul_assoc]
    _ ⊆ (C : Set M) * Z * ((Q : Set M) * Z * P) := Set.mul_subset_mul_left hPD
    _ ⊆ (Q : Set M) * Z * ((Q : Set M) * Z * P) :=
      Set.mul_subset_mul (Set.mul_subset_mul hC subset_rfl) subset_rfl
    _ = (Q : Set M) * ((Z : Set M) * Q) * Z * P := by simp only [mul_assoc]
    _ = (Q : Set M) * ((Q : Set M) * Z) * Z * P := by rw [← hQZ]
    _ = ((Q : Set M) * Q) * ((Z : Set M) * Z) * P := by simp only [mul_assoc]
    _ = (Q : Set M) * Z * P := by rw [coe_mul_coe, coe_mul_coe]

end Langlands.Geometry.Building

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- An element of the retained double-depth factor commutes with an
element of the ordinary root-depth factor, at arbitrary real depths. -/
theorem doubleFiltration_commute_filtration (hP : P.SatisfiesApartmentAxioms)
    (x : P.Apartment) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (r s : ℝ) {g h : rationalPoints G}
    (hg : g ∈ P.apartment.doubleFiltration x a r)
    (hh : h ∈ P.filtration x a s) : Commute g h := by
  by_cases h2a : 2 • a ∈ relativeRoots P.i
  · rw [P.apartment.doubleFiltration_of_mem x a r h2a] at hg
    exact P.doubleRootGroupPoints_commute hP ha hg.1 hh.1
  · rw [P.apartment.doubleFiltration_of_not_mem x a r h2a] at hg
    rw [Subgroup.mem_bot.mp hg]
    exact Commute.one_left _

/-- The original constant-depth two-factor block is itself a subgroup.
Its carrier remains definitionally the original set product. -/
def filtrationBlockSubgroup (hP : P.SatisfiesApartmentAxioms)
    (x : P.Apartment) (r : ℝ) {a : characterLattice P.S}
    (ha : a ∈ relativeRoots P.i) : Subgroup (rationalPoints G) where
  carrier := P.apartment.filtrationBlock x (fun _ => r) a
  one_mem' := ⟨1, (P.filtration x a r).one_mem,
    1, (P.apartment.doubleFiltration x a r).one_mem, one_mul _⟩
  mul_mem' := by
    rintro g h ⟨v, hv, w, hw, rfl⟩ ⟨v', hv', w', hw', rfl⟩
    refine ⟨v * v', (P.filtration x a r).mul_mem hv hv',
      w * w', (P.apartment.doubleFiltration x a r).mul_mem hw hw', ?_⟩
    have hcomm := P.doubleFiltration_commute_filtration hP x ha r r hw hv'
    calc
      (v * v') * (w * w') = v * (v' * w) * w' := by group
      _ = v * (w * v') * w' := by rw [hcomm.eq]
      _ = (v * w) * (v' * w') := by group
  inv_mem' := by
    rintro g ⟨v, hv, w, hw, rfl⟩
    refine ⟨v⁻¹, (P.filtration x a r).inv_mem hv,
      w⁻¹, (P.apartment.doubleFiltration x a r).inv_mem hw, ?_⟩
    have hcomm := P.doubleFiltration_commute_filtration hP x ha r r hw hv
    calc
      v⁻¹ * w⁻¹ = (w * v)⁻¹ := by group
      _ = (v * w)⁻¹ := congrArg Inv.inv hcomm.eq

@[simp]
theorem coe_filtrationBlockSubgroup (hP : P.SatisfiesApartmentAxioms)
    (x : P.Apartment) (r : ℝ) {a : characterLattice P.S}
    (ha : a ∈ relativeRoots P.i) :
    (P.filtrationBlockSubgroup hP x r ha : Set (rationalPoints G)) =
      P.apartment.filtrationBlock x (fun _ => r) a := rfl

theorem filtration_le_filtrationBlockSubgroup (hP : P.SatisfiesApartmentAxioms)
    (x : P.Apartment) (r : ℝ) {a : characterLattice P.S}
    (ha : a ∈ relativeRoots P.i) :
    P.filtration x a r ≤ P.filtrationBlockSubgroup hP x r ha :=
  P.apartment.filtration_subset_filtrationBlock x (fun _ => r) a

theorem doubleFiltration_le_filtrationBlockSubgroup (hP : P.SatisfiesApartmentAxioms)
    (x : P.Apartment) (r : ℝ) {a : characterLattice P.S}
    (ha : a ∈ relativeRoots P.i) :
    P.apartment.doubleFiltration x a r ≤ P.filtrationBlockSubgroup hP x r ha := by
  intro g hg
  exact ⟨1, (P.filtration x a r).one_mem, g, hg, one_mul _⟩

namespace CentralizerFiltration

variable {P}
variable (Zf : P.CentralizerFiltration)

/-- The actual centralizer-depth image normalizes every root-depth subgroup
because it is contained in the original norm-one centralizer. -/
theorem image_le_normalizer_filtration (x : P.Apartment) (r : NNReal)
    (a : characterLattice P.S) (s : ℝ) :
    Zf.image r ≤ Subgroup.normalizer (P.filtration x a s : Set (rationalPoints G)) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro z hz g hg
  obtain ⟨z, hz, rfl⟩ := hz
  have hz0 : z ∈ P.centralizerZero := by
    rw [← Zf.filtration_zero]
    exact Zf.antitone (zero_le : (0 : NNReal) ≤ r) hz
  have hfix := P.isOmegaCompatible.smul_eq_self
    (P.zeroDatum.centralizerZero_le_rationalCommonNormKernel hz0) x
  have hweyl : weylAction P.i (P.centralizer.toNormalizer z) = 1 :=
    weylAction_centralizerToNormalizer P.centralizer.isRepresentedBy z
  have h := P.apartment.conj_mem_filtration (P.centralizer.toNormalizer z) hg
  rw [hfix, hweyl] at h
  exact h

/-- The same centralizer-depth image normalizes the original two-factor
block subgroup, including its retained doubled-root factor. -/
theorem image_le_normalizer_filtrationBlockSubgroup (hP : P.SatisfiesApartmentAxioms)
    (x : P.Apartment) (r : NNReal) (s : ℝ)
    {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i) :
    Zf.image r ≤ Subgroup.normalizer
      (P.filtrationBlockSubgroup hP x s ha : Set (rationalPoints G)) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro z hz g hg
  obtain ⟨v, hv, w, hw, rfl⟩ := hg
  have hv' := Subgroup.le_normalizer_iff.mp (Zf.image_le_normalizer_filtration x r a s)
    z hz v hv
  have hw' : z * w * z⁻¹ ∈ P.apartment.doubleFiltration x a s := by
    by_cases h2a : 2 • a ∈ relativeRoots P.i
    · rw [P.apartment.doubleFiltration_of_mem x a s h2a] at hw ⊢
      exact Subgroup.le_normalizer_iff.mp
        (Zf.image_le_normalizer_filtration x r (2 • a) s) z hz w hw
    · rw [P.apartment.doubleFiltration_of_not_mem x a s h2a] at hw ⊢
      rw [Subgroup.mem_bot.mp hw]
      simp
  exact ⟨z * v * z⁻¹, hv', z * w * z⁻¹, hw', by group⟩

/-- Ordinary opposite-root exchange at one positive depth, with the
central factor lowered from depth `2r` to depth `r`. -/
theorem filtration_mul_opposite_subset_image
    (hZ : Zf.IsCommutatorFriendly) (x : P.Apartment)
    {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (r : NNReal) (hr : 0 < r) :
    (P.filtration x a r : Set (rationalPoints G)) * P.filtration x (-a) r ⊆
      (P.filtration x (-a) r : Set (rationalPoints G)) *
        (Zf.image r : Set (rationalPoints G)) * P.filtration x a r := by
  refine (Zf.filtration_mul_opposite_filtration_subset_depth hZ x ha r r
    (by positivity)).trans ?_
  exact Set.mul_subset_mul
    (Set.mul_subset_mul subset_rfl (Zf.image_antitone (by simp))) subset_rfl

/-- The doubled positive factor exchanges with the negative ordinary
factor while retaining the original entire positive block. -/
theorem doubleFiltration_mul_opposite_subset_block
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.IsCommutatorFriendly)
    (x : P.Apartment) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (r : NNReal) (hr : 0 < r) :
    (P.apartment.doubleFiltration x a r : Set (rationalPoints G)) *
        P.filtration x (-a) r ⊆
      (P.filtration x (-a) r : Set (rationalPoints G)) *
        (Zf.image r : Set (rationalPoints G)) *
          P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a := by
  rintro _ ⟨u, hu, v, hv, rfl⟩
  change u * v ∈ _
  by_cases h2a : 2 • a ∈ relativeRoots P.i
  · rw [P.apartment.doubleFiltration_of_mem x a r h2a] at hu
    let p := doublePositiveMoyPrasadCoordinates P hP Zf hZ x ha h2a r r
      (by positivity) ⟨u, hu⟩ ⟨v, hv⟩
    have hz : rationalPoints.map P.centralizer.j
        (p.val.2.1 : rationalPoints P.centralizer.Z) ∈ Zf.image r :=
      Subgroup.mem_map.mpr ⟨p.val.2.1, Zf.antitone (by simp)
        p.val.2.1.property, rfl⟩
    rw [← p.property]
    exact Set.mul_mem_mul (Set.mul_mem_mul p.val.1.property hz) p.val.2.2.property
  · rw [P.apartment.doubleFiltration_of_not_mem x a r h2a] at hu
    rw [Subgroup.mem_bot.mp hu, one_mul]
    have h1 : (1 : rationalPoints G) ∈
        P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a :=
      (P.filtrationBlockSubgroup hP x r ha).one_mem
    simpa only [mul_one] using
      Set.mul_mem_mul (Set.mul_mem_mul hv (Zf.image r).one_mem) h1

/-- Inversion of the mixed doubled-positive exchange gives the other
mixed exchange, retaining the original negative block. -/
theorem filtration_mul_oppositeDouble_subset_block
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.IsCommutatorFriendly)
    (x : P.Apartment) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (r : NNReal) (hr : 0 < r) :
    (P.filtration x a r : Set (rationalPoints G)) *
        P.apartment.doubleFiltration x (-a) r ⊆
      P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-a) *
        (Zf.image r : Set (rationalPoints G)) * P.filtration x a r := by
  have hneg : -a ∈ relativeRoots P.i := by
    let : Smooth G.X.hom := P.isConnectedReductive.smooth
    exact KPApartmentData.neg_mem_relativeRoots_of_rankOne
      P.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)
      x ha
  rintro _ ⟨u, hu, v, hv, rfl⟩
  have hinv : u⁻¹ ∈ P.filtration x (-(-a)) r := by
    rw [neg_neg]
    exact (P.filtration x a r).inv_mem hu
  have hex := Zf.doubleFiltration_mul_opposite_subset_block hP hZ x hneg r hr
    (Set.mul_mem_mul ((P.apartment.doubleFiltration x (-a) r).inv_mem hv) hinv)
  obtain ⟨_, ⟨w, hw, z, hz, rfl⟩, b, hb, heq⟩ := hex
  rw [neg_neg] at hw
  have heq' : b⁻¹ * z⁻¹ * w⁻¹ = u * v := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv heq
  change u * v ∈ _
  rw [← heq']
  exact Set.mul_mem_mul (Set.mul_mem_mul
    ((P.filtrationBlockSubgroup hP x r hneg).inv_mem hb)
    ((Zf.image r).inv_mem hz)) ((P.filtration x a r).inv_mem hw)

/-- The two doubled factors exchange by ordinary rank-one exchange in
the doubled-root direction; absent factors remain the identity subgroup. -/
theorem doubleFiltration_mul_oppositeDouble_subset_image
    (hZ : Zf.IsCommutatorFriendly) (x : P.Apartment)
    {a : characterLattice P.S} (r : NNReal) (hr : 0 < r) :
    (P.apartment.doubleFiltration x a r : Set (rationalPoints G)) *
        P.apartment.doubleFiltration x (-a) r ⊆
      (P.apartment.doubleFiltration x (-a) r : Set (rationalPoints G)) *
        (Zf.image r : Set (rationalPoints G)) * P.apartment.doubleFiltration x a r := by
  by_cases h2a : 2 • a ∈ relativeRoots P.i
  · by_cases hneg2a : 2 • -a ∈ relativeRoots P.i
    · rw [P.apartment.doubleFiltration_of_mem x a r h2a,
        P.apartment.doubleFiltration_of_mem x (-a) r hneg2a]
      simpa only [smul_neg] using Zf.filtration_mul_opposite_subset_image hZ x h2a r hr
    · rw [P.apartment.doubleFiltration_of_not_mem x (-a) r hneg2a]
      rintro _ ⟨u, hu, v, hv, rfl⟩
      change u * v ∈ _
      rw [Subgroup.mem_bot.mp hv, mul_one]
      simpa only [one_mul] using Set.mul_mem_mul
        (Set.mul_mem_mul (Subgroup.one_mem (⊥ : Subgroup (rationalPoints G)))
          (Zf.image r).one_mem) hu
  · rw [P.apartment.doubleFiltration_of_not_mem x a r h2a]
    rintro _ ⟨u, hu, v, hv, rfl⟩
    change u * v ∈ _
    rw [Subgroup.mem_bot.mp hu, one_mul]
    simpa only [mul_one] using Set.mul_mem_mul
      (Set.mul_mem_mul hv (Zf.image r).one_mem)
      (Subgroup.one_mem (⊥ : Subgroup (rationalPoints G)))

/-- Full local exchange of the unchanged indivisible-root blocks at
positive depth, including both factors in a nonreduced root system. -/
theorem filtrationBlock_mul_opposite_subset
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.IsCommutatorFriendly)
    (x : P.Apartment) {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i)
    (r : NNReal) (hr : 0 < r) :
    P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a *
        P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-a) ⊆
      P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (-a) *
        (Zf.image r : Set (rationalPoints G)) *
          P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a := by
  have hneg : -a ∈ relativeRoots P.i := by
    let : Smooth G.X.hom := P.isConnectedReductive.smooth
    exact KPApartmentData.neg_mem_relativeRoots_of_rankOne
      P.isMaximalSplitTorus.isSplitSubtorus.1
      (rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus)
      x ha
  exact twoFactorBlockExchange
    (P.filtration x a r) (P.apartment.doubleFiltration x a r)
    (P.filtration x (-a) r) (P.apartment.doubleFiltration x (-a) r)
    (P.filtrationBlockSubgroup hP x r ha) (P.filtrationBlockSubgroup hP x r hneg)
    (Zf.image r) rfl rfl
    (P.filtration_le_filtrationBlockSubgroup hP x r ha)
    (P.doubleFiltration_le_filtrationBlockSubgroup hP x r ha)
    (P.filtration_le_filtrationBlockSubgroup hP x r hneg)
    (Zf.image_le_normalizer_filtrationBlockSubgroup hP x r r ha)
    (Zf.image_le_normalizer_filtrationBlockSubgroup hP x r r hneg)
    (Zf.filtration_mul_opposite_subset_image hZ x ha r hr)
    (Zf.doubleFiltration_mul_opposite_subset_block hP hZ x ha r hr)
    (Zf.filtration_mul_oppositeDouble_subset_block hP hZ x ha r hr)
    (Zf.doubleFiltration_mul_oppositeDouble_subset_image hZ x r hr)

end CentralizerFiltration

end Langlands.Geometry.Building.ParahoricBuildingData
