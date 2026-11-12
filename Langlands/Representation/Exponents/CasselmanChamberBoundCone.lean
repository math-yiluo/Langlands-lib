import Langlands.GroupScheme.Rational.ParabolicRootPresentationSimpleRoots
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.Geometry.Building.RealTorusDuality
import Langlands.Representation.Exponents.CasselmanCentralDirections
import Langlands.Representation.Exponents.CasselmanConeNormBounds
import Langlands.Representation.Plancherel.SplitTorusPositiveCharacter

/-! # Positive root cones and strict bounds on the closed restricted-root chamber -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme.ParabolicRootPresentation

open RealTorusSpace

variable {k : Type u} [Field k]
  {A T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

/-- Pairing a real character with the integral cocharacters `1 ⊗ m`. -/
def latticePair (y : Vstar A) : cocharacterLattice A →+ ℝ where
  toFun m := pair A y ((1 : ℝ) ⊗ₜ[ℤ] m)
  map_zero' := by simp
  map_add' m n := by simp [TensorProduct.tmul_add]

omit [IsAffineHom G.X.hom] in
@[simp] theorem latticePair_apply (y : Vstar A) (m : cocharacterLattice A) :
    latticePair y m = pair A y ((1 : ℝ) ⊗ₜ[ℤ] m) := rfl

omit [IsAffineHom G.X.hom] in
theorem latticePair_restrictedRootVector (f : A ⟶ T') (α : characterLattice T')
    (m : cocharacterLattice A) :
    latticePair (restrictedRootVector f α) m = (latticePairing A (f ≫ α) m : ℝ) := by
  rw [latticePair_apply, restrictedRootVector_eq_tmul, pair_tmul_tmul, one_mul, one_mul]

omit [IsAffineHom G.X.hom] in
/-- A real character of a split torus vanishing on every integral cocharacter is zero. -/
theorem eq_zero_of_latticePair_eq_zero (hA : IsSplitTorus A.toGrp) (y : Vstar A)
    (hy : ∀ m : cocharacterLattice A, latticePair y m = 0) : y = 0 := by
  apply (characterDualEquiv hA).injective
  rw [map_zero]
  apply LinearMap.ext
  intro v
  rw [characterDualEquiv_apply, LinearMap.zero_apply]
  induction v using TensorProduct.inductionOn with
  | tmul t m =>
    have h := hy m
    rw [latticePair_apply] at h
    rw [show t ⊗ₜ[ℤ] m = t • ((1 : ℝ) ⊗ₜ[ℤ] m) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, h, smul_zero]
  | add v w hv hw => rw [map_add, hv, hw, add_zero]

section FiniteType

variable [LocallyOfFiniteType G.X.hom]

/-- An ambient cocharacter vanishing on the selected simple roots lifts
integrally through the specified split component. -/
theorem exists_lift_of_selected_pairing_eq_zero
    (hLI : LinearIndependent ℚ (fun α : simpleRelativeRoots r.data.i r.data.ν =>
      toRat (α : characterLattice r.data.T)))
    (ζ : cocharacterLattice r.data.T)
    (hζ : ∀ α ∈ r.data.J, latticePairing r.data.T α ζ = 0) :
    ∃ m : cocharacterLattice A, cocharacterMapInt r.data.f m = ζ := by
  classical
  obtain ⟨d, hd, ξ, hξ⟩ :=
    r.isCompatible.maximalSplit.isSplitSubtorus.1.exists_scaled_pairings
      (fun α : simpleRelativeRoots r.data.i r.data.ν => (α : characterLattice r.data.T)) hLI
      (fun α => if (α : characterLattice r.data.T) ∈ r.data.J then 0 else 1)
  let s := r.finite_simpleRoots.toFinset
  let N : ℤ := ∑ α ∈ s, |latticePairing r.data.T α ζ| + 1
  have hN : 0 < N := by
    have := Finset.sum_nonneg (s := s)
      (fun α _ => abs_nonneg (latticePairing r.data.T α ζ))
    omega
  have hξJ : ∀ α ∈ r.data.J, latticePairing r.data.T α ξ = 0 := by
    intro α hα
    simpa [hα] using hξ ⟨α, r.isCompatible.subset_simpleRoots hα⟩
  have hξpos : ∀ α ∈ simpleRelativeRoots r.data.i r.data.ν, α ∉ r.data.J →
      latticePairing r.data.T α ξ = d := by
    intro α hα hJ
    simpa [hJ] using hξ ⟨α, hα⟩
  have hstd₁ : IsStandardCocharacter r.data.i r.data.ν r.data.J (N • ξ) := by
    refine ⟨r.isCompatible.subset_simpleRoots, fun α hα => ?_, fun α hα hJ => ?_⟩
    · rw [map_zsmul, hξJ α hα, smul_zero]
    · rw [map_zsmul, hξpos α hα hJ, smul_eq_mul]
      exact mul_pos hN hd
  have hstd₂ : IsStandardCocharacter r.data.i r.data.ν r.data.J (ζ + N • ξ) := by
    refine ⟨r.isCompatible.subset_simpleRoots, fun α hα => ?_, fun α hα hJ => ?_⟩
    · rw [map_add, map_zsmul, hξJ α hα, hζ α hα, smul_zero, add_zero]
    · rw [map_add, map_zsmul, hξpos α hα hJ, smul_eq_mul]
      have hmem : α ∈ s := r.finite_simpleRoots.mem_toFinset.mpr hα
      have hle : |latticePairing r.data.T α ζ| ≤ ∑ β ∈ s, |latticePairing r.data.T β ζ| :=
        Finset.single_le_sum (f := fun β => |latticePairing r.data.T β ζ|)
          (fun β _ => abs_nonneg _) hmem
      have habs := neg_abs_le (latticePairing r.data.T α ζ)
      nlinarith
  obtain ⟨m₁, hm₁⟩ := r.exists_standardCocharacter_lift hstd₂
  obtain ⟨m₂, hm₂⟩ := r.exists_standardCocharacter_lift hstd₁
  exact ⟨m₁ - m₂, by rw [map_sub, hm₁, hm₂, add_sub_cancel_right]⟩

open scoped Classical in
/-- A family of integral component cocharacters dual, up to one common positive
factor, to the complementary simple roots. -/
theorem exists_dual_cocharacters
    (hLI : LinearIndependent ℚ (fun α : simpleRelativeRoots r.data.i r.data.ν =>
      toRat (α : characterLattice r.data.T))) :
    ∃ D : ℤ, 0 < D ∧ ∃ ν : characterLattice r.data.T → cocharacterLattice A,
      ∀ α ∈ simpleRelativeRoots r.data.i r.data.ν, α ∉ r.data.J →
        ∀ β ∈ simpleRelativeRoots r.data.i r.data.ν, β ∉ r.data.J →
          latticePairing A (r.data.f ≫ β) (ν α) = if β = α then D else 0 := by
  classical
  have hone : ∀ α : characterLattice r.data.T, ∃ d : ℤ, 0 < d ∧
      ∃ ζ : cocharacterLattice r.data.T,
        ∀ β : simpleRelativeRoots r.data.i r.data.ν,
          latticePairing r.data.T (β : characterLattice r.data.T) ζ =
            d * if (β : characterLattice r.data.T) = α then 1 else 0 := fun α =>
    r.isCompatible.maximalSplit.isSplitSubtorus.1.exists_scaled_pairings
      (fun β : simpleRelativeRoots r.data.i r.data.ν => (β : characterLattice r.data.T)) hLI
      (fun β => if (β : characterLattice r.data.T) = α then 1 else 0)
  choose d hd ζ hζ using hone
  let s := r.finite_simpleRoots.toFinset
  let D : ℤ := ∏ α ∈ s, d α
  have hD : 0 < D := Finset.prod_pos fun α _ => hd α
  have hdvd : ∀ α ∈ s, d α ∣ D := fun α hα => Finset.dvd_prod_of_mem d hα
  have hlift : ∀ α ∈ simpleRelativeRoots r.data.i r.data.ν, α ∉ r.data.J →
      ∃ m : cocharacterLattice A,
        cocharacterMapInt r.data.f m = (D / d α) • ζ α := by
    intro α hα hJ
    apply r.exists_lift_of_selected_pairing_eq_zero hLI
    intro β hβ
    have hne : β ≠ α := fun h => hJ (h ▸ hβ)
    rw [map_zsmul, hζ α ⟨β, r.isCompatible.subset_simpleRoots hβ⟩]
    simp [hne]
  have : Nonempty (cocharacterLattice A) := ⟨0⟩
  choose! m hm using hlift
  refine ⟨D, hD, m, ?_⟩
  intro α hα hJ β hβ hβJ
  rw [RelativeRoot.latticePairing_restrict_cocharacterMapInt,
    hm α hα hJ, map_zsmul, hζ α ⟨β, hβ⟩, smul_eq_mul]
  have hαs : α ∈ s := r.finite_simpleRoots.mem_toFinset.mpr hα
  by_cases hβα : β = α
  · simp only [hβα, ite_true, mul_one]
    exact Int.ediv_mul_cancel (hdvd α hαs)
  · simp [hβα]

/-- Strictly positive pairings with the dual cocharacters of all complementary
simple roots, and vanishing on the integral cocharacters orthogonal to all of
them, place a real character in the strictly positive root cone. -/
theorem mem_positiveCone_of_latticePair
    (hLI : LinearIndependent ℚ (fun α : simpleRelativeRoots r.data.i r.data.ν =>
      toRat (α : characterLattice r.data.T)))
    (hA : IsSplitTorus A.toGrp) (x : Vstar A)
    (h0 : ∀ m : cocharacterLattice A,
      (∀ α ∈ simpleRelativeRoots r.data.i r.data.ν, α ∉ r.data.J →
        latticePairing A (r.data.f ≫ α) m = 0) → latticePair x m = 0)
    (hpos : ∀ m : cocharacterLattice A,
      (∀ α ∈ simpleRelativeRoots r.data.i r.data.ν, α ∉ r.data.J →
        0 ≤ latticePairing A (r.data.f ≫ α) m) →
      (∃ α ∈ simpleRelativeRoots r.data.i r.data.ν, α ∉ r.data.J ∧
        0 < latticePairing A (r.data.f ≫ α) m) → 0 < latticePair x m) :
    x ∈ r.positiveCone := by
  classical
  obtain ⟨D, hD, ν, hν⟩ := r.exists_dual_cocharacters hLI
  have hSfin : (simpleRelativeRoots r.data.i r.data.ν \ r.data.J).Finite :=
    r.finite_simpleRoots.sdiff
  let s := hSfin.toFinset
  have hs : ∀ {α}, α ∈ s ↔ α ∈ simpleRelativeRoots r.data.i r.data.ν ∧ α ∉ r.data.J :=
    fun {α} => by rw [hSfin.mem_toFinset]; rfl
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  let c : characterLattice r.data.T → ℝ := fun α => latticePair x (ν α) / D
  have hc : ∀ α ∈ s, 0 < c α := by
    intro α hα
    obtain ⟨hα₁, hα₂⟩ := hs.mp hα
    apply div_pos _ hDR
    apply hpos (ν α)
    · intro β hβ hβJ
      rw [hν α hα₁ hα₂ β hβ hβJ]
      split_ifs <;> omega
    · exact ⟨α, hα₁, hα₂, by rw [hν α hα₁ hα₂ α hα₁ hα₂]; simpa using hD⟩
  refine (mem_restrictedRootPositiveCone_iff_roots r.data.i r.data.ν r.data.J r.data.f
    r.finite_simpleRoots s (by rw [hSfin.coe_toFinset])).mpr ⟨c, hc, ?_⟩
  let y := x - ∑ α ∈ s, c α • restrictedRootVector r.data.f α
  have hyroot : ∀ m : cocharacterLattice A, latticePair y m =
      latticePair x m - ∑ α ∈ s, c α * (latticePairing A (r.data.f ≫ α) m : ℝ) := by
    intro m
    have h := fun α => latticePair_restrictedRootVector r.data.f α m
    simp only [latticePair_apply] at h ⊢
    simp only [y, map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, h]
  have hydual : ∀ α ∈ s, latticePair y (ν α) = 0 := by
    intro α hα
    obtain ⟨hα₁, hα₂⟩ := hs.mp hα
    rw [hyroot, Finset.sum_congr rfl (fun β hβ => by
      rw [hν α hα₁ hα₂ β (hs.mp hβ).1 (hs.mp hβ).2])]
    simp only [apply_ite (fun n : ℤ => (n : ℝ)), Int.cast_zero, mul_ite, mul_zero,
      Finset.sum_ite_eq', hα, ite_true]
    simp only [c]
    field_simp
    ring
  have hyperp : ∀ m : cocharacterLattice A,
      (∀ β ∈ simpleRelativeRoots r.data.i r.data.ν, β ∉ r.data.J →
        latticePairing A (r.data.f ≫ β) m = 0) → latticePair y m = 0 := by
    intro m hm
    rw [hyroot, h0 m hm, Finset.sum_eq_zero (fun β hβ => by
      rw [hm β (hs.mp hβ).1 (hs.mp hβ).2, Int.cast_zero, mul_zero]), sub_zero]
  have hy : y = 0 := by
    apply eq_zero_of_latticePair_eq_zero hA y
    intro m
    let m' : cocharacterLattice A :=
      D • m - ∑ α ∈ s, latticePairing A (r.data.f ≫ α) m • ν α
    have hm' : ∀ β ∈ simpleRelativeRoots r.data.i r.data.ν, β ∉ r.data.J →
        latticePairing A (r.data.f ≫ β) m' = 0 := by
      intro β hβ hβJ
      simp only [m', map_sub, map_zsmul, map_sum, smul_eq_mul]
      rw [Finset.sum_congr rfl (fun α hα => by
        rw [hν α (hs.mp hα).1 (hs.mp hα).2 β hβ hβJ])]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, hs.mpr ⟨hβ, hβJ⟩, ite_true]
      ring
    have hdecomp : D • m = m' + ∑ α ∈ s, latticePairing A (r.data.f ≫ α) m • ν α := by
      simp only [m', sub_add_cancel]
    have h1 : latticePair y (D • m) = 0 := by
      rw [hdecomp, map_add, hyperp m' hm', map_sum, zero_add]
      exact Finset.sum_eq_zero fun α hα => by rw [map_zsmul, hydual α hα, smul_zero]
    rw [map_zsmul, zsmul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left (by exact_mod_cast hD.ne')
  simp only [y, sub_eq_zero] at hy
  exact hy.symm

section Reductive

omit [LocallyOfFiniteType G.X.hom] in
/-- For a compatible presentation of a connected reductive group the simple
relative roots are rationally independent. -/
theorem linearIndependent_simpleRoots (hG : IsConnectedReductive G) :
    LinearIndependent ℚ (fun α : simpleRelativeRoots r.data.i r.data.ν =>
      toRat (α : characterLattice r.data.T)) :=
  Module.Flat.linearIndependent_one_tmul
    (linearIndependent_simpleRelativeRoots_of_standardCocharacter_exists r.data.i r.data.ν
      fun J hJ => (standardCocharacter k G hG r.data.T r.data.i r.isCompatible.maximalSplit
        r.data.ν r.isCompatible.generic J hJ).1)

/-- A component cocharacter orthogonal to every complementary simple root is
central in the ambient group: it pairs to zero with every relative root. -/
theorem isCentral_of_pairing_eq_zero (hG : IsConnectedReductive G)
    (m : cocharacterLattice A)
    (hm : ∀ α ∈ simpleRelativeRoots r.data.i r.data.ν, α ∉ r.data.J →
      latticePairing A (r.data.f ≫ α) m = 0) :
    IsCentral (CommGroupScheme.groupHom m ≫ a ≫ l ≫ p) := by
  have := hG.smooth
  have := hG.connectedSpace
  have hsimple : ∀ α ∈ simpleRelativeRoots r.data.i r.data.ν,
      latticePairing r.data.T α (cocharacterMapInt r.data.f m) = 0 := by
    intro α hα
    rw [← RelativeRoot.latticePairing_restrict_cocharacterMapInt]
    by_cases hJ : α ∈ r.data.J
    · rw [r.selectedRoot_restrict_eq_zero hJ, map_zero, LinearMap.zero_apply]
    · exact hm α hα hJ
  have hpos : ∀ α ∈ positiveRelativeRoots r.data.i r.data.ν,
      latticePairing r.data.T α (cocharacterMapInt r.data.f m) = 0 := by
    intro α hα
    exact positiveRelativeRoots_induction r.data.i r.data.ν
      (P := fun χ => latticePairing r.data.T χ (cocharacterMapInt r.data.f m) = 0)
      hsimple (fun b₁ _ b₂ _ h₁ h₂ => by rw [map_add, LinearMap.add_apply, h₁, h₂, add_zero]) hα
  have hall : ∀ α ∈ relativeRoots r.data.i,
      latticePairing r.data.T α (cocharacterMapInt r.data.f m) = 0 := by
    intro α hα
    rcases lt_or_gt_of_ne (r.isCompatible.generic α hα) with hn | hp'
    · have hneg := relativeRootNegation k G hG r.data.T r.data.i r.isCompatible.maximalSplit α hα
      have h := hpos (-α) ⟨hneg, by rw [map_neg, LinearMap.neg_apply]; omega⟩
      rw [map_neg, LinearMap.neg_apply, neg_eq_zero] at h
      exact h
    · exact hpos α ⟨hα, hp'⟩
  have hc := rootAnnihilatorCentrality k G r.data.T r.isCompatible.maximalSplit.isSplitSubtorus.1
    r.data.i (cocharacterMapInt r.data.f m) hall
  rw [← r.isCompatible.factor_comp]
  exact hc

end Reductive

end FiniteType

end Langlands.GroupScheme.ParabolicRootPresentation

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RealTorusSpace ParabolicRootPresentation

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

local instance casselmanChamberAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

/-- Strict bounds at every split-component point of the closed restricted-root
chamber with some positive valuation put the normalized real part of an
exponent of a representation with a unitary central character in the strictly
positive root cone. -/
theorem normalizedRealPart_mem_positiveCone_of_norm_lt_one
    (hG : IsConnectedReductive G) (ha : IsSplitComponent a)
    (pres : ParabolicRootPresentation p l a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (c : UnitaryCentralCharacter π.representation)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ)
    (hbound : ∀ t : rationalPoints A.toGrp,
      (∀ β ∈ pres.restrictedRoots, 0 ≤ pair A β
        (Plancherel.SplitTorus.valuation ha.isCentralSplitTorus.1.1 t).toAdd) →
      (∃ β ∈ pres.restrictedRoots, 0 < pair A β
        (Plancherel.SplitTorus.valuation ha.isCentralSplitTorus.1.1 t).toAdd) →
      ‖(χ t : ℂ)‖ < 1) :
    Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
      pres.positiveCone := by
  have := ha.isAffine
  let := RationalPointFamily.splitComponentPointTopology ha
  let hA := ha.isCentralSplitTorus.1.1
  apply pres.mem_positiveCone_of_latticePair (pres.linearIndependent_simpleRoots hG) hA
  · intro m hm
    have hc := pres.isCentral_of_pairing_eq_zero hG m hm
    have h0 := normalizedJacquetExponent_realPart_restrict_eq_zero p l r hp hl hr hmul ha
      isSplitTorus_gm m hc π c χ hχ
    rw [latticePair_apply]
    have hmap : cocharacterMapReal m ((1 : ℝ) ⊗ₜ[ℤ] (𝟙 (Gm (Spec (CommRingCat.of k))))) =
        (1 : ℝ) ⊗ₜ[ℤ] m := by
      rw [cocharacterMapReal_tmul, Category.id_comp]
    rw [← hmap, pair_cocharacterMapReal, h0, map_zero, LinearMap.zero_apply]
  · intro m hnonneg hposm
    let t := CocharacterUniformizer.latticeSection k A (Multiplicative.ofAdd m)
    have hval : (Plancherel.SplitTorus.valuation hA t).toAdd = (1 : ℝ) ⊗ₜ[ℤ] m :=
      Plancherel.SplitTorus.valuation_latticeSection hA m
    have hroot : ∀ β ∈ pres.restrictedRoots, ∃ α ∈ simpleRelativeRoots pres.data.i pres.data.ν,
        α ∉ pres.data.J ∧ pair A β (Plancherel.SplitTorus.valuation hA t).toAdd =
          (latticePairing A (pres.data.f ≫ α) m : ℝ) := by
      intro β hβ
      obtain ⟨α, hα, hJ, rfl⟩ := pres.mem_restrictedRoots.mp hβ
      refine ⟨α, hα, hJ, ?_⟩
      rw [hval, pair_tmul_tmul, one_mul, one_mul]
    have hlt := hbound t
      (fun β hβ => by
        obtain ⟨α, hα, hJ, he⟩ := hroot β hβ
        rw [he]
        exact_mod_cast hnonneg α hα hJ)
      (by
        obtain ⟨α, hα, hJ, hαpos⟩ := hposm
        refine ⟨_, restrictedRootVector_mem_restrictedSimpleRoots pres.data.i pres.data.ν
          pres.data.J pres.data.f hα hJ, ?_⟩
        rw [hval, restrictedRootVector_eq_tmul, pair_tmul_tmul, one_mul, one_mul]
        exact_mod_cast hαpos)
    rw [Plancherel.SplitTorus.norm_eq_rpow_normalizedRealPart hA χ hχ.1 t, hval] at hlt
    have hq : (1 : ℝ) < (LocalField.residueCardinality k : ℝ) := by
      exact_mod_cast LocalField.residueCardinality_gt_one k
    rcases (Real.rpow_lt_one_iff_of_pos (by linarith)).mp hlt with h | h
    · rw [latticePair_apply]
      linarith [h.2]
    · exact absurd h.1 (not_lt.mpr hq.le)

/-- For an exponent of a representation with a unitary central character of a
connected reductive group, membership of the normalized real part in the
strictly positive root cone is equivalent to strict bounds at all points of
the closed restricted-root chamber with some positive valuation. -/
theorem normalizedRealPart_mem_positiveCone_iff_norm_lt_one
    (hG : IsConnectedReductive G) (ha : IsSplitComponent a)
    (pres : ParabolicRootPresentation p l a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (c : UnitaryCentralCharacter π.representation)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ) :
    Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
        pres.positiveCone ↔
      ∀ t : rationalPoints A.toGrp,
        (∀ β ∈ pres.restrictedRoots, 0 ≤ pair A β
          (Plancherel.SplitTorus.valuation ha.isCentralSplitTorus.1.1 t).toAdd) →
        (∃ β ∈ pres.restrictedRoots, 0 < pair A β
          (Plancherel.SplitTorus.valuation ha.isCentralSplitTorus.1.1 t).toAdd) →
        ‖(χ t : ℂ)‖ < 1 := by
  refine ⟨fun hcone t hnonneg hpos => ?_,
    normalizedRealPart_mem_positiveCone_of_norm_lt_one p l r hp hl hr hmul hG ha pres π c χ hχ⟩
  exact norm_lt_one_of_normalizedRealPart_mem_positiveCone pres χ hχ.1 hcone t hnonneg hpos

end Langlands.Aubert.General.RepresentedParabolic
