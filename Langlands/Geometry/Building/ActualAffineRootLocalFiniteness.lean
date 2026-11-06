import Langlands.Geometry.Building.ActualAffineRootArrangement
import Langlands.Geometry.Building.FilteredRootReflectionCells
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring

/-! # Discrete actual root-value differences from V6 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.BruhatTits Langlands.Plancherel

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- A positive multiple of every torus character extends to the actual centralizer. -/
theorem exists_rootCharacterDenominator (a : characterLattice B.S) :
    ∃ d : ℕ, 0 < d ∧ ∃ χ : rationalCharacters B.centralizer.Z,
      Cartan.characterRestriction B.centralizer.s χ = d • a := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have : IsClosedImmersion B.centralizer.j.hom.hom.left :=
    B.centralizer.isClosedSubgroup
  have : IsAffineHom B.centralizer.Z.X.hom := by
    rw [← B.centralizer.j.hom.hom.w]
    infer_instance
  have : LocallyOfFiniteType B.centralizer.Z.X.hom := by
    rw [← B.centralizer.j.hom.hom.w]
    infer_instance
  have hs : IsCentralSplitTorus B.centralizer.s := by
    refine ⟨⟨B.isMaximalSplitTorus.isSplitSubtorus.1, ?_⟩, ?_⟩
    · apply IsClosedSubgroup.of_comp B.centralizer.isClosedSubgroup
      rw [B.centralizer.comp_eq]
      exact B.isMaximalSplitTorus.isSplitSubtorus.2
    · apply isCentral_of_range_le_torusCentralizer B.centralizer.isRepresentedBy.1
      rw [B.centralizer.comp_eq]
      exact B.centralizer.isRepresentedBy.2.le
  have hindex := CharacterRestrictionFiniteIndex.finiteIndex_range_characterRestrict
    B.centralizer.s hs
  obtain ⟨d, hd, _, χ, hχ⟩ :=
    (characterRestrict B.centralizer.s).range.exists_nsmul_mem_of_index_ne_zero
      hindex.index_ne_zero ((rationalCharacters.equivCharacterLattice B.S).symm a)
  refine ⟨d, hd, χ, ?_⟩
  change (rationalCharacters.equivCharacterLattice B.S)
    (characterRestrict B.centralizer.s χ) = d • a
  rw [hχ, map_nsmul, AddEquiv.apply_symm_apply]

/-- A positive integer clearing the extension obstruction for an actual torus character. -/
def rootCharacterDenominator (a : characterLattice B.S) : ℕ :=
  (B.exists_rootCharacterDenominator a).choose

theorem rootCharacterDenominator_pos (a : characterLattice B.S) :
    0 < B.rootCharacterDenominator a :=
  (B.exists_rootCharacterDenominator a).choose_spec.1

theorem exists_character_rootCharacterDenominator (a : characterLattice B.S) :
    ∃ χ : rationalCharacters B.centralizer.Z,
      Cartan.characterRestriction B.centralizer.s χ =
        B.rootCharacterDenominator a • a :=
  (B.exists_rootCharacterDenominator a).choose_spec.2

/-- After clearing that denominator, every actual centralizer translation has
integral evaluation in the chosen character direction. -/
theorem rootCharacterDenominator_eval_translation
    (a : characterLattice B.S) (z : rationalPoints B.centralizer.Z) :
    ∃ m : ℤ, (B.rootCharacterDenominator a : ℝ) *
      eval B.S a (B.centralizer.translation z).toAdd = (m : ℝ) := by
  obtain ⟨χ, hχ⟩ := B.exists_character_rootCharacterDenominator a
  refine ⟨-((rationalCharacterValuation B.centralizer.Z z).toAdd χ), ?_⟩
  have he := eval_centralizerTranslation B.centralizer.s B.centralizer.bijective z χ
  rw [hχ] at he
  simpa only [eval_eq_pair, TensorProduct.tmul_smul, map_nsmul,
    LinearMap.smul_apply, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Int.cast_neg] using he

variable {a : relativeRoots B.i} {g₀ g : rationalPoints G}
    {p₀ p : rationalPoints G × rationalPoints G}

/-- The correction between two same-root reflections has an actual centralizer lift. -/
theorem exists_centralizer_reflection_correction
    (hg₀ : g₀ ∈ B.rootGroup a) (hg₀1 : g₀ ≠ 1)
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp₀ : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g₀ p₀)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p) :
    ∃ z : rationalPoints B.centralizer.Z,
      B.centralizer.toNormalizer z = (B.reflectionElement hp₀)⁻¹ * B.reflectionElement hp := by
  have hc := B.reflectionElement_inv_mul_mem_centralizer hg₀ hg₀1 hg hg1 hp₀ hp
  rw [← torusCentralizer_carrier_base, ← B.centralizer.isRepresentedBy.2] at hc
  obtain ⟨z, hz⟩ := hc
  exact ⟨z, Subtype.ext hz⟩

/-- Any functional with the same actual root derivative changes by twice the
reflecting root functional under its opposite-pair reflection. -/
theorem reflectionFunctional_reflectionElement_same_root
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p)
    (x : B.Apartment) :
    B.reflectionFunctional a g₀ (B.reflectionElement hp • x) =
      B.reflectionFunctional a g₀ x - 2 * B.reflectionFunctional a g x := by
  change B.reflectionFunctional a g₀
    (B.apartment.normalizerAffineEquiv (B.reflectionElement hp) x) = _
  rw [B.normalizerAffineEquiv_reflectionElement hg hg1 hp]
  change B.reflectionFunctional a g₀
    ((-B.reflectionFunctional a g x) • B.reflectionCoroot hg hg1 hp +ᵥ x) = _
  simp only [AffineMap.map_vadd, reflectionFunctional_linear, map_smul,
    B.rootForm_reflectionCoroot hg hg1 hp, smul_eq_mul, vadd_eq_add]
  ring

/-- V6 identifies a same-root value difference with an actual centralizer translation. -/
theorem exists_translation_eval_eq_rootValueDifference
    (hg₀ : g₀ ∈ B.rootGroup a) (hg₀1 : g₀ ≠ 1)
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp₀ : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g₀ p₀)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p)
    (x : B.Apartment) :
    ∃ z : rationalPoints B.centralizer.Z,
      eval B.S a (B.centralizer.translation z).toAdd =
        2 * (B.reflectionFunctional a g x - B.reflectionFunctional a g₀ x) := by
  obtain ⟨z, hz⟩ := B.exists_centralizer_reflection_correction hg₀ hg₀1 hg hg1 hp₀ hp
  refine ⟨z, ?_⟩
  have hneg (y : B.Apartment) :
      B.reflectionFunctional a g₀ (B.reflectionElement hp₀ • y) =
        -B.reflectionFunctional a g₀ y := by
    have h := B.reflectionFunctional_reflectionElement_same_root
      (g₀ := g₀) hg₀ hg₀1 hp₀ y
    linarith
  have hneginv (y : B.Apartment) :
      B.reflectionFunctional a g₀ ((B.reflectionElement hp₀)⁻¹ • y) =
        -B.reflectionFunctional a g₀ y := by
    have h := hneg ((B.reflectionElement hp₀)⁻¹ • y)
    rw [smul_inv_smul] at h
    linarith
  have he := congrArg (fun y : B.Apartment => B.reflectionFunctional a g₀ y)
    (B.isOmegaCompatible.smul_eq_vadd z x)
  rw [hz, mul_smul, hneginv,
    B.reflectionFunctional_reflectionElement_same_root hg hg1 hp x] at he
  simp only [AffineMap.map_vadd, reflectionFunctional_linear, rootForm_mk, vadd_eq_add] at he
  linarith

/-- Every same-root value difference becomes integral after a fixed positive scaling. -/
theorem rootValueDifference_integer
    (hg₀ : g₀ ∈ B.rootGroup a) (hg₀1 : g₀ ≠ 1)
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp₀ : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g₀ p₀)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p)
    (x : B.Apartment) :
    ∃ m : ℤ, (2 * (B.rootCharacterDenominator a : ℝ)) *
      (B.reflectionFunctional a g x - B.reflectionFunctional a g₀ x) = (m : ℝ) := by
  obtain ⟨z, hz⟩ :=
    B.exists_translation_eval_eq_rootValueDifference hg₀ hg₀1 hg hg1 hp₀ hp x
  obtain ⟨m, hm⟩ := B.rootCharacterDenominator_eval_translation a z
  refine ⟨m, ?_⟩
  rw [hz] at hm
  nlinarith only [hm]

private theorem finite_integer_abs_le (C : ℝ) :
    {m : ℤ | |(m : ℝ)| ≤ C}.Finite := by
  refine (Set.finite_Icc (-⌈C⌉) ⌈C⌉).subset ?_
  intro m hm
  have hbound := abs_le.mp (hm.trans (Int.le_ceil C))
  constructor
  · exact_mod_cast hbound.1
  · exact_mod_cast hbound.2

/-- The same-root point functionals have finitely many bounded values at each point. -/
theorem finite_bounded_reflectionFunctionals_of_oppositePairs
    (hF : RelativeRoot.HasOppositeFactorPairs B.i)
    (a : relativeRoots B.i) (x : B.Apartment) (bound : ℝ) :
    {ψ : B.Apartment →ᵃ[ℝ] ℝ |
      ∃ g ∈ B.rootGroup a, g ≠ 1 ∧ ψ = B.reflectionFunctional a g ∧
        |ψ x| ≤ bound}.Finite := by
  obtain ⟨g₀, hg₀, hgtop⟩ := x.isValuation.exists_ne_top a.property
  have hg₀1 : g₀ ≠ 1 := by
    rintro rfl
    exact hgtop (B.val_apply_one a x)
  obtain ⟨p₀, hp₀⟩ := hF a a.property g₀ hg₀ hg₀1
  let d : ℝ := 2 * (B.rootCharacterDenominator a : ℝ)
  have hd : 0 < d := mul_pos (by norm_num)
    (by exact_mod_cast B.rootCharacterDenominator_pos a)
  let r₀ : ℝ := B.reflectionFunctional a g₀ x
  let M : Set ℤ := {m | |(m : ℝ)| ≤ d * (bound + |r₀|)}
  have hM : M.Finite := finite_integer_abs_le _
  refine (hM.image (fun m : ℤ =>
    B.apartment.affineFunctional a x (r₀ + (m : ℝ) / d))).subset ?_
  rintro ψ ⟨g, hg, hg1, rfl, hbound⟩
  obtain ⟨p, hp⟩ := hF a a.property g hg hg1
  obtain ⟨m, hm⟩ := B.rootValueDifference_integer hg₀ hg₀1 hg hg1 hp₀ hp x
  change d * (B.reflectionFunctional a g x - r₀) = (m : ℝ) at hm
  have hmM : m ∈ M := by
    change |(m : ℝ)| ≤ d * (bound + |r₀|)
    calc
      |(m : ℝ)| = d * |B.reflectionFunctional a g x - r₀| := by
        rw [← hm, abs_mul, abs_of_pos hd]
      _ ≤ d * (|B.reflectionFunctional a g x| + |r₀|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) hd.le
      _ ≤ d * (bound + |r₀|) :=
        mul_le_mul_of_nonneg_left (add_le_add hbound le_rfl) hd.le
  refine ⟨m, hmM, ?_⟩
  apply AffineMap.ext_linear (by rfl) (p := x)
  have hval : r₀ + (m : ℝ) / d = B.reflectionFunctional a g x := by
    have hmdiv : (m : ℝ) / d = B.reflectionFunctional a g x - r₀ :=
      (div_eq_iff hd.ne').mpr (by nlinarith only [hm])
    linarith only [hmdiv]
  simpa only [KPApartmentData.affineFunctional_apply, vsub_self, map_zero, zero_add]
    using hval

/-- Full V6 and actual opposite pairs imply bounded finiteness of ordinary affine roots. -/
theorem finite_bounded_affineRoots_of_oppositePairs
    (hF : RelativeRoot.HasOppositeFactorPairs B.i)
    (x : B.Apartment) (bound : Module.Dual ℝ (TranslationSpace B.i) → ℝ) :
    {ψ | ψ ∈ B.affineRoots ∧ |ψ x| ≤ bound ψ.linear}.Finite := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  let := B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i |>.fintype
  let S : relativeRoots B.i → Set (B.Apartment →ᵃ[ℝ] ℝ) := fun a =>
    {ψ | ∃ g ∈ B.rootGroup a, g ≠ 1 ∧ ψ = B.reflectionFunctional a g ∧
      |ψ x| ≤ bound (rootForm B.i a)}
  have hfin : (⋃ a ∈ (Set.univ : Set (relativeRoots B.i)), S a).Finite :=
    Set.finite_univ.biUnion fun a _ =>
      B.finite_bounded_reflectionFunctionals_of_oppositePairs hF a x _
  refine hfin.subset ?_
  rintro ψ ⟨hψ, hbound⟩
  have hψ' := B.apartment.affineRoots_subset_extendedAffineRoots hψ
  rw [← B.reflectionAffineRoots_eq] at hψ'
  obtain ⟨a, g, hg, hg1, rfl⟩ := hψ'
  refine Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨Set.mem_univ _, ?_⟩⟩
  exact ⟨g, hg, hg1, rfl, hbound⟩

/-- Actual supplied data form a locally finite reflection arrangement from
opposite-pair existence alone; neither V7 nor AS5 is used. -/
theorem isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
    (hF : RelativeRoot.HasOppositeFactorPairs B.i) :
    AffineRootSystem.IsLocallyFiniteReflectionArrangement B.affineRoots :=
  B.isLocallyFiniteReflectionArrangement_of_oppositePairs hF
    (B.finite_bounded_affineRoots_of_oppositePairs hF)

/-- With actual opposite pairs, generation modulo the action kernel is the sole
remaining membership premise for this actual normalizer facet-fixing conclusion. -/
theorem normalizer_facet_fixing_of_reflections_sup_ker_of_oppositePairs
    (hF : RelativeRoot.HasOppositeFactorPairs B.i)
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    (n : normalizerPoints B.i)
    (hn : n ∈ B.reflectionNormalizer ⊔ B.apartment.normalizerAffineEquiv.ker)
    (hfix : (fun x : B.Apartment => n • x) '' Fa = Fa) :
    ∀ x ∈ Fa, n • x = x :=
  B.normalizer_facet_fixing_of_mem_reflectionNormalizer_sup_ker hF
    (B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs hF) hFa n hn hfix

end Langlands.Geometry.Building.ValuationBuildingData
