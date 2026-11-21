import Langlands.Geometry.Building.TorusParahoricBuildingConstruction
import Langlands.Geometry.Building.KPLieFiltrationDual
import Langlands.BruhatTits.IntegralModels.SplitTorusDepthZero
import Langlands.GroupScheme.Lie.SplitTorusCoordinates
import Mathlib.RingTheory.Nakayama

/-! # The root-free Lie filtration of a split torus -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (I : Type u) [Finite I]

local notation "T" => splitTorus.commGroupScheme (Spec (CommRingCat.of F)) I
local notation "P" => ofTorus T (IsSplitTorus.isTorus (isSplitTorus_splitTorus I))

local instance : IsAffineHom (T).toGrp.X.hom := isAffineHom_splitTorus_spec _ I

local notation "A₀" => IntegralModel.lieLattice (IntegralModel.splitTorusModel 𝒪[F] F I)

private theorem splitTorus_affineRoots_isEmpty : IsEmpty (P).affineRoots := by
  have : Smooth (T).toGrp.X.hom := (P).isConnectedReductive.smooth
  have hΦ := ValuationBuildingData.relativeRoots_eq_empty_of_commutative (P).i
    (P).isMaximalSplitTorus.isSplitSubtorus
  have : IsEmpty (relativeRoots (P).i) := Set.isEmpty_coe_sort.2 hΦ
  exact ⟨fun ψ => by
    obtain ⟨a, _, _⟩ := ψ.2
    exact isEmptyElim a⟩

/-- The root-free Lie filtration on the actual split torus `Gₘ^I`. At nonnegative
real depth `r`, the centralizer lattice is `𝔪^⌈r⌉ • Lie(Gₘ,𝒪^I)`. -/
def splitTorusLieFiltration : (P).LieFiltrationData where
  centralizerLie r := 𝓂[F] ^ ⌈(r : ℝ)⌉₊ • A₀
  centralizerLie_antitone := by
    intro r s hrs
    exact Submodule.smul_mono_left
      (pow_le_pow_right_of_le_one' (by simp) (Nat.ceil_mono (NNReal.coe_le_coe.2 hrs)))
  affineRootLie := fun ψ => (splitTorus_affineRoots_isEmpty F I).false ψ |>.elim
  affineRootLie_le := fun ψ => (splitTorus_affineRoots_isEmpty F I).false ψ |>.elim

local notation "L" => splitTorusLieFiltration F I

/-- The filtration does not depend on the apartment point. There are no affine-root
summands and the differential of the centralizer inclusion is the identity. -/
theorem splitTorus_lieFiltration (x : (P).Apartment) (r : NNReal) :
    (L).lieFiltration x r = 𝓂[F] ^ ⌈(r : ℝ)⌉₊ • A₀ := by
  let := splitTorus_affineRoots_isEmpty F I
  rw [LieFiltrationData.lieFiltration, iSup_of_empty, sup_bot_eq]
  have hid : GenericLie.map 𝒪[F] (𝟙 (T).toGrp) = LinearMap.id := by
    ext y
    apply Additive.toMul.injective
    apply Subtype.ext
    exact Category.comp_id _
  change Submodule.map (GenericLie.map 𝒪[F] (𝟙 (T).toGrp)) (𝓂[F] ^ ⌈(r : ℝ)⌉₊ • A₀) = _
  rw [hid, Submodule.map_id]

/-- The standard model supplies the actual depth-zero lattice. -/
@[simp] theorem splitTorus_lieFiltration_zero (x : (P).Apartment) :
    (L).lieFiltration x 0 = A₀ := by
  rw [splitTorus_lieFiltration]
  simp

/-- Increasing depth by one multiplies by the maximal ideal. -/
theorem splitTorus_lieFiltration_isPeriodic : (L).IsPeriodic := by
  intro x r
  rw [splitTorus_lieFiltration, splitTorus_lieFiltration]
  have hr : ⌈((r : ℝ) + 1)⌉₊ = ⌈(r : ℝ)⌉₊ + 1 := by
    rw [← Int.natCast_inj, Int.natCast_ceil_eq_ceil (by positivity), Nat.cast_add,
      Int.natCast_ceil_eq_ceil r.coe_nonneg, Int.ceil_add_one, Nat.cast_one]
  rw [NNReal.coe_add, NNReal.coe_one, hr, pow_succ', Submodule.mul_smul]

private theorem smul_lattice_eq_pow_ideal {π : 𝒪[F]} (hπ : Irreducible π) (n : ℕ) :
    (π : F) ^ n • A₀ = 𝓂[F] ^ n • A₀ := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  have hsmul (z : GenericLie 𝒪[F] (T).toGrp) : (π ^ n) • z = (π : F) ^ n • z := by
    rw [GenericLie.smul_def, map_pow]
    rfl
  ext y
  simp only [Submodule.mem_smul_pointwise_iff_exists, hsmul]

/-- At every real depth, including negative depths, the lattice is the integral
Lie lattice scaled by the indicated integer power of any uniformizer. -/
theorem splitTorus_lieFiltrationReal (x : (P).Apartment) (r : ℝ) {π : 𝒪[F]} (hπ : Irreducible π) :
    (L).lieFiltrationReal x r = (π : F) ^ ⌈r⌉ • A₀ := by
  let n := LieFiltrationData.indexShift r
  have hπ₀ : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hc : (⌈(LieFiltrationData.shiftedIndex r : ℝ)⌉₊ : ℤ) = ⌈r⌉ + n := by
    rw [Int.natCast_ceil_eq_ceil (LieFiltrationData.shiftedIndex r).coe_nonneg]
    change ⌈r + (n : ℝ)⌉ = ⌈r⌉ + n
    rw [Int.ceil_add_natCast]
  have hscaled : (L).lieFiltration x (LieFiltrationData.shiftedIndex r) =
      (π : F) ^ n • ((π : F) ^ ⌈r⌉ • A₀) := by
    rw [splitTorus_lieFiltration, ← smul_lattice_eq_pow_ideal F I hπ, ← mul_smul]
    congr 1
    rw [← zpow_natCast, hc, zpow_add₀ hπ₀, mul_comm, zpow_natCast]
  ext y
  rw [LieFiltrationData.mem_lieFiltrationReal, hscaled]
  change (∀ a ∈ 𝓂[F] ^ n, a • y ∈ (π : F) ^ n • ((π : F) ^ ⌈r⌉ • A₀)) ↔ _
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  constructor
  · intro hy
    have h := hy (π ^ n) (Ideal.mem_span_singleton_self _)
    rw [GenericLie.smul_def, map_pow, Submodule.mem_smul_pointwise_iff_exists] at h
    obtain ⟨z, hz, hzy⟩ := h
    have hzy' : z = y := smul_right_injective _ (pow_ne_zero n hπ₀) hzy
    simpa only [hzy'] using hz
  · intro hy a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [mul_smul, smul_comm b, GenericLie.smul_def 𝒪[F] (T).toGrp (π ^ n) (b • y), map_pow]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.smul_mem _ _ hy)

/-- For the strict piece the exponent is the least integer strictly above `r`. -/
theorem splitTorus_lieFiltrationPlusReal (x : (P).Apartment) (r : ℝ) {π : 𝒪[F]}
    (hπ : Irreducible π) :
    (L).lieFiltrationPlusReal x r = (π : F) ^ (⌊r⌋ + 1 : ℤ) • A₀ := by
  let s : ℝ := (⌊r⌋ : ℝ) + 1
  have hrs : r < s := Int.lt_floor_add_one r
  have hs : ⌈s⌉ = ⌊r⌋ + 1 := by simp [s]
  rw [← hs, ← splitTorus_lieFiltrationReal F I x s hπ]
  refine le_antisymm ?_ ((L).lieFiltrationReal_le_lieFiltrationPlusReal x hrs)
  refine iSup₂_le fun t hrt => ?_
  by_cases hst : s ≤ t
  · exact (L).lieFiltrationReal_antitone (splitTorus_lieFiltration_isPeriodic F I) x hst
  · have ht : ⌈t⌉ = ⌊r⌋ + 1 := Int.ceil_eq_iff.2 (by
      push_cast
      constructor
      · linarith [Int.floor_le r]
      · exact le_of_lt (lt_of_not_ge hst))
    rw [splitTorus_lieFiltrationReal F I x t hπ, splitTorus_lieFiltrationReal F I x s hπ, ht, hs]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem splitTorus_lieLattice_isLattice : Submodule.IsLattice F A₀ :=
  IntegralModel.lieLattice_isLattice (IntegralModel.splitTorusModel_isSmooth 𝒪[F] F I)

/-- Each real-depth piece is an integral lattice in the actual generic Lie space. -/
theorem splitTorus_lieFiltrationReal_isLattice (x : (P).Apartment) (r : ℝ) :
    Submodule.IsLattice F ((L).lieFiltrationReal x r) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hπ₀ : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  let := splitTorus_lieLattice_isLattice F I
  rw [splitTorus_lieFiltrationReal F I x r hπ]
  exact Submodule.IsLattice.smul _ _ (Units.mk0 _ (zpow_ne_zero _ hπ₀))

private theorem maximalIdeal_smul_splitTorusLieLattice_lt [Nonempty I] : 𝓂[F] • A₀ < A₀ := by
  have hA := splitTorus_lieLattice_isLattice F I
  refine lt_of_le_of_ne Submodule.smul_le_right fun he => ?_
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot 𝓂[F] A₀ hA.fg he.ge
    (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal 𝒪[F]) bot_ne_top).symm)
  have hspan := hA.span_eq_top
  rw [hbot, Submodule.bot_coe, Submodule.span_zero_singleton] at hspan
  have : Nontrivial (GenericLie 𝒪[F] (T).toGrp) :=
    (splitTorus.infinitesimalLinearEquiv (R := CommRingCat.of F) I F).injective.nontrivial
  exact bot_ne_top hspan

/-- The Lie filtration jumps at precisely the integer depths for a nontrivial
split torus. The empty product has no jumps. -/
theorem splitTorus_lieFiltrationPlusReal_lt_iff (x : (P).Apartment) (r : ℝ) :
    (L).lieFiltrationPlusReal x r < (L).lieFiltrationReal x r ↔
      Nonempty I ∧ r ∈ Set.range (Int.cast : ℤ → ℝ) := by
  by_cases hI : Nonempty I
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    rw [splitTorus_lieFiltrationPlusReal F I x r hπ, splitTorus_lieFiltrationReal F I x r hπ,
      and_iff_right hI]
    constructor
    · intro h
      refine ⟨⌊r⌋, ?_⟩
      by_contra hn
      have he : ⌈r⌉ = ⌊r⌋ + 1 := Int.ceil_eq_iff.2 (by
        push_cast
        exact ⟨by linarith [lt_of_le_of_ne (Int.floor_le r) hn], (Int.lt_floor_add_one r).le⟩)
      rw [he] at h
      exact lt_irrefl _ h
    · rintro ⟨n, rfl⟩
      have hπ₀ : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
      have hlt : (π : F) • A₀ < A₀ := by
        simpa only [pow_one] using (smul_lattice_eq_pow_ideal F I hπ 1).trans_lt
          (by simpa only [pow_one] using maximalIdeal_smul_splitTorusLieLattice_lt F I)
      rw [Int.floor_intCast, Int.ceil_intCast, zpow_add₀ hπ₀, zpow_one, mul_smul]
      refine lt_of_le_of_ne (smul_mono_right _ hlt.le) fun h => hlt.ne ?_
      have he := congrArg (fun A : Submodule 𝒪[F] (GenericLie 𝒪[F] (T).toGrp) =>
        ((π : F) ^ n)⁻¹ • A) h
      simpa only [inv_smul_smul₀ (zpow_ne_zero n hπ₀)] using he
  · have : IsEmpty I := not_nonempty_iff.mp hI
    have : Subsingleton (GenericLie 𝒪[F] (T).toGrp) :=
      (splitTorus.infinitesimalLinearEquiv (R := CommRingCat.of F) I F).symm.injective.subsingleton
    simp [hI, Submodule.eq_bot_of_subsingleton]

end Langlands.Geometry.Building.ParahoricBuildingData
