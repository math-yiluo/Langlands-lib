import Langlands.Geometry.Building.IntegerValuationAffineWeylProof
import Langlands.Geometry.Building.ChamberWallProductAssembly

/-! # Extended affine roots for explicit integer-valued building data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

variable {a : relativeRoots B.i} {g : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}

/-- The coroot of an actual opposite pair is a coroot of the extended affine roots. -/
theorem isCoroot_reflectionCoroot_extendedAffineRoots
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p) :
    AffineRootSystem.IsCoroot B.apartment.extendedAffineRoots (B.reflectionFunctional a g)
      (B.reflectionCoroot hg hg1 hp) := by
  refine ⟨B.rootForm_reflectionCoroot hg hg1 hp, fun f hf => ?_⟩
  have hm := B.apartment.normalizerAffineEquiv_mem_rootStabilizer_extendedAffineRoots
    (B.reflectionElement hp)
  rw [B.normalizerAffineEquiv_reflectionElement hg hg1 hp] at hm
  have hf' := (hm f).2 hf
  exact (AffineRootSystem.comp_affineReflection (B.reflectionFunctional a g)
    (B.rootForm_reflectionCoroot hg hg1 hp) f) ▸ hf'


/-- The derivative of `Ψ′` is `Φ` (AS 2): every actual root has a nonidentity point with a
finite value. -/
theorem derivativeRoots_extendedAffineRoots :
    AffineRootSystem.derivativeRoots B.apartment.extendedAffineRoots =
      Set.range (rootForm B.i) := by
  apply Set.Subset.antisymm
  · rintro f ⟨ψ, ⟨a, hlin, _⟩, rfl⟩
    exact ⟨a, hlin.symm⟩
  · rintro _ ⟨a, rfl⟩
    let x : B.Apartment := Classical.arbitrary B.Apartment
    obtain ⟨g, hg, hgtop⟩ := x.isValuation.exists_ne_top a.property
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hgtop
    exact ⟨_, B.apartment.affineFunctional_mem_extendedAffineRoots hg hr.symm, rfl⟩

theorem finite_derivativeRoots_extendedAffineRoots :
    (AffineRootSystem.derivativeRoots B.apartment.extendedAffineRoots).Finite := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  let := B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i |>.fintype
  rw [B.derivativeRoots_extendedAffineRoots]
  exact Set.finite_range _

theorem span_derivativeRoots_extendedAffineRoots :
    Submodule.span ℝ (AffineRootSystem.derivativeRoots B.apartment.extendedAffineRoots) = ⊤ :=
  top_unique <| (B.span_derivativeRoots_affineRoots).symm.le.trans <| Submodule.span_mono <|
      Set.image_mono B.apartment.affineRoots_subset_extendedAffineRoots

/-- Coroots of `Ψ′`: those of the actual opposite pairs. -/
theorem exists_isCoroot_extendedAffineRoots {ψ : B.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ B.apartment.extendedAffineRoots) :
    ∃ v : TranslationSpace B.i,
      AffineRootSystem.IsCoroot B.apartment.extendedAffineRoots ψ v := by
  rw [← B.reflectionAffineRoots_eq] at hψ
  obtain ⟨a, g, hg, hg1, rfl⟩ := hψ
  obtain ⟨p, hp⟩ := B.hasOppositeFactorPairs a a.property g hg hg1
  exact ⟨_, B.isCoroot_reflectionCoroot_extendedAffineRoots hg hg1 hp⟩

/-- A chosen actual coroot for an extended affine root of the supplied data. -/
def extendedAffineRootCoroot (ψ : B.Apartment →ᵃ[ℝ] ℝ)
    (hψ : ψ ∈ B.apartment.extendedAffineRoots) : TranslationSpace B.i :=
  Classical.choose (B.exists_isCoroot_extendedAffineRoots hψ)

/-- The chosen extended-root coroot preserves the same extended affine roots. -/
theorem isCoroot_extendedAffineRootCoroot (ψ : B.Apartment →ᵃ[ℝ] ℝ)
    (hψ : ψ ∈ B.apartment.extendedAffineRoots) :
    AffineRootSystem.IsCoroot B.apartment.extendedAffineRoots ψ
      (B.extendedAffineRootCoroot ψ hψ) :=
  Classical.choose_spec (B.exists_isCoroot_extendedAffineRoots hψ)

/-- AR 3 for `Ψ′`: every coroot of `Ψ′` is the integral coroot of an opposite pair. -/
theorem coroot_integral_extendedAffineRoots {ψ θ : B.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ B.apartment.extendedAffineRoots) (hθ : θ ∈ B.apartment.extendedAffineRoots)
    {v : TranslationSpace B.i}
    (hv : AffineRootSystem.IsCoroot B.apartment.extendedAffineRoots θ v) :
    ∃ n : ℤ, ψ.linear v = n := by
  obtain ⟨b, hb, -⟩ := hψ
  rw [← B.reflectionAffineRoots_eq] at hθ
  obtain ⟨a, g, hg, hg1, rfl⟩ := hθ
  obtain ⟨p, hp⟩ := B.hasOppositeFactorPairs a a.property g hg hg1
  have hvv := AffineRootSystem.isCoroot_unique_of_finite_of_span
    B.finite_derivativeRoots_extendedAffineRoots B.span_derivativeRoots_extendedAffineRoots
    (B.isCoroot_reflectionCoroot_extendedAffineRoots hg hg1 hp) hv
  rw [hb, ← hvv]
  exact B.rootForm_reflectionCoroot_integral hg hg1 hp b


/-- Bounded finiteness of `Ψ′` at a point (KP Proposition 6.3.7, from V 6). -/
theorem finite_bounded_extendedAffineRoots (x : B.Apartment) (C : ℝ) :
    {ψ | ψ ∈ B.apartment.extendedAffineRoots ∧ |ψ x| ≤ C}.Finite := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  let := B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i |>.fintype
  refine (Set.finite_univ.biUnion fun a _ =>
    B.finite_bounded_reflectionFunctionals_of_oppositePairs B.hasOppositeFactorPairs a x C).subset
      ?_
  rintro ψ ⟨hψ, hbound⟩
  rw [← B.reflectionAffineRoots_eq] at hψ
  obtain ⟨a, g, hg, hg1, rfl⟩ := hψ
  exact Set.mem_biUnion (Set.mem_univ a) ⟨g, hg, hg1, rfl, hbound⟩

/-- AS 2: `Ψ′` is an affine root system. -/
theorem isAffineRootSystemWithRankZero_extendedAffineRoots
    (hunit : ∃ t : kˣ, IntegerValuation.order v t = 1) :
    AffineRootSystem.IsAffineRootSystemWithRankZero B.apartment.extendedAffineRoots where
  span_derivativeRoots_eq_top := B.span_derivativeRoots_extendedAffineRoots
  linear_ne_zero := fun ψ hψ hzero => by
    obtain ⟨v, hv⟩ := B.exists_isCoroot_extendedAffineRoots hψ
    have h := hv.1
    rw [hzero, LinearMap.zero_apply] at h
    norm_num at h
  finite_derivativeRoots := B.finite_derivativeRoots_extendedAffineRoots
  exists_isCoroot := fun _ hψ => B.exists_isCoroot_extendedAffineRoots hψ
  coroot_integral := fun _ hψ _ hθ _ hv => B.coroot_integral_extendedAffineRoots hψ hθ hv
  infinite_fiber := fun _ hψ => B.infinite_fiber_extendedAffineRoots hunit hψ
  finite_bounded := fun ψ _ M => by
    let x : B.Apartment := Classical.arbitrary B.Apartment
    refine (B.finite_bounded_extendedAffineRoots x (M + |ψ x|)).subset ?_
    rintro θ ⟨hθ, -, hM⟩
    refine ⟨hθ, ?_⟩
    calc |θ x| = |(θ x - ψ x) + ψ x| := by ring_nf
      _ ≤ |θ x - ψ x| + |ψ x| := abs_add_le _ _
      _ ≤ M + |ψ x| := add_le_add (hM x) le_rfl


/-- Every extended root is an ordinary root or half an ordinary root. -/
theorem mem_or_two_smul_mem_affineRoots
    {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ B.apartment.extendedAffineRoots) :
    ψ ∈ B.affineRoots ∨ (2 : ℝ) • ψ ∈ B.affineRoots := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  exact B.apartment.mem_or_two_smul_mem_affineRoots_of_oppositePairs
    B.isMaximalSplitTorus.1.1 B.hasOppositeFactorPairs hψ

end Langlands.Geometry.Building.IntegerValuationBuildingData
