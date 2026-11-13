import Langlands.Geometry.Building.IntegerRootReflections
import Langlands.Geometry.Building.ActualAffineRootArrangement
import Langlands.Geometry.Building.AffineRootSystemPullback
import Langlands.GroupScheme.Reductive.RootDatumAssembly
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan

/-! # Finite spanning derivatives and integral coroots for integer-valuation data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (B : IntegerValuationBuildingData v G)

/-- Ordinary affine roots have finitely many derivative directions for the actual torus. -/
theorem finite_derivativeRoots_affineRoots :
    (AffineRootSystem.derivativeRoots B.affineRoots).Finite := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  let := B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i |>.fintype
  refine (Set.finite_range (rootForm B.i)).subset ?_
  rintro f ⟨ψ, ⟨a, hlin, _⟩, rfl⟩
  exact ⟨a, hlin.symm⟩

/-- Actual opposite pairs supply coroots for every ordinary affine root. -/
theorem exists_isCoroot_affineRoots
    {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ B.affineRoots) :
    ∃ v : TranslationSpace B.i, AffineRootSystem.IsCoroot B.affineRoots ψ v := by
  have hψ' := B.apartment.affineRoots_subset_extendedAffineRoots hψ
  rw [← B.reflectionAffineRoots_eq] at hψ'
  obtain ⟨a, g, hg, hg1, rfl⟩ := hψ'
  obtain ⟨p, hp⟩ := B.hasOppositeFactorPairs a a.property g hg hg1
  exact ⟨B.reflectionCoroot hg hg1 hp,
    B.isCoroot_reflectionCoroot_without_apartment_axioms hg hg1 hp⟩

/-- A coroot chosen from the actual opposite-pair construction for an ordinary root. -/
def affineRootCoroot
    {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ B.affineRoots) :
    TranslationSpace B.i :=
  (B.exists_isCoroot_affineRoots hψ).choose

theorem isCoroot_affineRootCoroot
    {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ B.affineRoots) :
    AffineRootSystem.IsCoroot B.affineRoots ψ (B.affineRootCoroot hψ) :=
  (B.exists_isCoroot_affineRoots hψ).choose_spec

/-- In particular every ordinary affine root is nonconstant. -/
theorem linear_ne_zero_affineRoots
    {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ B.affineRoots) :
    ψ.linear ≠ 0 := by
  obtain ⟨v, hv⟩ := B.exists_isCoroot_affineRoots hψ
  intro hzero
  have h := hv.1
  rw [hzero, LinearMap.zero_apply] at h
  norm_num at h

/-- V0, opposite-pair-derived AS4 and reduced root coordinates give spanning derivatives. -/
theorem span_derivativeRoots_affineRoots :
    Submodule.span ℝ (AffineRootSystem.derivativeRoots B.affineRoots) = ⊤ := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have : Module.Finite ℝ (V B.S) :=
    B.isMaximalSplitTorus.isSplitSubtorus.1.finite_realCocharacterSpace
  apply Submodule.span_eq_top_of_ne_zero
  intro v hv
  have hsep : ∃ a : relativeRoots B.i, rootForm B.i a v ≠ 0 := by
    by_contra! h
    exact hv (eq_zero_of_rootForm_eq_zero B.i v h)
  obtain ⟨a, ha⟩ := hsep
  let x : B.Apartment := Classical.arbitrary B.Apartment
  obtain ⟨g, hg, hgtop⟩ := x.isValuation.exists_ne_top a.property
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hgtop
  let ψ := B.apartment.affineFunctional a x r
  have hψ : ψ ∈ B.apartment.extendedAffineRoots :=
    B.apartment.affineFunctional_mem_extendedAffineRoots hg hr.symm
  have hlin : ψ.linear = rootForm B.i a := rfl
  rcases B.apartment.mem_or_two_smul_mem_affineRoots_of_oppositePairs
    B.isMaximalSplitTorus.isSplitSubtorus.1 B.hasOppositeFactorPairs hψ with h | h
  · refine ⟨ψ.linear, AffineRootSystem.linear_mem_derivativeRoots h, ?_⟩
    rwa [hlin]
  · refine ⟨((2 : ℝ) • ψ).linear, AffineRootSystem.linear_mem_derivativeRoots h, ?_⟩
    rw [AffineMap.smul_linear, hlin, LinearMap.smul_apply]
    exact mul_ne_zero (by norm_num) ha

/-- Every actual root takes an integral value on the coroot of an actual opposite pair. -/
theorem rootForm_reflectionCoroot_integral
    {a : relativeRoots B.i} {g : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p)
    (b : relativeRoots B.i) :
    ∃ n : ℤ, rootForm B.i b (B.reflectionCoroot hg hg1 hp) = n :=
  ⟨latticePairing B.S b.val
      (hp.coroot B.i B.isMaximalSplitTorus.isSplitSubtorus.1 a.property.1 hg hg1), by
    simp only [reflectionCoroot, rootForm_mk, eval_tmul, one_mul]⟩

/-- AR 1 already identifies every coroot of an ordinary affine root with its actual
opposite-pair coroot. -/
theorem reflectionCoroot_eq_of_isCoroot
    {a : relativeRoots B.i} {g : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p)
    {w : TranslationSpace B.i}
    (hw : AffineRootSystem.IsCoroot B.affineRoots (B.reflectionFunctional a g) w) :
    B.reflectionCoroot hg hg1 hp = w :=
  AffineRootSystem.isCoroot_unique_of_finite_of_span
    B.finite_derivativeRoots_affineRoots B.span_derivativeRoots_affineRoots
    (B.isCoroot_reflectionCoroot_without_apartment_axioms hg hg1 hp) hw

/-- AR 3 for the ordinary affine roots, without a local-finiteness premise. -/
theorem coroot_integral_affineRoots {ψ θ : B.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ B.affineRoots) (hθ : θ ∈ B.affineRoots) {w : TranslationSpace B.i}
    (hw : AffineRootSystem.IsCoroot B.affineRoots θ w) :
    ∃ n : ℤ, ψ.linear w = n := by
  obtain ⟨b, hb, -⟩ := hψ
  have hθ' := B.apartment.affineRoots_subset_extendedAffineRoots hθ
  rw [← B.reflectionAffineRoots_eq] at hθ'
  obtain ⟨a, g, hg, hg1, rfl⟩ := hθ'
  obtain ⟨p, hp⟩ := B.hasOppositeFactorPairs a a.property g hg hg1
  rw [hb, ← B.reflectionCoroot_eq_of_isCoroot hg hg1 hp hw]
  exact B.rootForm_reflectionCoroot_integral hg hg1 hp b

/-- Each affine Weyl generator is the original apartment action of an actual normalizer
point. Closure therefore lies in that action's range. -/
theorem affineWeylGroup_le_range :
    AffineRootSystem.affineWeylGroup B.affineRoots ≤ B.apartment.normalizerAffineEquiv.range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro e ⟨ψ, hψ, w, hw, rfl⟩
  have hψ' := B.apartment.affineRoots_subset_extendedAffineRoots hψ
  rw [← B.reflectionAffineRoots_eq] at hψ'
  obtain ⟨a, g, hg, hg1, rfl⟩ := hψ'
  obtain ⟨p, hp⟩ := B.hasOppositeFactorPairs a a.property g hg hg1
  refine ⟨B.reflectionElement hp, ?_⟩
  have heq := B.reflectionCoroot_eq_of_isCoroot hg hg1 hp hw
  simpa only [heq] using B.normalizerAffineEquiv_reflectionElement hg hg1 hp

variable {α : relativeRoots B.i} {u w : rationalPoints G}
    {p q : rationalPoints G × rationalPoints G}

/-- All actual opposite pairs along the same relative root have the same integral coroot. -/
theorem reflectionPair_coroot_eq
    (hu : u ∈ B.rootGroup α) (hu1 : u ≠ 1)
    (hv : w ∈ B.rootGroup α) (hv1 : w ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p)
    (hq : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) w q) :
    hp.coroot B.i B.isMaximalSplitTorus.isSplitSubtorus.1 α.property.1 hu hu1 =
      hq.coroot B.i B.isMaximalSplitTorus.isSplitSubtorus.1 α.property.1 hv hv1 := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  obtain ⟨hp2, hpw⟩ :=
    hp.coroot_spec B.i B.isMaximalSplitTorus.isSplitSubtorus.1 α.property.1 hu hu1
  obtain ⟨hq2, hqw⟩ :=
    hq.coroot_spec B.i B.isMaximalSplitTorus.isSplitSubtorus.1 α.property.1 hv hv1
  exact coroot_eq_of_weylAction B.i B.isMaximalSplitTorus.isSplitSubtorus.1
    (B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i)
    (relativeRootsRestrictedCharactersSpan k G B.isConnectedReductive B.S B.i
      B.isMaximalSplitTorus)
    α.property hp2 hq2 hpw hqw

/-- The correction between actual opposite-pair representatives along one root centralizes
the entire split torus, including its central directions. -/
theorem reflectionElement_inv_mul_mem_centralizer
    (hu : u ∈ B.rootGroup α) (hu1 : u ≠ 1)
    (hv : w ∈ B.rootGroup α) (hv1 : w ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p)
    (hq : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) w q) :
    ((B.reflectionElement hp)⁻¹ * B.reflectionElement hq : normalizerPoints B.i).val ∈
      centralizerPoints B.i := by
  apply (B.isMaximalSplitTorus.isSplitSubtorus.1.weylAction_eq_one_iff B.i _).mp
  have heq : weylAction B.i (B.reflectionElement hp) =
      weylAction B.i (B.reflectionElement hq) := by
    apply LinearEquiv.ext
    intro χ
    unfold reflectionElement
    rw [(hp.coroot_spec B.i B.isMaximalSplitTorus.isSplitSubtorus.1
      α.property.1 hu hu1).2,
      (hq.coroot_spec B.i B.isMaximalSplitTorus.isSplitSubtorus.1
        α.property.1 hv hv1).2,
      B.reflectionPair_coroot_eq hu hu1 hv hv1 hp hq]
  rw [map_mul, map_inv, heq, inv_mul_cancel]

end Langlands.Geometry.Building.IntegerValuationBuildingData
