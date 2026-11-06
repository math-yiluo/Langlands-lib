import Langlands.Geometry.Building.PositiveRootConeDepth
import Langlands.Geometry.Building.RootValuationFieldRestriction

/-! # Actual positive-cone depths under field extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : S.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "a_K" a => characterLattice.baseChange b S a

/-- Extend an additive real depth through the inverse actual character pullback. -/
def fieldExtendedAdditiveDepth (hS : IsSplitTorus S.toGrp)
    (f : characterLattice S →+ ℝ) : characterLattice S_K →+ ℝ :=
  f.comp (characterLattice.baseChangeEquiv b S hS).symm.toAddMonoidHom

@[simp] theorem fieldExtendedAdditiveDepth_apply (hS : IsSplitTorus S.toGrp)
    (f : characterLattice S →+ ℝ) (a : characterLattice S) :
    fieldExtendedAdditiveDepth (K := K) hS f (a_K a) = f a :=
  congrArg f ((characterLattice.baseChangeEquiv b S hS).symm_apply_apply a)

variable [IsAffineHom G.X.hom] [Smooth G.X.hom] [Mono i.hom.hom.left]

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance extendedMono : Mono (i_K).hom.hom.left := by
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  change Mono ((Over.pullback b).map i.hom.hom).left
  infer_instance

omit [Mono i.hom.hom.left] in
/-- The literal original cone is the character preimage of the actual extended cone. -/
theorem positiveIntegralRootCone_fieldExtend_preimage
    (hS : IsSplitTorus S.toGrp) (a a' : characterLattice S) :
    (characterLattice.baseChange b S) ⁻¹'
        positiveIntegralRootCone (S := S_K) i_K (a_K a) (a_K a') =
      positiveIntegralRootCone i a a' := by
  ext c
  change ((a_K c) ∈ relativeRoots (T := S_K) i_K ∧
      ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (a_K c) = p • (a_K a) + q • (a_K a')) ↔ _
  constructor
  · rintro ⟨hc, p, q, hp, hq, heq⟩
    refine ⟨(mem_roots_baseChange_iff (K := K) G S hS i c).mp hc, p, q, hp, hq, ?_⟩
    apply (characterLattice.baseChangeEquiv b S hS).injective
    simpa only [characterLattice.baseChangeEquiv_apply, map_add, map_nsmul] using heq
  · rintro ⟨hc, p, q, hp, hq, rfl⟩
    exact ⟨(mem_roots_baseChange_iff (K := K) G S hS i _).mpr hc,
      p, q, hp, hq, by rw [map_add, map_nsmul, map_nsmul]⟩

/-- Additive cone-depth generation is reflected using collection only upstairs. -/
theorem mem_positiveConeGenerated_fieldExtend_iff
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    (ν : cocharacterLattice S) (a a' : characterLattice S)
    (ha : 0 < latticePairing S a ν) (ha' : 0 < latticePairing S a' ν)
    {ψ : RootFunctionFamily S_K G_K} (hψ : IsRootDatumValuation (S := S_K) i_K ψ)
    (f : characterLattice S →+ ℝ) (g : rationalPoints G) :
    rationalExtend k K G g ∈ rootDepthGeneratedSubgroup (S := S_K) i_K ψ
        (positiveIntegralRootCone (S := S_K) i_K (a_K a) (a_K a'))
        (fieldExtendedAdditiveDepth (K := K) hS f) ↔
      g ∈ rootDepthGeneratedSubgroup i (RootFunctionFamily.fieldRestrict (k := k) ψ)
        (positiveIntegralRootCone i a a') f := by
  classical
  obtain ⟨n, c, hinj, hc⟩ := RelativeRoot.exists_fin_enumeration_indivisiblePositiveRoots
    i ν (hS.finite_relativeRoots i)
  have hapos : 0 < latticePairing S_K (a_K a) (cocharacterLattice.baseChange b S ν) := by
    rwa [latticePairing_baseChange]
  have ha'pos : 0 < latticePairing S_K (a_K a') (cocharacterLattice.baseChange b S ν) := by
    rwa [latticePairing_baseChange]
  have hcover : ∀ d ∈ positiveIntegralRootCone (S := S_K) i_K (a_K a) (a_K a'),
      ∃ j, d = (a_K (c j)) ∨ d = 2 • (a_K (c j)) := by
    intro d hd
    obtain ⟨e, rfl⟩ := (characterLattice.baseChangeEquiv b S hS).surjective d
    change (a_K e) ∈ _ at hd
    have he : e ∈ positiveIntegralRootCone i a a' := by
      rw [← positiveIntegralRootCone_fieldExtend_preimage (K := K) i hS a a']
      exact hd
    obtain ⟨j, hj | hj⟩ := hE.positive_subset_primitive_double_cover i hS ν c hc
      (positiveIntegralRootCone_positive i ν ha ha') e he
    · exact ⟨j, Or.inl (congrArg (characterLattice.baseChange b S) hj)⟩
    · exact ⟨j, Or.inr (by
        simpa only [characterLattice.baseChangeEquiv_apply, map_nsmul] using
          congrArg (characterLattice.baseChange b S) hj)⟩
  have h := mem_rootDepthGeneratedSubgroup_fieldExtend_iff i hS hE ν c hinj hc hψ
    (positiveIntegralRootCone_closedDepth (S := S_K) i_K _ hapos ha'pos
      (fieldExtendedAdditiveDepth (K := K) hS f))
    (fun d _ _ => (additiveDepth_double _ d).le) hcover g
  have hf : ((fieldExtendedAdditiveDepth (K := K) hS f : characterLattice S_K → ℝ) ∘
      characterLattice.baseChange b S) = f := by
    funext d
    exact fieldExtendedAdditiveDepth_apply hS f d
  rw [positiveIntegralRootCone_fieldExtend_preimage i hS a a', hf] at h
  exact h

omit [Smooth G.X.hom] [Mono i.hom.hom.left] in
/-- Only depths at actual output roots are needed to identify the V3 union.
In particular the two input values need not be prescribed. -/
theorem rootDepthGeneratedSubgroup_positiveCone_of_outputDepth
    (φ : RootFunctionFamily S G) (a a' : characterLattice S)
    (r s : ℝ) (f : characterLattice S →+ ℝ)
    (hf : ∀ p q : ℕ, 0 < p → 0 < q → p • a + q • a' ∈ relativeRoots i →
      f (p • a + q • a') = p * r + q * s) :
    rootDepthGeneratedSubgroup i φ (positiveIntegralRootCone i a a') f =
      Subgroup.closure (⋃ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • a' ∈ relativeRoots i),
        rootFiltration i φ (p • a + q • a') (p * r + q * s)) := by
  unfold rootDepthGeneratedSubgroup
  congr 1
  ext g
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨⟨c, hc, p, q, hp, hq, rfl⟩, hg⟩
    exact ⟨p, q, hp, hq, hc, by simpa only [hf p q hp hq hc] using hg⟩
  · rintro ⟨p, q, hp, hq, hc, hg⟩
    exact ⟨⟨p • a + q • a', hc, p, q, hp, hq, rfl⟩,
      by simpa only [hf p q hp hq hc] using hg⟩

/-- The literal restricted V3 bound descends when one additive depth agrees
with the required depths at every actual output root. -/
theorem fieldRestrict_commutator_of_outputDepth
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    (ν : cocharacterLattice S) (a a' : characterLattice S)
    (ha : a ∈ relativeRoots i) (ha' : a' ∈ relativeRoots i)
    (hapos : 0 < latticePairing S a ν) (ha'pos : 0 < latticePairing S a' ν)
    {ψ : RootFunctionFamily S_K G_K} (hψ : IsRootDatumValuation (S := S_K) i_K ψ)
    (r s : ℝ) (f : characterLattice S →+ ℝ)
    (hf : ∀ p q : ℕ, 0 < p → 0 < q → p • a + q • a' ∈ relativeRoots i →
      f (p • a + q • a') = p * r + q * s) :
    ⁅Subgroup.closure (rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) ψ) a r),
      Subgroup.closure (rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) ψ) a' s)⁆ ≤
      Subgroup.closure (⋃ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • a' ∈ relativeRoots i),
        rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) ψ)
          (p • a + q • a') (p * r + q * s)) := by
  let fK := fieldExtendedAdditiveDepth (K := K) hS f
  have hroot (c : characterLattice S) (hc : c ∈ relativeRoots i) :
      (a_K c) ∈ relativeRoots (T := S_K) i_K :=
    (mem_roots_baseChange_iff (K := K) G S hS i c).mpr hc
  have hinput (c : characterLattice S) (hc : c ∈ relativeRoots i) (t : ℝ) :
      Subgroup.closure (rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) ψ) c t) ≤
        (Subgroup.closure (rootFiltration (S := S_K) i_K ψ (a_K c) t)).comap
          (rationalExtend k K G) := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    apply Subgroup.subset_closure
    exact (Set.ext_iff.mp (rootFiltration_fieldRestrict i hS ψ c hc.1 t) g).mp hg
  have haposK : 0 < latticePairing S_K (a_K a) (cocharacterLattice.baseChange b S ν) := by
    rwa [latticePairing_baseChange]
  have ha'posK : 0 < latticePairing S_K (a_K a') (cocharacterLattice.baseChange b S ν) := by
    rwa [latticePairing_baseChange]
  have hfK : ∀ p q : ℕ, 0 < p → 0 < q →
      p • (a_K a) + q • (a_K a') ∈ relativeRoots (T := S_K) i_K →
      fK (p • (a_K a) + q • (a_K a')) = p * r + q * s := by
    intro p q hp hq hc
    have hc' : p • a + q • a' ∈ relativeRoots i :=
      (mem_roots_baseChange_iff (K := K) G S hS i _).mp
        (by simpa only [map_add, map_nsmul, relativeRoots] using hc)
    change fieldExtendedAdditiveDepth (K := K) hS f _ = _
    rw [← map_nsmul, ← map_nsmul, ← map_add, fieldExtendedAdditiveDepth_apply]
    exact hf p q hp hq hc'
  have hup := hψ.commutator (a_K a) (hroot a ha) (a_K a') (hroot a' ha')
    (KPApartmentData.positiveRoots_nonopposite (cocharacterLattice.baseChange b S ν)
      ⟨hroot a ha, haposK⟩ ⟨hroot a' ha', ha'posK⟩) r s
  rw [← rootDepthGeneratedSubgroup_positiveCone_of_outputDepth (S := S_K) i_K ψ
    (a_K a) (a_K a') r s fK hfK] at hup
  rw [← rootDepthGeneratedSubgroup_positiveCone_of_outputDepth i
    (RootFunctionFamily.fieldRestrict (k := k) ψ) a a' r s f hf]
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  apply (mem_positiveConeGenerated_fieldExtend_iff i hS hE ν a a' hapos ha'pos hψ f _).mp
  apply hup
  rw [map_commutatorElement]
  exact Subgroup.commutator_mem_commutator (hinput a ha r hx) (hinput a' ha' s hy)

end Langlands.Geometry.Building
