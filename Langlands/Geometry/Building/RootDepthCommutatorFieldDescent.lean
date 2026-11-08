import Langlands.Geometry.Building.RootDepthFieldDescent
import Langlands.Geometry.Building.RootValuationFieldDescent

/-! # Commutator descent from actual depth-collection data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace RootDepthCollectionData

section OverField

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} [IsAffineHom G.X.hom]
  {φ : RootFunctionFamily S G} (D : RootDepthCollectionData i φ)

include D

/-- The supplied subgroup V3 is the literal root-filtration closure V3. -/
theorem commutator_le_closure
    (a : characterLattice S) (ha : a ∈ relativeRoots i)
    (a' : characterLattice S) (ha' : a' ∈ relativeRoots i)
    (hnon : ∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] a' : Vstar S) ≠
      -(t • (1 : ℝ) ⊗ₜ[ℤ] a)) (r s : ℝ) :
    ⁅Subgroup.closure (rootFiltration i φ a r),
      Subgroup.closure (rootFiltration i φ a' s)⁆ ≤
      Subgroup.closure (⋃ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • a' ∈ relativeRoots i),
        rootFiltration i φ (p • a + q • a') (p * r + q * s)) := by
  simpa only [← D.coe_subgroup, Subgroup.closure_iUnion, Subgroup.closure_eq] using
    D.commutator_le a ha a' ha' hnon r s

end OverField

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "a_K" a => characterLattice.baseChange b S a

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance extendedMono : Mono (i_K).hom.hom.left := by
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  change Mono ((Over.pullback b).map i.hom.hom).left
  infer_instance

omit [Smooth G.X.hom] [Mono i.hom.hom.left] in
/-- The actual subgroup preimage at the original character and real depth. -/
def fieldRestrictedFiltrationSubgroup
    {ψ : RootFunctionFamily (k := K) S_K G_K}
    (D : RootDepthCollectionData (k := K) (S := S_K) (G := G_K) i_K ψ)
    (a : characterLattice S) (r : ℝ) : Subgroup (rationalPoints G) :=
  (D.subgroup (a_K a) r).comap (rationalExtend k K G)

omit [Mono i.hom.hom.left] in
/-- At every nonzero character this is exactly the literal restricted filtration. -/
theorem coe_fieldRestrictedFiltrationSubgroup
    {ψ : RootFunctionFamily (k := K) S_K G_K}
    (D : RootDepthCollectionData (k := K) (S := S_K) (G := G_K) i_K ψ)
    (hS : IsSplitTorus S.toGrp) (a : characterLattice S) (ha : a ≠ 0) (r : ℝ) :
    (D.fieldRestrictedFiltrationSubgroup (k := k) (K := K) i a r : Set (rationalPoints G)) =
      rootFiltration i (RootFunctionFamily.fieldRestrict
        (k := k) (K := K) (S := S) (G := G) ψ) a r := by
  ext g
  change rationalExtend k K G g ∈ (D.subgroup (a_K a) r : Set (rationalPoints G_K)) ↔ _
  rw [D.coe_subgroup, rootFiltration_fieldRestrict i hS ψ a ha r]
  rfl

/-- Additive cone-depth generation is reflected using collection only upstairs. -/
theorem mem_positiveConeGenerated_fieldExtend_iff
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    (ν : cocharacterLattice S) (a a' : characterLattice S)
    (ha : 0 < latticePairing S a ν) (ha' : 0 < latticePairing S a' ν)
    {ψ : RootFunctionFamily (k := K) S_K G_K} (D : RootDepthCollectionData (k := K) (S := S_K) (G := G_K) i_K ψ)
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
  have h := D.mem_generated_fieldExtend_iff (k := k) (K := K) i hS hE ν c hinj hc
    (positiveIntegralRootCone_closedDepth (S := S_K) i_K _ hapos ha'pos
      (fieldExtendedAdditiveDepth (K := K) hS f))
    (fun d _ _ => (additiveDepth_double _ d).le) hcover g
  change rationalExtend k K G g ∈ rootDepthGeneratedSubgroup (S := S_K) i_K ψ
      (positiveIntegralRootCone (S := S_K) i_K (a_K a) (a_K a'))
      (fieldExtendedAdditiveDepth (K := K) hS f) ↔
    g ∈ rootDepthGeneratedSubgroup i
      (RootFunctionFamily.fieldRestrict (k := k) (K := K) (S := S) (G := G) ψ)
      ((characterLattice.baseChange b S) ⁻¹'
        positiveIntegralRootCone (S := S_K) i_K (a_K a) (a_K a'))
      ((fieldExtendedAdditiveDepth (K := K) hS f : characterLattice S_K → ℝ) ∘
        characterLattice.baseChange b S) at h
  have hf : ((fieldExtendedAdditiveDepth (K := K) hS f : characterLattice S_K → ℝ) ∘
      characterLattice.baseChange b S) = f := by
    funext d
    exact fieldExtendedAdditiveDepth_apply hS f d
  rw [positiveIntegralRootCone_fieldExtend_preimage i hS a a', hf] at h
  exact h

/-- The literal restricted V3 bound descends when one additive depth agrees
with the required depths at every actual output root. -/
theorem fieldRestrict_commutator_of_outputDepth
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    (ν : cocharacterLattice S) (a a' : characterLattice S)
    (ha : a ∈ relativeRoots i) (ha' : a' ∈ relativeRoots i)
    (hapos : 0 < latticePairing S a ν) (ha'pos : 0 < latticePairing S a' ν)
    {ψ : RootFunctionFamily (k := K) S_K G_K}
    (D : RootDepthCollectionData (k := K) (S := S_K) (G := G_K) i_K ψ)
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
  have hup := D.commutator_le_closure (a_K a) (hroot a ha) (a_K a') (hroot a' ha')
    (KPApartmentData.positiveRoots_nonopposite (cocharacterLattice.baseChange b S ν)
      ⟨hroot a ha, haposK⟩ ⟨hroot a' ha', ha'posK⟩) r s
  rw [← rootDepthGeneratedSubgroup_positiveCone_of_outputDepth (S := S_K) i_K ψ
    (a_K a) (a_K a') r s fK hfK] at hup
  rw [← rootDepthGeneratedSubgroup_positiveCone_of_outputDepth i
    (RootFunctionFamily.fieldRestrict (k := k) ψ) a a' r s f hf]
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  apply (mem_positiveConeGenerated_fieldExtend_iff i hS hE ν a a' hapos ha'pos D f _).mp
  apply hup
  rw [map_commutatorElement]
  exact Subgroup.commutator_mem_commutator (hinput a ha r hx) (hinput a' ha' s hy)

/-- Original opposite factor pairs discharge the positivity and output-depth
choices, giving V3 for every nonopposite pair and arbitrary real depths. -/
theorem fieldRestrict_commutator
    (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
    {ψ : RootFunctionFamily (k := K) S_K G_K}
    (D : RootDepthCollectionData (k := K) (S := S_K) (G := G_K) i_K ψ)
    (a : characterLattice S) (ha : a ∈ relativeRoots i)
    (a' : characterLattice S) (ha' : a' ∈ relativeRoots i)
    (hnon : ∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] a' : Vstar S) ≠
      -(t • (1 : ℝ) ⊗ₜ[ℤ] a)) (r s : ℝ) :
    ⁅Subgroup.closure (rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) ψ) a r),
      Subgroup.closure (rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) ψ) a' s)⁆ ≤
      Subgroup.closure (⋃ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • a' ∈ relativeRoots i),
        rootFiltration i (RootFunctionFamily.fieldRestrict (k := k) ψ)
          (p • a + q • a') (p * r + q * s)) := by
  obtain ⟨ν, hapos, ha'pos⟩ :=
    hS.exists_cocharacter_pos_pair_of_not_opposite a a' ha.1 ha'.1 hnon
  obtain ⟨f, hf⟩ := exists_additive_outputDepth i hS hE ha ha' hnon r s
  exact fieldRestrict_commutator_of_outputDepth i hS hE ν a a' ha ha'
    hapos ha'pos D r s f hf

end RootDepthCollectionData

end Langlands.Geometry.Building
