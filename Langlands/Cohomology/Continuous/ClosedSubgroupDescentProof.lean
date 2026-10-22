import Langlands.Cohomology.Continuous.ClosedSubgroupTopologyProof
import Langlands.Cohomology.Continuous.RestrictionMaps
import Langlands.Cohomology.Continuous.ClosedSubgroupDescentStatement

universe u
open CategoryTheory
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A continuous covariant tuple function is represented by a genuine nested cochain. -/
theorem exists_cochain_of_covariant [CompactSpace G] (A : DiscreteModule k G)
    (q : ℕ) (f : covariantFunctions A.toTopRep (q + 1)) (hf : Continuous f.1) :
    ∃ v : (underlyingContinuousCochains A.toTopRep).X q,
      nestedEval A.toTopRep (q + 1) v.1 = f.1 := by
  obtain ⟨N, F, hF⟩ := exists_covariant_quotient_factor A (q + 1) f hf
  let : DiscreteTopology (G ⧸ N.toSubgroup) :=
    QuotientGroup.discreteTopology_iff.mpr N.isOpen
  let w : (TopRep.homogeneousCochains (finiteQuotientTopRep A N)).X q :=
    ⟨nestedLift (finiteQuotientTopRep A N) (q + 1) F.1,
      nestedLift_covariant (finiteQuotientTopRep A N) (q + 1) F⟩
  refine ⟨(ContinuousCohomology.cochainsMap (quotientProjection N)
    (fixedCoefficientInclusion A N)).f q w, ?_⟩
  funext x
  change nestedEval A.toTopRep (q + 1)
    ((ContinuousCohomology.resolutionMap (quotientProjection N)
      (fixedCoefficientInclusion A N) (q + 1)).hom w.1) x = _
  rw [nestedEval_resolutionMap]
  change (nestedEval (finiteQuotientTopRep A N) (q + 1)
    (nestedLift (finiteQuotientTopRep A N) (q + 1) F.1)
      ((quotientProjection N) ∘ x)).1 = _
  rw [nestedEval_lift]
  exact hF x

/-- On tuple evaluations, actual subgroup restriction is coordinatewise inclusion. -/
theorem nestedEval_restriction (A : DiscreteModule k G) (H : Subgroup G) (q : ℕ)
    (v : (underlyingContinuousCochains A.toTopRep).X q) (x : Fin (q + 1) → H) :
    nestedEval (A.restrict H).toTopRep (q + 1)
      ((continuousRestrictionCochains A H).f q v).1 x =
        nestedEval A.toTopRep (q + 1) v.1 (fun i => (x i : G)) := by
  change nestedEval (A.restrict H).toTopRep (q + 1)
    ((ContinuousCohomology.resolutionMap (subgroupInclusion H)
      (𝟙 (A.restrict H).toTopRep) (q + 1)).hom v.1) x = _
  rw [nestedEval_resolutionMap]
  rfl

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Extending a covariant function first as a function makes covariance valid on an open neighborhood. -/
theorem exists_openNormal_covariant_extension (A : DiscreteModule k G)
    (H : ClosedSubgroup G) [H.toSubgroup.Normal] (n : ℕ)
    (f : covariantFunctions (A.restrict H.toSubgroup).toTopRep n)
    (hf : Continuous f.1) :
    ∃ (U : OpenNormalSubgroup G) (F : C((Fin n → G), A.toTopRep)),
      H.toSubgroup ≤ U.toSubgroup ∧
      (∀ x : Fin n → H, F (fun i => (x i : G)) = f.1 x) ∧
      (∀ (g : G), g ∈ U → ∀ (x : Fin n → G), (∀ i, x i ∈ U) →
        F (fun i => g * x i) = A.toTopRep.ρ g (F x)) := by
  obtain ⟨F, hF⟩ := exists_closedSubgroup_tuple_extension (Y := A.toTopRep) H n ⟨f.1, hf⟩
  let L : C((Fin (n + 1) → G), A.toTopRep) :=
    ⟨fun x => F (fun i => x 0 * x i.succ), F.continuous.comp
      (continuous_pi fun i => (continuous_apply 0).mul (continuous_apply i.succ))⟩
  let R : C((Fin (n + 1) → G), A.toTopRep) :=
    ⟨fun x => A.toTopRep.ρ (x 0) (F (Fin.tail x)), by
      have ht : Continuous (fun x : Fin (n + 1) → G => F (Fin.tail x)) :=
        F.continuous.comp (continuous_pi fun i => continuous_apply i.succ)
      exact A.continuous_action.comp ((continuous_apply 0).prodMk ht)⟩
  have hLR : ∀ x : Fin (n + 1) → H,
      L (fun i => (x i : G)) = R (fun i => (x i : G)) := by
    intro x
    change F (fun i => (x 0 : G) * (x i.succ : G)) =
      A.toTopRep.ρ (x 0 : G) (F (fun i => (x i.succ : G)))
    exact (hF (fun i => x 0 * x i.succ)).trans
      ((f.property (x 0) (Fin.tail x)).trans
        (congrArg (A.toTopRep.ρ (x 0 : G)) (hF (Fin.tail x))).symm)
  obtain ⟨U, hHU, hU⟩ := exists_openNormal_tuple_agreement H (n + 1) L R hLR
  refine ⟨U, F, hHU, hF, ?_⟩
  intro g hg x hx
  have hm : ∀ i : Fin (n + 1), (Fin.cons g x : Fin (n + 1) → G) i ∈ U := by
    intro i
    exact Fin.cases hg hx i
  simpa only [L, R, ContinuousMap.coe_mk, Fin.cons_zero, Fin.cons_succ,
    Fin.tail_cons] using hU (Fin.cons g x) hm

end Langlands.Continuous

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Evaluate the differential in the underlying continuous cochain complex. -/
theorem nestedEval_cochain_d (A : DiscreteModule k G) (q : ℕ)
    (b : (underlyingContinuousCochains A.toTopRep).X q)
    (x : Fin (q + 1 + 1) → G) :
    nestedEval A.toTopRep (q + 1 + 1)
      (((underlyingContinuousCochains A.toTopRep).d q (q + 1)) b).1 x =
      ∑ i : Fin (q + 1 + 1), (-1 : k) ^ i.val •
        nestedEval A.toTopRep (q + 1) b.1 (x ∘ i.succAbove) := by
  change nestedEval A.toTopRep (q + 1 + 1)
    (((TopRep.homogeneousCochains A.toTopRep).d q (q + 1)) b).1 x = _
  rw [TopRep.homogeneousCochains.d_apply]
  exact nestedEval_d A.toTopRep (q + 1) b.1 x

variable [CompactSpace G] [TotallyDisconnectedSpace G]

omit [TotallyDisconnectedSpace G] in
/-- A cochain which vanishes on a closed normal subgroup vanishes on a neighborhood. -/
theorem exists_openNormal_restriction_cochain_zero (A : DiscreteModule k G)
    (H : ClosedSubgroup G) [H.toSubgroup.Normal] (q : ℕ)
    (c : (underlyingContinuousCochains A.toTopRep).X q)
    (hc : (continuousRestrictionCochains A H.toSubgroup).f q c = 0) :
    ∃ U : OpenNormalSubgroup G, H.toSubgroup ≤ U.toSubgroup ∧
      (continuousRestrictionCochains A U.toSubgroup).f q c = 0 := by
  let C : C((Fin (q + 1) → G), A.toTopRep) :=
    ⟨nestedEval A.toTopRep (q + 1) c.1,
      (continuous_nestedEval A.toTopRep (q + 1)).comp
        (continuous_const.prodMk continuous_id)⟩
  have hC : ∀ x : Fin (q + 1) → H, C (fun i => (x i : G)) = 0 := by
    intro x
    change nestedEval A.toTopRep (q + 1) c.1 (fun i => (x i : G)) = 0
    rw [← nestedEval_restriction A H.toSubgroup q c x, hc]
    simp
  obtain ⟨U, hHU, hU⟩ := exists_openNormal_tuple_agreement H (q + 1) C 0 hC
  refine ⟨U, hHU, ?_⟩
  apply Subtype.ext
  apply nestedEval_injective (A.restrict U.toSubgroup).toTopRep (q + 1)
  funext x
  rw [nestedEval_restriction]
  simpa only [C, ContinuousMap.coe_mk, ZeroMemClass.coe_zero, map_zero, Pi.zero_apply,
    ContinuousMap.zero_apply] using hU (fun i => (x i : G)) (fun i => (x i).2)

/-- A primitive on a closed normal subgroup extends to a primitive on a neighborhood. -/
theorem exists_openNormal_restriction_boundary (A : DiscreteModule k G)
    (H : ClosedSubgroup G) [H.toSubgroup.Normal] (q : ℕ)
    (c : (underlyingContinuousCochains A.toTopRep).X (q + 1))
    (b : (underlyingContinuousCochains (A.restrict H.toSubgroup).toTopRep).X q)
    (hb : (underlyingContinuousCochains (A.restrict H.toSubgroup).toTopRep).d q (q + 1) b =
      (continuousRestrictionCochains A H.toSubgroup).f (q + 1) c) :
    ∃ U : OpenNormalSubgroup G, H.toSubgroup ≤ U.toSubgroup ∧
      ∃ w : (underlyingContinuousCochains (A.restrict U.toSubgroup).toTopRep).X q,
        (underlyingContinuousCochains (A.restrict U.toSubgroup).toTopRep).d q (q + 1) w =
          (continuousRestrictionCochains A U.toSubgroup).f (q + 1) c := by
  classical
  let : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  let : CompactSpace H.toSubgroup := inferInstanceAs (CompactSpace H)
  let f : covariantFunctions (A.restrict H.toSubgroup).toTopRep (q + 1) :=
    ⟨nestedEval (A.restrict H.toSubgroup).toTopRep (q + 1) b.1,
      nestedEval_invariant (A.restrict H.toSubgroup).toTopRep (q + 1) b⟩
  have hf : Continuous f.1 :=
    (continuous_nestedEval (A.restrict H.toSubgroup).toTopRep (q + 1)).comp
      (continuous_const.prodMk continuous_id)
  obtain ⟨U, F, hHU, hF, hcov⟩ := exists_openNormal_covariant_extension A H (q + 1) f hf
  let D : C((Fin (q + 1 + 1) → G), A.toTopRep) :=
    ⟨fun x => ∑ i : Fin (q + 1 + 1), (-1 : k) ^ i.val • F (x ∘ i.succAbove), by
      apply continuous_finsetSum
      intro i _
      exact (F.continuous.comp (continuous_pi fun j =>
        continuous_apply (i.succAbove j))).const_smul _⟩
  let C : C((Fin (q + 1 + 1) → G), A.toTopRep) :=
    ⟨nestedEval A.toTopRep (q + 1 + 1) c.1,
      (continuous_nestedEval A.toTopRep (q + 1 + 1)).comp
        (continuous_const.prodMk continuous_id)⟩
  have hDC : ∀ x : Fin (q + 1 + 1) → H,
      D (fun i => (x i : G)) = C (fun i => (x i : G)) := by
    intro x
    have h := congrArg (fun v : (underlyingContinuousCochains
      (A.restrict H.toSubgroup).toTopRep).X (q + 1) =>
        nestedEval (A.restrict H.toSubgroup).toTopRep (q + 1 + 1) v.1 x) hb
    rw [nestedEval_cochain_d, nestedEval_restriction] at h
    change (∑ i : Fin (q + 1 + 1), (-1 : k) ^ i.val •
      F ((fun j => (x j : G)) ∘ i.succAbove)) =
        nestedEval A.toTopRep (q + 1 + 1) c.1 (fun i => (x i : G))
    rw [← h]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun y => (-1 : k) ^ i.val • y) (hF (x ∘ i.succAbove))
  obtain ⟨V, hHV, hV⟩ := exists_openNormal_tuple_agreement H (q + 1 + 1) D C hDC
  let W := U ⊓ V
  let : CompactSpace W.toSubgroup :=
    isCompact_iff_compactSpace.mp W.toOpenSubgroup.isClosed.isCompact
  let fw : covariantFunctions (A.restrict W.toSubgroup).toTopRep (q + 1) :=
    ⟨fun x => F (fun i => (x i : G)), by
      intro g x
      exact hcov (g : G) g.2.1 (fun i => (x i : G)) (fun i => (x i).2.1)⟩
  have hfw : Continuous fw.1 :=
    F.continuous.comp (continuous_pi fun i =>
      continuous_subtype_val.comp (continuous_apply i))
  obtain ⟨w, hw⟩ := exists_cochain_of_covariant (A.restrict W.toSubgroup) q fw hfw
  refine ⟨W, le_inf hHU hHV, w, ?_⟩
  apply Subtype.ext
  apply nestedEval_injective (A.restrict W.toSubgroup).toTopRep (q + 1 + 1)
  funext x
  rw [nestedEval_cochain_d, nestedEval_restriction]
  calc
    (∑ i : Fin (q + 1 + 1), (-1 : k) ^ i.val •
      nestedEval (A.restrict W.toSubgroup).toTopRep (q + 1) w.1 (x ∘ i.succAbove)) =
        D (fun i => (x i : G)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact congrArg (fun y => (-1 : k) ^ i.val • y) (congrFun hw (x ∘ i.succAbove))
    _ = C (fun i => (x i : G)) := hV (fun i => (x i : G)) (fun i => (x i).2.2)
    _ = _ := rfl

end Langlands.Continuous

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Boundary descent for the actual short complexes, including degree zero. -/
theorem exists_openNormal_restriction_boundary_sc (A : DiscreteModule k G)
    (H : ClosedSubgroup G) [H.toSubgroup.Normal] (q : ℕ)
    (c : (underlyingContinuousCochains A.toTopRep).X q)
    (hb : ∃ b : ((underlyingContinuousCochains (A.restrict H.toSubgroup).toTopRep).sc q).X₁,
      ((underlyingContinuousCochains (A.restrict H.toSubgroup).toTopRep).sc q).f b =
        (continuousRestrictionCochains A H.toSubgroup).f q c) :
    ∃ U : OpenNormalSubgroup G, H.toSubgroup ≤ U.toSubgroup ∧
      ∃ w : ((underlyingContinuousCochains (A.restrict U.toSubgroup).toTopRep).sc q).X₁,
        ((underlyingContinuousCochains (A.restrict U.toSubgroup).toTopRep).sc q).f w =
          (continuousRestrictionCochains A U.toSubgroup).f q c := by
  cases q with
  | zero =>
    obtain ⟨b, hb⟩ := hb
    have hd : ((underlyingContinuousCochains
        (A.restrict H.toSubgroup).toTopRep).sc 0).f = 0 := by
      change (underlyingContinuousCochains (A.restrict H.toSubgroup).toTopRep).dTo 0 = 0
      apply HomologicalComplex.dTo_eq_zero
      simp [CochainComplex.prev_nat_zero, ComplexShape.up_Rel]
    have hc : (continuousRestrictionCochains A H.toSubgroup).f 0 c = 0 := by
      rw [hd] at hb
      exact hb.symm
    obtain ⟨U, hHU, hU⟩ := exists_openNormal_restriction_cochain_zero A H 0 c hc
    refine ⟨U, hHU, 0, ?_⟩
    rw [map_zero, hU]
  | succ q =>
    change ∃ b : (underlyingContinuousCochains
      (A.restrict H.toSubgroup).toTopRep).X ((ComplexShape.up ℕ).prev (q + 1)),
      (underlyingContinuousCochains (A.restrict H.toSubgroup).toTopRep).d
        ((ComplexShape.up ℕ).prev (q + 1)) (q + 1) b =
          (continuousRestrictionCochains A H.toSubgroup).f (q + 1) c at hb
    rw [CochainComplex.prev_nat_succ] at hb
    obtain ⟨b, hb⟩ := hb
    obtain ⟨U, hHU, w, hw⟩ := exists_openNormal_restriction_boundary A H q c b hb
    refine ⟨U, hHU, ?_⟩
    change ∃ w : (underlyingContinuousCochains
      (A.restrict U.toSubgroup).toTopRep).X ((ComplexShape.up ℕ).prev (q + 1)),
      (underlyingContinuousCochains (A.restrict U.toSubgroup).toTopRep).d
        ((ComplexShape.up ℕ).prev (q + 1)) (q + 1) w =
          (continuousRestrictionCochains A U.toSubgroup).f (q + 1) c
    rw [CochainComplex.prev_nat_succ]
    exact ⟨w, hw⟩

/-- Restriction zero is detected on a neighborhood in the underlying module homology. -/
theorem exists_openNormal_restriction_homology_zero (A : DiscreteModule k G)
    (H : ClosedSubgroup G) [H.toSubgroup.Normal] (q : ℕ)
    (x : (underlyingContinuousCochains A.toTopRep).homology q)
    (hx : HomologicalComplex.homologyMap (continuousRestrictionCochains A H.toSubgroup) q x = 0) :
    ∃ U : OpenNormalSubgroup G, H.toSubgroup ≤ U.toSubgroup ∧
      HomologicalComplex.homologyMap (continuousRestrictionCochains A U.toSubgroup) q x = 0 := by
  let S := (underlyingContinuousCochains A.toTopRep).sc q
  let T (K : Subgroup G) := (underlyingContinuousCochains (A.restrict K).toTopRep).sc q
  let φ (K : Subgroup G) : S ⟶ T K :=
    (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) q).map
      (continuousRestrictionCochains A K)
  obtain ⟨c, hc, rfl⟩ := moduleCycleClass_surjective S x
  have hcycle (K : Subgroup G) : (T K).g ((φ K).τ₂ c) = 0 := by
    have h := ConcreteCategory.congr_hom (φ K).comm₂₃ c
    change (T K).g ((φ K).τ₂ c) = (φ K).τ₃ (S.g c) at h
    simpa only [hc, map_zero] using h
  change ShortComplex.homologyMap (φ H.toSubgroup) (moduleCycleClass S c hc) = 0 at hx
  rw [moduleCycleClass_naturality (φ H.toSubgroup) c hc (hcycle H.toSubgroup)] at hx
  obtain ⟨U, hHU, hb⟩ := exists_openNormal_restriction_boundary_sc A H q c
    ((moduleCycleClass_eq_zero_iff (T H.toSubgroup) _ (hcycle H.toSubgroup)).mp hx)
  refine ⟨U, hHU, ?_⟩
  change ShortComplex.homologyMap (φ U.toSubgroup) (moduleCycleClass S c hc) = 0
  rw [moduleCycleClass_naturality (φ U.toSubgroup) c hc (hcycle U.toSubgroup)]
  exact (moduleCycleClass_eq_zero_iff (T U.toSubgroup) _ (hcycle U.toSubgroup)).mpr hb

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- Forgetting topology commutes with actual restriction on cohomology. -/
theorem continuousRestriction_homology_comparison (A : DiscreteModule k G)
    (H : Subgroup G) (q : ℕ) (x : continuousCohomology q A.toTopRep) :
    (((TopRep.homogeneousCochains (A.restrict H).toTopRep).sc q).mapHomologyIso
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).inv
        (continuousRestriction A H q x) =
      HomologicalComplex.homologyMap (continuousRestrictionCochains A H) q
        ((((TopRep.homogeneousCochains A.toTopRep).sc q).mapHomologyIso
          (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).inv x) := by
  have h := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (TopModuleCat.{u} k) (ComplexShape.up ℕ) q).map
      (ContinuousCohomology.cochainsMap (subgroupInclusion H) (𝟙 (A.restrict H).toTopRep)))
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))
  exact ConcreteCategory.congr_hom h x

/-- Actual continuous restriction zero is detected on an open normal supergroup. -/
theorem exists_openNormal_continuousRestriction_zero (A : DiscreteModule k G)
    (H : ClosedSubgroup G) [H.toSubgroup.Normal] (q : ℕ)
    (x : continuousCohomology q A.toTopRep)
    (hx : continuousRestriction A H.toSubgroup q x = 0) :
    ∃ U : OpenNormalSubgroup G, H.toSubgroup ≤ U.toSubgroup ∧
      continuousRestriction A U.toSubgroup q x = 0 := by
  let e := ((TopRep.homogeneousCochains A.toTopRep).sc q).mapHomologyIso
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))
  have hz : HomologicalComplex.homologyMap (continuousRestrictionCochains A H.toSubgroup) q
      (e.inv x) = 0 := by
    rw [← continuousRestriction_homology_comparison, hx, map_zero]
  obtain ⟨U, hHU, hU⟩ := exists_openNormal_restriction_homology_zero A H q (e.inv x) hz
  refine ⟨U, hHU, ?_⟩
  let eU := ((TopRep.homogeneousCochains (A.restrict U.toSubgroup).toTopRep).sc q).mapHomologyIso
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))
  apply (ModuleCat.mono_iff_injective eU.inv).mp inferInstance
  rw [map_zero]
  exact (continuousRestriction_homology_comparison A U.toSubgroup q x).trans hU

/-- The exact published all-degree closed-normal restriction zero-detection proposition. -/
theorem closedNormalRestrictionZeroDetection : ClosedNormalRestrictionZeroDetection.{u} := by
  intro k G _ _ _ _ _ _ _ _ A H _ q x hx
  exact exists_openNormal_continuousRestriction_zero A H q x hx

end Langlands.Continuous
