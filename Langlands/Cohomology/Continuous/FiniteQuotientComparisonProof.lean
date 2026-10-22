import Langlands.Cohomology.Continuous.FiniteQuotientComparisonStatement
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Evaluation of nested continuous functions is jointly continuous on finite tuples. -/
theorem continuous_nestedEval [LocallyCompactSpace G] (A : TopRep.{u} k G) (n : ℕ) :
    Continuous (fun p : TopRep.resolutionX A n × (Fin n → G) => nestedEval A n p.1 p.2) := by
  induction n with
  | zero => exact continuous_fst
  | succ n ih =>
    change Continuous (fun p : C(G, TopRep.resolutionX A n) × (Fin (n + 1) → G) =>
      nestedEval A n (p.1 (p.2 0)) (Fin.tail p.2))
    exact ih.comp ((continuous_eval.comp
      (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))).prodMk
        (continuous_pi fun i => (continuous_apply i.succ).comp continuous_snd))



section Shift

variable {X Y : Type u} [Group X]

/-- Right translations fixing a function form a genuine subgroup. -/
def rightShiftStabilizer (f : X → Y) : Subgroup X where
  carrier := {g | ∀ x, f (x * g) = f x}
  one_mem' := by intro x; rw [mul_one]
  mul_mem' := by
    intro g h hg hh x
    rw [← mul_assoc, hh (x * g), hg x]
  inv_mem' := by
    intro g hg x
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using (hg (x * g⁻¹)).symm

variable [TopologicalSpace X] [IsTopologicalGroup X] [CompactSpace X]
  [TopologicalSpace Y] [DiscreteTopology Y]

/-- Compactness makes the right translation stabilizer of a discrete-valued continuous map open. -/
theorem isOpen_rightShiftStabilizer (f : X → Y) (hf : Continuous f) :
    IsOpen (rightShiftStabilizer f : Set X) := by
  have hopen : IsOpen {p : X × X | f (p.2 * p.1) = f p.2} :=
    (isOpen_discrete {p : Y × Y | p.1 = p.2}).preimage
      ((hf.comp (continuous_snd.mul continuous_fst)).prodMk (hf.comp continuous_snd))
  convert (isClosedMap_fst_of_compactSpace _ hopen.isClosed_compl).isOpen_compl using 1
  ext g
  simp [rightShiftStabilizer, Set.mem_image, Prod.exists]

/-- A continuous map from a compact group to a discrete space is constant on cosets of
some open normal subgroup. -/
theorem exists_openNormal_right_invariant (f : X → Y) (hf : Continuous f) :
    ∃ N : OpenNormalSubgroup X, ∀ g ∈ N, ∀ x, f (x * g) = f x := by
  let U : OpenSubgroup X :=
    { toSubgroup := rightShiftStabilizer f
      isOpen' := isOpen_rightShiftStabilizer f hf }
  have : Finite (X ⧸ U.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen
  have : Subgroup.FiniteIndex U.toSubgroup := U.finiteIndex_of_finite_quotient
  let N : OpenNormalSubgroup X :=
    { toSubgroup := Subgroup.normalCore U.toSubgroup
      isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _
        (U.normalCore_isClosed U.isClosed) }
  refine ⟨N, ?_⟩
  intro g hg x
  exact (U.normalCore_le hg) x

end Shift

omit [IsTopologicalGroup G] in
/-- An open normal subgroup of a finite power contains the power of one common open normal subgroup. -/
theorem exists_common_openNormal (n : ℕ) (K : OpenNormalSubgroup (Fin n → G)) :
    ∃ N : OpenNormalSubgroup G, ∀ x : Fin n → G, (∀ i, x i ∈ N) → x ∈ K := by
  let U : Fin n → OpenSubgroup G := fun i =>
    K.toOpenSubgroup.comap (MonoidHom.mulSingle (fun _ : Fin n => G) i)
      (continuous_mulSingle i)
  let N : OpenNormalSubgroup G :=
    { toOpenSubgroup := OpenSubgroup.iInfOfFinite U
      isNormal' := by
        change (⨅ i : Fin n, K.toSubgroup.comap
          (MonoidHom.mulSingle (fun _ : Fin n => G) i)).Normal
        exact Subgroup.normal_iInf_normal (fun _ => inferInstance) }
  refine ⟨N, ?_⟩
  intro x hx
  apply Subgroup.pi_mem_of_mulSingle_mem
  intro i
  exact (OpenSubgroup.iInfOfFinite_le U i) (hx i)

/-- A continuous discrete-valued function on a finite power has one common normal period in all coordinates. -/
theorem exists_common_normal_period [CompactSpace G] {Y : Type u} [TopologicalSpace Y]
    [DiscreteTopology Y] (n : ℕ) (f : (Fin n → G) → Y) (hf : Continuous f) :
    ∃ N : OpenNormalSubgroup G, ∀ y : Fin n → G, (∀ i, y i ∈ N) →
      ∀ x, f (x * y) = f x := by
  obtain ⟨K, hK⟩ := exists_openNormal_right_invariant f hf
  obtain ⟨N, hN⟩ := exists_common_openNormal n K
  exact ⟨N, fun y hy x => hK y (hN y hy) x⟩

/-- Actual finite-tuple factorization through one open normal quotient. -/
theorem exists_finite_quotient_factor [CompactSpace G] {Y : Type u} [TopologicalSpace Y]
    [DiscreteTopology Y] (n : ℕ) (f : (Fin n → G) → Y) (hf : Continuous f) :
    ∃ (N : OpenNormalSubgroup G) (F : C((Fin n → G ⧸ N.toSubgroup), Y)),
      ∀ x : Fin n → G, F (fun i => (x i : G ⧸ N.toSubgroup)) = f x := by
  classical
  obtain ⟨N, hN⟩ := exists_common_normal_period n f hf
  have hfactor : f.FactorsThrough (fun x : Fin n → G =>
      (fun i => (x i : G ⧸ N.toSubgroup))) := by
    intro x y hxy
    have hm : ∀ i, (x⁻¹ * y) i ∈ N := fun i =>
      QuotientGroup.eq.mp (congrFun hxy i)
    simpa only [mul_inv_cancel_left] using (hN (x⁻¹ * y) hm x).symm
  let : DiscreteTopology (G ⧸ N.toSubgroup) :=
    QuotientGroup.discreteTopology_iff.mpr N.toOpenSubgroup.isOpen
  let F : C((Fin n → G ⧸ N.toSubgroup), Y) :=
    ⟨fun z => f (fun i => (z i).out), continuous_of_discreteTopology⟩
  refine ⟨N, F, ?_⟩
  intro x
  apply hfactor
  funext i
  exact Quotient.out_eq (x i : G ⧸ N.toSubgroup)

end Langlands.Continuous

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- Covariance forces the values of a quotient-factorable function to be fixed. -/
theorem covariant_factor_fixed (A : TopRep.{u} k G) (N : OpenNormalSubgroup G)
    (n : ℕ) (f : covariantFunctions A n)
    (hf : f.1.FactorsThrough (fun x : Fin n → G =>
      (fun i => (x i : G ⧸ N.toSubgroup)))) (x : Fin n → G) :
    f.1 x ∈ Representation.invariants (A.ρ.toRepresentation.comp N.toSubgroup.subtype) := by
  intro g
  change A.ρ g.1 (f.1 x) = f.1 x
  rw [← f.property g.1 x]
  apply hf
  funext i
  simp only [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr g.2, one_mul]

/-- The quotient function with values in the actual fixed submodule and its covariance proof. -/
noncomputable def descendCovariant (A : DiscreteModule k G) (N : OpenNormalSubgroup G)
    (n : ℕ) (f : covariantFunctions A.toTopRep n)
    (hf : f.1.FactorsThrough (fun x : Fin n → G =>
      (fun i => (x i : G ⧸ N.toSubgroup)))) :
    covariantFunctions (finiteQuotientTopRep A N) n := by
  refine ⟨(fun z => ⟨f.1 (fun i => (z i).out),
    covariant_factor_fixed A.toTopRep N n f hf _⟩), ?_⟩
  intro q z
  refine QuotientGroup.induction_on q (fun g => ?_)
  apply Subtype.ext
  change f.1 (fun i => (((g : G ⧸ N.toSubgroup) * z i)).out) =
    A.toTopRep.ρ g (f.1 (fun i => (z i).out))
  rw [← f.property g _]
  apply hf
  funext i
  simp only [Quotient.out_eq, QuotientGroup.mk_mul]

omit [IsTopologicalGroup G] in
theorem descendCovariant_apply (A : DiscreteModule k G) (N : OpenNormalSubgroup G)
    (n : ℕ) (f : covariantFunctions A.toTopRep n)
    (hf : f.1.FactorsThrough (fun x : Fin n → G =>
      (fun i => (x i : G ⧸ N.toSubgroup)))) (x : Fin n → G) :
    ((descendCovariant A N n f hf).1 (fun i => (x i : G ⧸ N.toSubgroup))).1 = f.1 x := by
  apply hf
  funext i
  exact Quotient.out_eq (x i : G ⧸ N.toSubgroup)

/-- Every continuous covariant tuple function descends to actual fixed coefficients. -/
theorem exists_covariant_quotient_factor [CompactSpace G] (A : DiscreteModule k G)
    (n : ℕ) (f : covariantFunctions A.toTopRep n) (hcont : Continuous f.1) :
    ∃ (N : OpenNormalSubgroup G) (F : covariantFunctions (finiteQuotientTopRep A N) n),
      ∀ x : Fin n → G, (F.1 (fun i => (x i : G ⧸ N.toSubgroup))).1 = f.1 x := by
  obtain ⟨N, F, hF⟩ := exists_finite_quotient_factor n f.1 hcont
  have hf : f.1.FactorsThrough (fun x : Fin n → G =>
      (fun i => (x i : G ⧸ N.toSubgroup))) := by
    intro x y hxy
    rw [← hF x, ← hF y]
    exact congrArg F hxy
  exact ⟨N, descendCovariant A N n f hf, descendCovariant_apply A N n f hf⟩

/-- Covariance makes the discrete nested lift invariant. -/
theorem nestedLift_covariant [DiscreteTopology G] (A : TopRep.{u} k G) (n : ℕ)
    (f : covariantFunctions A n) :
    nestedLift A n f.1 ∈ (TopRep.resolutionX A n).ρ.invariants := by
  intro g
  apply nestedEval_injective A n
  funext x
  rw [nestedEval_action, nestedEval_lift]
  simpa only [mul_inv_cancel_left] using (f.property g (fun i => g⁻¹ * x i)).symm

/-- Actual finite-stage continuous cochains jointly cover the original nested complex. -/
theorem exists_finite_stage_cochain [CompactSpace G] [LocallyCompactSpace G]
    (A : DiscreteModule k G) (q : ℕ) (f : (TopRep.homogeneousCochains A.toTopRep).X q) :
    ∃ (N : OpenNormalSubgroup G)
      (v : (TopRep.homogeneousCochains (finiteQuotientTopRep A N)).X q),
      (ContinuousCohomology.cochainsMap (quotientProjection N)
        (fixedCoefficientInclusion A N)).f q v = f := by
  let fc : covariantFunctions A.toTopRep (q + 1) :=
    ⟨nestedEval A.toTopRep (q + 1) f.1, nestedEval_invariant A.toTopRep (q + 1) f⟩
  have hcont : Continuous fc.1 :=
    (continuous_nestedEval A.toTopRep (q + 1)).comp (continuous_const.prodMk continuous_id)
  obtain ⟨N, F, hF⟩ := exists_covariant_quotient_factor A (q + 1) fc hcont
  let : DiscreteTopology (G ⧸ N.toSubgroup) :=
    QuotientGroup.discreteTopology_iff.mpr N.toOpenSubgroup.isOpen
  let v : (TopRep.homogeneousCochains (finiteQuotientTopRep A N)).X q :=
    ⟨nestedLift (finiteQuotientTopRep A N) (q + 1) F.1,
      nestedLift_covariant (finiteQuotientTopRep A N) (q + 1) F⟩
  refine ⟨N, v, ?_⟩
  apply Subtype.ext
  apply nestedEval_injective A.toTopRep (q + 1)
  funext x
  change nestedEval A.toTopRep (q + 1)
    ((ContinuousCohomology.resolutionMap (quotientProjection N)
      (fixedCoefficientInclusion A N) (q + 1)).hom v.1) x = _
  rw [nestedEval_resolutionMap]
  change (nestedEval (finiteQuotientTopRep A N) (q + 1)
    (nestedLift (finiteQuotientTopRep A N) (q + 1) F.1)
      ((quotientProjection N) ∘ x)).1 = _
  rw [nestedEval_lift]
  exact hF x

/-- Inflation on actual nested continuous cochains is injective. -/
theorem continuousFiniteInflation_cochains_injective (A : DiscreteModule k G)
    (N : OpenNormalSubgroup G) (q : ℕ) :
    Function.Injective ((ContinuousCohomology.cochainsMap (quotientProjection N)
      (fixedCoefficientInclusion A N)).f q) := by
  intro v w hvw
  apply Subtype.ext
  apply nestedEval_injective (finiteQuotientTopRep A N) (q + 1)
  funext z
  let x : Fin (q + 1) → G := fun i => (z i).out
  have h := congrArg (fun t : (TopRep.homogeneousCochains A.toTopRep).X q =>
    nestedEval A.toTopRep (q + 1) t.1 x) hvw
  change nestedEval A.toTopRep (q + 1)
      ((ContinuousCohomology.resolutionMap (quotientProjection N)
        (fixedCoefficientInclusion A N) (q + 1)).hom v.1) x =
    nestedEval A.toTopRep (q + 1)
      ((ContinuousCohomology.resolutionMap (quotientProjection N)
        (fixedCoefficientInclusion A N) (q + 1)).hom w.1) x at h
  rw [nestedEval_resolutionMap, nestedEval_resolutionMap] at h
  have hx : (quotientProjection N) ∘ x = z := by
    funext i
    exact Quotient.out_eq (z i)
  rw [hx] at h
  exact Subtype.ext h

end Langlands.Continuous

namespace Langlands.Continuous

variable {k : Type u} [CommRing k]

/-- An actual cycle represented by a module element in the kernel. -/
noncomputable def moduleCycle (S : ShortComplex (ModuleCat.{u} k))
    (x : S.X₂) (hx : S.g x = 0) : S.cycles :=
  S.moduleCatCyclesIso.inv ⟨x, hx⟩

theorem moduleCycle_val (S : ShortComplex (ModuleCat.{u} k))
    (x : S.X₂) (hx : S.g x = 0) : S.iCycles (moduleCycle S x hx) = x := by
  exact ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_iCycles ⟨x, hx⟩

/-- The class of a genuine cycle in Mathlib's actual homology object. -/
noncomputable def moduleCycleClass (S : ShortComplex (ModuleCat.{u} k))
    (x : S.X₂) (hx : S.g x = 0) : S.homology :=
  S.homologyπ (moduleCycle S x hx)

theorem moduleCycleClass_surjective (S : ShortComplex (ModuleCat.{u} k))
    (y : S.homology) : ∃ (x : S.X₂) (hx : S.g x = 0), moduleCycleClass S x hx = y := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance y
  have hx : S.g (S.iCycles z) = 0 := ConcreteCategory.congr_hom S.iCycles_g z
  refine ⟨S.iCycles z, hx, ?_⟩
  apply congrArg S.homologyπ
  apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
  exact moduleCycle_val S _ hx

theorem moduleCycleClass_naturality {S T : ShortComplex (ModuleCat.{u} k)}
    (φ : S ⟶ T) (x : S.X₂) (hx : S.g x = 0) (hy : T.g (φ.τ₂ x) = 0) :
    ShortComplex.homologyMap φ (moduleCycleClass S x hx) =
      moduleCycleClass T (φ.τ₂ x) hy := by
  have h := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality φ)
    (moduleCycle S x hx)
  change ShortComplex.homologyMap φ (moduleCycleClass S x hx) =
    T.homologyπ (ShortComplex.cyclesMap φ (moduleCycle S x hx)) at h
  rw [h]
  apply congrArg T.homologyπ
  apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
  rw [moduleCycle_val]
  have hh := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i φ) (moduleCycle S x hx)
  change T.iCycles (ShortComplex.cyclesMap φ (moduleCycle S x hx)) =
    φ.τ₂ (S.iCycles (moduleCycle S x hx)) at hh
  simpa only [moduleCycle_val] using hh

theorem moduleCycleClass_eq_zero_iff (S : ShortComplex (ModuleCat.{u} k))
    (x : S.X₂) (hx : S.g x = 0) :
    moduleCycleClass S x hx = 0 ↔ ∃ y : S.X₁, S.f y = x := by
  have h := ConcreteCategory.congr_hom S.homology_π_ι (moduleCycle S x hx)
  change S.homologyι (moduleCycleClass S x hx) =
    S.pOpcycles (S.iCycles (moduleCycle S x hx)) at h
  rw [moduleCycle_val] at h
  constructor
  · intro hz
    apply (S.moduleCat_pOpcycles_eq_zero_iff x).mp
    simpa only [hz, map_zero] using h.symm
  · intro hy
    apply (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance
    rw [map_zero, h]
    exact (S.moduleCat_pOpcycles_eq_zero_iff x).mpr hy

section Filtered

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ ShortComplex (ModuleCat.{u} k)) (c : Limits.Cocone F)

omit [IsFiltered J] in
set_option backward.isDefEq.respectTransparency false in
/-- Injectivity in the outgoing term lets cycles descend along a jointly surjective cocone. -/
theorem homologyCocone_jointly_surjective
    (hinj : ∀ i, Function.Injective (c.ι.app i).τ₃)
    (hsurj : ∀ x : c.pt.X₂, ∃ (i : J) (xi : (F.obj i).X₂), (c.ι.app i).τ₂ xi = x)
    (y : c.pt.homology) :
    ∃ (i : J) (yi : (F.obj i).homology), ShortComplex.homologyMap (c.ι.app i) yi = y := by
  obtain ⟨x, hx, hxy⟩ := moduleCycleClass_surjective c.pt y
  obtain ⟨i, xi, hxi⟩ := hsurj x
  have hcycle : (F.obj i).g xi = 0 := by
    apply hinj i
    rw [map_zero]
    have h := ConcreteCategory.congr_hom (c.ι.app i).comm₂₃ xi
    change c.pt.g ((c.ι.app i).τ₂ xi) = (c.ι.app i).τ₃ ((F.obj i).g xi) at h
    rw [hxi, hx] at h
    exact h.symm
  refine ⟨i, moduleCycleClass (F.obj i) xi hcycle, ?_⟩
  have htarget : c.pt.g ((c.ι.app i).τ₂ xi) = 0 := by rw [hxi, hx]
  rw [moduleCycleClass_naturality (c.ι.app i) xi hcycle htarget]
  change moduleCycleClass c.pt ((c.ι.app i).τ₂ xi) htarget = y
  simpa only [hxi] using hxy

set_option backward.isDefEq.respectTransparency false in
/-- A class killed in the cocone becomes a boundary at a common later stage. -/
theorem homologyCocone_eventually_zero
    (hinj : ∀ i, Function.Injective (c.ι.app i).τ₂)
    (hsurj : ∀ x : c.pt.X₁, ∃ (i : J) (xi : (F.obj i).X₁), (c.ι.app i).τ₁ xi = x)
    (i : J) (yi : (F.obj i).homology)
    (hzero : ShortComplex.homologyMap (c.ι.app i) yi = 0) :
    ∃ (j : J) (f : i ⟶ j), ShortComplex.homologyMap (F.map f) yi = 0 := by
  obtain ⟨xi, hxi, rfl⟩ := moduleCycleClass_surjective (F.obj i) yi
  have htarget : c.pt.g ((c.ι.app i).τ₂ xi) = 0 := by
    have h := ConcreteCategory.congr_hom (c.ι.app i).comm₂₃ xi
    change c.pt.g ((c.ι.app i).τ₂ xi) = (c.ι.app i).τ₃ ((F.obj i).g xi) at h
    simpa only [hxi, map_zero] using h
  rw [moduleCycleClass_naturality (c.ι.app i) xi hxi htarget] at hzero
  obtain ⟨w, hw⟩ := (moduleCycleClass_eq_zero_iff c.pt _ htarget).mp hzero
  obtain ⟨j, wj, hj⟩ := hsurj w
  let l := IsFiltered.max i j
  let f : i ⟶ l := IsFiltered.leftToMax i j
  let g : j ⟶ l := IsFiltered.rightToMax i j
  have hc : (F.obj l).g ((F.map f).τ₂ xi) = 0 := by
    have h := ConcreteCategory.congr_hom (F.map f).comm₂₃ xi
    change (F.obj l).g ((F.map f).τ₂ xi) = (F.map f).τ₃ ((F.obj i).g xi) at h
    simpa only [hxi, map_zero] using h
  have hb : (F.obj l).f ((F.map g).τ₁ wj) = (F.map f).τ₂ xi := by
    apply hinj l
    calc
      (c.ι.app l).τ₂ ((F.obj l).f ((F.map g).τ₁ wj)) =
          c.pt.f ((c.ι.app l).τ₁ ((F.map g).τ₁ wj)) :=
        (ConcreteCategory.congr_hom (c.ι.app l).comm₁₂ ((F.map g).τ₁ wj)).symm
      _ = c.pt.f ((c.ι.app j).τ₁ wj) := congrArg c.pt.f
        (ConcreteCategory.congr_hom (congrArg ShortComplex.Hom.τ₁ (c.w g)) wj)
      _ = c.pt.f w := congrArg c.pt.f hj
      _ = (c.ι.app i).τ₂ xi := hw
      _ = (c.ι.app l).τ₂ ((F.map f).τ₂ xi) :=
        (ConcreteCategory.congr_hom (congrArg ShortComplex.Hom.τ₂ (c.w f)) xi).symm
  refine ⟨l, f, ?_⟩
  rw [moduleCycleClass_naturality (F.map f) xi hxi hc]
  exact (moduleCycleClass_eq_zero_iff (F.obj l) _ hc).mpr ⟨(F.map g).τ₁ wj, hb⟩

set_option backward.isDefEq.respectTransparency false in
/-- An injective, degreewise exhaustive filtered cocone remains colimiting on homology. -/
noncomputable def homologyCoconeIsColimit
    (hinj₂ : ∀ i, Function.Injective (c.ι.app i).τ₂)
    (hinj₃ : ∀ i, Function.Injective (c.ι.app i).τ₃)
    (hsurj₁ : ∀ x : c.pt.X₁, ∃ (i : J) (xi : (F.obj i).X₁), (c.ι.app i).τ₁ xi = x)
    (hsurj₂ : ∀ x : c.pt.X₂, ∃ (i : J) (xi : (F.obj i).X₂), (c.ι.app i).τ₂ xi = x) :
    Limits.IsColimit ((ShortComplex.homologyFunctor (ModuleCat.{u} k)).mapCocone c) := by
  apply Limits.isColimitOfReflects (forget (ModuleCat.{u} k))
  apply Limits.Types.FilteredColimit.isColimitOf'
  · intro y
    obtain ⟨i, yi, hyi⟩ := homologyCocone_jointly_surjective F c hinj₃ hsurj₂ y
    exact ⟨i, yi, hyi.symm⟩
  · intro i xi yi hxy
    change (F.obj i).homology at xi yi
    change ShortComplex.homologyMap (c.ι.app i) xi =
      ShortComplex.homologyMap (c.ι.app i) yi at hxy
    have hz : ShortComplex.homologyMap (c.ι.app i) (xi - yi) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨j, f, hf⟩ := homologyCocone_eventually_zero F c hinj₂ hsurj₁ i (xi - yi) hz
    refine ⟨j, f, ?_⟩
    change ShortComplex.homologyMap (F.map f) xi = ShortComplex.homologyMap (F.map f) yi
    exact sub_eq_zero.mp (by simpa only [map_sub] using hf)

end Filtered

end Langlands.Continuous

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem finiteStageCochainMap_injective (A : DiscreteModule k G)
    (N : OpenNormalSubgroup G) (q : ℕ) :
    Function.Injective ((finiteStageCochainMap A N).f q) := by
  let : DiscreteTopology (G ⧸ N.toSubgroup) :=
    QuotientGroup.discreteTopology_iff.mpr N.toOpenSubgroup.isOpen
  have : IsIso (continuousToOrdinaryCochains (finiteQuotientTopRep A N)) :=
    continuousToOrdinaryCochains_isIso (finiteQuotientTopRep A N)
  exact (continuousFiniteInflation_cochains_injective A N q).comp
    ((ModuleCat.mono_iff_injective
      ((inv (continuousToOrdinaryCochains (finiteQuotientTopRep A N))).f q)).mp inferInstance)

theorem finiteStageCochainMap_jointly_surjective [CompactSpace G] [LocallyCompactSpace G]
    (A : DiscreteModule k G) (q : ℕ) (v : (underlyingContinuousCochains A.toTopRep).X q) :
    ∃ (N : OpenNormalSubgroup G)
      (x : (groupCohomology.inhomogeneousCochains (finiteQuotientRep A.toRep N)).X q),
      (finiteStageCochainMap A N).f q x = v := by
  obtain ⟨N, w, hw⟩ := exists_finite_stage_cochain A q v
  refine ⟨N, (continuousToOrdinaryCochains (finiteQuotientTopRep A N)).f q w, ?_⟩
  have h := congrArg (fun t => (t.f q) w) (comparison_comp_finiteStageCochainMap A N)
  exact h.trans hw

/-- Degreewise injectivity and exhaustion prove the actual cochain colimit property. -/
noncomputable def finiteStageCochainCoconeIsColimit [CompactSpace G] [LocallyCompactSpace G]
    (A : DiscreteModule k G) : Limits.IsColimit (finiteStageCochainCocone A) := by
  apply HomologicalComplex.isColimitOfEval
  intro q
  apply Limits.isColimitOfReflects (forget (ModuleCat.{u} k))
  apply Limits.Types.FilteredColimit.isColimitOf'
  · intro v
    obtain ⟨N, x, hx⟩ := finiteStageCochainMap_jointly_surjective A q v
    exact ⟨OrderDual.toDual N, x, hx.symm⟩
  · intro N x y h
    have heq := finiteStageCochainMap_injective A (OrderDual.ofDual N) q h
    exact ⟨N, 𝟙 N, by rw [heq]⟩

set_option backward.isDefEq.respectTransparency false in
/-- Finite-stage cycles and eventual boundaries prove the cohomology colimit. -/
noncomputable def finiteStageHomologyCoconeIsColimit [CompactSpace G] [LocallyCompactSpace G]
    (A : DiscreteModule k G) (q : ℕ) : Limits.IsColimit (finiteStageHomologyCocone A q) := by
  apply homologyCoconeIsColimit
    (finiteQuotientCochainDiagram A.toRep ⋙
      HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) q)
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) q).mapCocone
      (finiteStageCochainCocone A))
  · intro N
    exact finiteStageCochainMap_injective A (OrderDual.ofDual N) q
  · intro N
    exact finiteStageCochainMap_injective A (OrderDual.ofDual N) ((ComplexShape.up ℕ).next q)
  · intro x
    obtain ⟨N, v, hv⟩ :=
      finiteStageCochainMap_jointly_surjective A ((ComplexShape.up ℕ).prev q) x
    exact ⟨OrderDual.toDual N, v, hv⟩
  · intro x
    obtain ⟨N, v, hv⟩ := finiteStageCochainMap_jointly_surjective A q x
    exact ⟨OrderDual.toDual N, v, hv⟩

/-- The comparison isomorphism, obtained from the proved colimit universal property. -/
noncomputable def finiteQuotientComparisonIso [CompactSpace G] [LocallyCompactSpace G]
    (A : DiscreteModule k G) (q : ℕ) :
    finiteQuotientCohomology A.toRep q ≅
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj (continuousCohomology q A.toTopRep) :=
  Limits.colimit.isoColimitCocone
    ⟨finiteStageHomologyCocone A q, finiteStageHomologyCoconeIsColimit A q⟩ ≪≫
    (((TopRep.homogeneousCochains A.toTopRep).sc q).mapHomologyIso
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)))

theorem finiteQuotientComparisonIso_hom [CompactSpace G] [LocallyCompactSpace G]
    (A : DiscreteModule k G) (q : ℕ) :
    (finiteQuotientComparisonIso A q).hom = finiteQuotientComparison A q := rfl

instance finiteQuotientComparison_isIso [CompactSpace G] [LocallyCompactSpace G]
    (A : DiscreteModule k G) (q : ℕ) : IsIso (finiteQuotientComparison A q) := by
  rw [← finiteQuotientComparisonIso_hom]
  infer_instance

/-- A linear isomorphism in the common arbitrary universe, for every natural degree. -/
noncomputable def finiteQuotientComparisonLinearEquiv [CompactSpace G] [LocallyCompactSpace G]
    (A : DiscreteModule k G) (q : ℕ) :
    finiteQuotientCohomology A.toRep q ≃ₗ[k] continuousCohomology q A.toTopRep :=
  (finiteQuotientComparisonIso A q).toLinearEquiv

/-- The linear equivalence has the canonical comparison as its forward linear map. -/
theorem finiteQuotientComparisonLinearEquiv_toLinearMap
    [CompactSpace G] [LocallyCompactSpace G] (A : DiscreteModule k G) (q : ℕ) :
    (finiteQuotientComparisonLinearEquiv A q).toLinearMap =
      (finiteQuotientComparison A q).hom := rfl

@[simp]
theorem finiteQuotientComparisonLinearEquiv_apply
    [CompactSpace G] [LocallyCompactSpace G] (A : DiscreteModule k G) (q : ℕ)
    (x : finiteQuotientCohomology A.toRep q) :
    finiteQuotientComparisonLinearEquiv A q x = finiteQuotientComparison A q x := rfl

/-- Compactness and finite descent identify actual finite-quotient and continuous cohomology. -/
theorem finiteQuotientComparisonIsIso : FiniteQuotientComparisonIsIso.{u} := by
  intro k G _ _ _ _ _ _ _ A q
  infer_instance

example : FiniteQuotientComparisonIsIso.{u} := finiteQuotientComparisonIsIso.{u}

end Langlands.Continuous
