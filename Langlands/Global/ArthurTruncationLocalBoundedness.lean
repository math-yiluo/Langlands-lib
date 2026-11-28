import Langlands.Global.ArthurTruncationFixedPoint
import Langlands.Global.AdelicIntertwiningConvergenceReduction
import Langlands.Global.ArthurTruncationWeyl
import Langlands.Global.ArthurTruncationFinitenessProof
import Langlands.Global.ArthurTruncationRay

/-! # Measurable, locally bounded kernels and compact cutoff support -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj Pointwise ENNReal

namespace Langlands.Global.ArthurTruncation.Idempotence

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  AdelicGroupPoints ArthurParabolicSpaces EisensteinConstantTerm

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

section Radical

variable {U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine U.X.left]
  (j : U ⟶ G) [IsClosedImmersion j.hom.hom.left]
  (φ : AdelicGroupPoints F G → ℂ)

local notation "V" => SubgroupFunctor.range j
local notation "A" => AdelicSubgroupPoints.adelicPoints F G V
local notation "Γ" => AdelicSubgroupPoints.rationalSubgroup F G V
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G V

local instance : IsClosed (A : Set (AdelicGroupPoints F G)) :=
  AdelicSubgroupPoints.isClosed_adelicPoints_range F G j

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffine U.X.left]
  [IsClosedImmersion j.hom.hom.left] in
private theorem radicalIntegrand_invariant
    (hφ : ∀ r ∈ rationalSubgroup F G, ∀ x, φ (r * x) = φ x)
    (r : Γ) (n : A) (x : AdelicGroupPoints F G) :
    φ ((((r : A) * n : A) : AdelicGroupPoints F G) * x) =
      φ ((n : AdelicGroupPoints F G) * x) := by
  rw [Subgroup.coe_mul, mul_assoc]
  apply hφ
  exact rationalImage_le_rationalSubgroup j
    ((mem_rationalSubgroup_range_iff j _).mp r.property)

/-- The integral along a represented radical of a measurable rational-invariant
function is measurable in the external adelic argument. -/
theorem measurable_subgroupConstantTerm
    (hφm : Measurable φ)
    (hφ : ∀ r ∈ rationalSubgroup F G, ∀ x, φ (r * x) = φ x) :
    Measurable (subgroupConstantTerm F j φ) := by
  let : LocallyCompactSpace A := (AdelicSubgroupPoints.isClosed_adelicPoints_range F G j).locallyCompactSpace
  let s := LeftCosetSpace.fundamentalDomain Γ (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G V)
  let m := AdelicSubgroupPoints.normalizedHaarMeasure F G V
  have : SFinite m := by
    change SFinite (AdelicSubgroupPoints.quotientMassNormalizer F G V •
      (Measure.haar : Measure A))
    infer_instance
  have heq (x : AdelicGroupPoints F G) :
      subgroupConstantTerm F j φ x = ∫ n in s, φ ((n : AdelicGroupPoints F G) * x) ∂m := by
    unfold subgroupConstantTerm
    rw [normalizedRationalQuotientHaarMeasure_eq_quotientMeasure]
    exact RankinSelbergGlobal.Unfolding.integral_out_eq Γ
      (hφm.comp (continuous_subtype_val.mul_const x).measurable)
      (fun r n => radicalIntegrand_invariant j φ hφ r n x) m s
  have hf : Measurable fun p : AdelicGroupPoints F G × A =>
      φ ((p.2 : AdelicGroupPoints F G) * p.1) :=
    hφm.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  rw [funext heq]
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := m.restrict s)).measurable

/-- A compact radical quotient lets a single compact set of representatives control
all values of the constant term on a compact set of arguments. -/
theorem subgroupConstantTerm_bounded_on_compact
    (hs : Smooth U.X.hom) (hc : ConnectedSpace U.X.left) (hu : IsUnipotent U)
    (hφ : IsLocallyBoundedInvariant (rationalSubgroup F G) φ)
    (C : Set (AdelicGroupPoints F G)) (hC : IsCompact C) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ C, ‖subgroupConstantTerm F j φ x‖ ≤ M := by
  let : CompactSpace Q := AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j hs hc hu
  let m := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G V
  let : IsProbabilityMeasure m :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G V
  obtain ⟨Ω, hΩ, hrep⟩ := AdelicSubgroupPoints.exists_isCompact_rational_mul_mem_range F j hs hc hu
  obtain ⟨M, hM⟩ := hφ.2.1 ((Subtype.val '' Ω) * C) ((hΩ.image continuous_subtype_val).mul hC)
  refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
  change ‖∫ q : Q, φ (((q.out : A) : AdelicGroupPoints F G) * x) ∂m‖ ≤ max M 0
  refine (norm_integral_le_of_norm_le_const (C := max M 0)
    (Filter.Eventually.of_forall fun q : Q => ?_)).trans_eq ?_
  · obtain ⟨r, hr, hrq⟩ := hrep q.out
    rw [← radicalIntegrand_invariant j φ hφ.2.2 ⟨r, hr⟩ q.out x]
    exact (hM _ ⟨_, ⟨r * q.out, hrq, rfl⟩, x, hx, rfl⟩).trans (le_max_left _ _)
  · simp [Measure.real_def]

end Radical

section Cutoff

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

omit [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left] in
/-- Every real character applied to the minimal Iwasawa height is continuous. -/
theorem continuous_pair_height (ξ : Vstar T) :
    Continuous fun g => pair T ξ (height hi hK hρ g) := by
  obtain ⟨m, rfl⟩ := hρ.surjective ξ
  simp only [height, pair_toA0]
  have hm : Continuous (realParameterPairing F (Standard.parabolicScheme i ν ∅) m) := by
    induction m using TensorProduct.inductionOn with
    | tmul t χ => exact continuous_const.mul (continuous_dualEval F _ χ)
    | add a b ha hb =>
      rw [map_add, LinearMap.coe_add]
      exact ha.add hb
  exact hm.comp hK.continuous_height

include hν in
omit [LocallyOfFiniteType G.X.hom] in
theorem continuous_fullWeight_height (β : simpleRelativeRoots i ν) :
    Continuous fun g => ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) β.1
      (height hi hK hρ g) := by
  simp only [← pair_fundamentalWeight hG hi hν D β]
  exact continuous_pair_height hi hK hρ _

include hν in
theorem measurable_tauHat_complex (S : Set (characterLattice T)) (Tp : V T) :
    Measurable fun g => (ArthurRelative.tauHat hG hi ν D S (simpleRelativeRoots i ν)
      (height hi hK hρ g - Tp) : ℂ) := by
  classical
  simp only [ArthurRelative.tauHat_eq hG hi D (ν := ν) S Set.Subset.rfl, Int.cast_ite,
    Int.cast_one, Int.cast_zero, map_sub]
  apply Measurable.ite _ measurable_const measurable_const
  change MeasurableSet {x : AdelicGroupPoints F G | ∀ a ∈ simpleRelativeRoots i ν \ S,
    0 < ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) a
      (height hi hK hρ x) - ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) a Tp}
  let I := simpleRelativeRoots i ν \ S
  have hI : I.Countable := ((hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).subset
    Set.sdiff_subset).countable
  let : Countable I := hI.to_subtype
  have heq : {x : AdelicGroupPoints F G | ∀ a ∈ I,
      0 < ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) a (height hi hK hρ x) -
        ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) a Tp} =
      ⋂ a : I, {x | 0 < ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) a.1
        (height hi hK hρ x) - ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) a.1 Tp} :=
    by ext x; simp only [Set.mem_ofPred_eq, Set.mem_iInter, Subtype.forall]
  rw [heq]
  exact MeasurableSet.iInter fun a =>
    (isOpen_lt continuous_const
      ((continuous_fullWeight_height hG hi hν D hK hρ ⟨a.1, a.2.1⟩).sub
        continuous_const)).measurableSet

include hν in
omit [LocallyOfFiniteType G.X.hom] in
private theorem fullWeight_height_mul_le_on_compact
    (C : Set (AdelicGroupPoints F G)) (hC : IsCompact C)
    (β : simpleRelativeRoots i ν) :
    ∃ B : ℝ, ∀ g z : AdelicGroupPoints F G, z ∈ C →
      ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) β.1 (height hi hK hρ (g * z)) ≤
        ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) β.1 (height hi hK hρ g) + B := by
  let ξ := fundamentalWeight hG hi hν D β
  obtain ⟨m, hm⟩ := hρ.surjective ξ
  let w := ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) β.1
  have hw (x : AdelicGroupPoints F G) : w (height hi hK hρ x) =
      realParameterPairing F (Standard.parabolicScheme i ν ∅) m (hK.height x) := by
    rw [show w = ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) β.1 from rfl,
      ← pair_fundamentalWeight hG hi hν D β]
    change pair T ξ _ = _
    rw [← hm, height, pair_toA0]
  obtain ⟨b, hb⟩ := (hK.isCompact.mul hC).bddAbove_image
    (continuous_fullWeight_height hG hi hν D hK hρ β).continuousOn
  refine ⟨b, fun g z hz => ?_⟩
  obtain ⟨k, hk, heq⟩ := hK.exists_height_mul_eq_add g z
  change w (height hi hK hρ (g * z)) ≤ w (height hi hK hρ g) + b
  rw [hw, heq, map_add, ← hw, ← hw]
  exact add_le_add le_rfl (hb ⟨k * z, ⟨k, hk, z, hz, rfl⟩, rfl⟩)

include hν in
/-- Finitely many rational cosets meet the active cutoff on any prescribed compact set. -/
theorem finite_cutoff_support_on_compact
    (S : Finset (characterLattice T)) (hS : S ∈ (simpleFinset ν hG hi).powerset)
    (Tp : V T) (C : Set (AdelicGroupPoints F G)) (hC : IsCompact C) :
    {c : ParabolicRationalCosets F (Standard.parabolicHom i ν (S : Set (characterLattice T))) |
      ∃ x ∈ C, ArthurRelative.tauHat hG hi ν D (S : Set (characterLattice T))
        (simpleRelativeRoots i ν)
        (height hi hK hρ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * x) - Tp) ≠ 0}.Finite := by
  classical
  let : Fintype (simpleRelativeRoots i ν) :=
    (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).fintype
  choose B hB using fullWeight_height_mul_le_on_compact hG hi hν D hK hρ C hC
  let v : V T := (1 : ℝ) ⊗ₜ[ℤ] ν
  let w (β : simpleRelativeRoots i ν) :=
    ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) β.1
  have hv (β : simpleRelativeRoots i ν) : 0 < w β v :=
    fullWeight_pos_of_simple_pos hG hi hν D (fun _ hb => cocharacter_simple_pos hb) β.2
  let R := ∑ β, max (B β / w β v) 0
  have hR (β : simpleRelativeRoots i ν) : B β ≤ R * w β v := by
    apply (div_le_iff₀ (hv β)).mp
    exact (le_max_left _ _).trans (Finset.single_le_sum
      (f := fun b => max (B b / w b v) 0)
      (fun b _ => le_max_right _ _) (Finset.mem_univ β))
  refine (truncationFiniteness F G T i ν hG hi hν D K hK hρ S hS (Tp - R • v) 1).subset ?_
  intro c hc
  obtain ⟨x, hx, hcut⟩ := hc
  rw [ArthurRelative.tauHat_eq hG hi D (ν := ν) _ Set.Subset.rfl] at hcut
  have hpos : ∀ a ∈ simpleRelativeRoots i ν \ (S : Set (characterLattice T)),
      0 < ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) a
        (height hi hK hρ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * x) - Tp) := by
    by_contra hn
    exact hcut (ite_eq_right hn)
  change ArthurRelative.tauHat hG hi ν D _ _ _ ≠ 0
  rw [ArthurRelative.tauHat_eq hG hi D (ν := ν) _ Set.Subset.rfl, ite_eq_left]
  · exact one_ne_zero
  · intro a ha
    let b : simpleRelativeRoots i ν := ⟨a, ha.1⟩
    have h₁ := hB b (c.out : rationalSubgroup F G).val x hx
    have h₂ := hpos a ha
    have h₃ := hR b
    simp only [w, b, mul_one, map_sub, map_smul, smul_eq_mul] at h₂ h₃ ⊢
    linarith

/-- One summand before the rational coset sum in the truncation formula. -/
def cutoffKernel (S : Set (characterLattice T)) (Tp : V T)
    (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) : ℂ :=
  constantTerm F i ν S φ g * (ArthurRelative.tauHat hG hi ν D S (simpleRelativeRoots i ν)
    (height hi hK hρ g - Tp) : ℂ)

include hν in
theorem cutoffKernel_measurable (S : Set (characterLattice T)) (Tp : V T)
    (φ : AdelicGroupPoints F G → ℂ) (hφ : IsLocallyBoundedInvariant (rationalSubgroup F G) φ) :
    Measurable (cutoffKernel hG hi D hK hρ S Tp φ) :=
  (measurable_subgroupConstantTerm _ φ hφ.1 hφ.2.2).mul
    (measurable_tauHat_complex hG hi hν D hK hρ S Tp)

include hν in
theorem cutoffKernel_bounded_on_compact (S : Set (characterLattice T))
    (hS : S ⊆ simpleRelativeRoots i ν) (Tp : V T)
    (φ : AdelicGroupPoints F G → ℂ) (hφ : IsLocallyBoundedInvariant (rationalSubgroup F G) φ)
    (C : Set (AdelicGroupPoints F G)) (hC : IsCompact C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ C, ‖cutoffKernel hG hi D hK hρ S Tp φ x‖ ≤ B := by
  classical
  have hU := (Standard.parabolicStructure i ν hG hi hν S hS).2.2.1.1
  obtain ⟨B, hB, hbound⟩ := subgroupConstantTerm_bounded_on_compact
    (Standard.unipotentHom i ν S) φ hU.smooth hU.connectedSpace hU.isUnipotent hφ C hC
  refine ⟨B, hB, fun x hx => ?_⟩
  unfold cutoffKernel
  rw [ArthurRelative.tauHat_eq hG hi D S Set.Subset.rfl]
  split
  · simpa only [Int.cast_one, mul_one] using hbound x hx
  · simpa only [Int.cast_zero, mul_zero, norm_zero] using hB

include hν in
/-- The sum of the absolute values of the coset kernels is uniformly bounded on a compact set. -/
theorem exists_enorm_cutoffSeries_bound (S : Finset (characterLattice T))
    (hS : S ∈ (simpleFinset ν hG hi).powerset) (Tp : V T)
    (φ : AdelicGroupPoints F G → ℂ) (hφ : IsLocallyBoundedInvariant (rationalSubgroup F G) φ)
    (C : Set (AdelicGroupPoints F G)) (hC : IsCompact C) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ x ∈ C,
      ∑' c : ParabolicRationalCosets F (Standard.parabolicHom i ν (S : Set (characterLattice T))),
        ‖cutoffKernel hG hi D hK hρ (S : Set (characterLattice T)) Tp φ
          (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * x)‖ₑ ≤ B := by
  classical
  let J := (S : Set (characterLattice T))
  let P := ParabolicRationalCosets F (Standard.parabolicHom i ν J)
  let r (c : P) := ((c.out : rationalSubgroup F G) : AdelicGroupPoints F G)
  let supp : Set P := {c | ∃ x ∈ C, ArthurRelative.tauHat hG hi ν D J (simpleRelativeRoots i ν)
    (height hi hK hρ (r c * x) - Tp) ≠ 0}
  have hfin : supp.Finite := finite_cutoff_support_on_compact hG hi hν D hK hρ S hS Tp C hC
  have hJ : J ⊆ simpleRelativeRoots i ν :=
    fun β hβ => (mem_simpleFinset hG hi).mp ((Finset.mem_powerset.mp hS) hβ)
  have hb (c : P) := cutoffKernel_bounded_on_compact hG hi hν D hK hρ J hJ Tp φ hφ
    (r c • C) (hC.smul (r c))
  choose B hB hbound using hb
  let H : ℝ≥0∞ := ∑ c ∈ hfin.toFinset, ENNReal.ofReal (B c)
  refine ⟨H, ENNReal.sum_ne_top.mpr fun c _ => ENNReal.ofReal_ne_top, fun x hx => ?_⟩
  let f (c : P) : ℝ≥0∞ := ‖cutoffKernel hG hi D hK hρ J Tp φ (r c * x)‖ₑ
  change (∑' c, f c) ≤ H
  rw [tsum_eq_sum (s := hfin.toFinset)]
  · refine Finset.sum_le_sum fun c _ => ?_
    have := hbound c (r c * x) ⟨x, hx, rfl⟩
    simpa only [ofReal_norm, f] using ENNReal.ofReal_le_ofReal this
  · intro c hc
    have hcut : ArthurRelative.tauHat hG hi ν D J (simpleRelativeRoots i ν)
        (height hi hK hρ (r c * x) - Tp) = 0 := by
      by_contra h
      exact hc (hfin.mem_toFinset.mpr ⟨x, hx, h⟩)
    simp only [f, cutoffKernel, hcut, Int.cast_zero, mul_zero, enorm_zero]

/-- The series of absolute values of the rational cutoff kernels. -/
def cutoffSeriesEnorm (S : Set (characterLattice T)) (Tp : V T)
    (φ : AdelicGroupPoints F G → ℂ) (x : AdelicGroupPoints F G) : ℝ≥0∞ :=
  ∑' c : ParabolicRationalCosets F (Standard.parabolicHom i ν S),
    ‖cutoffKernel hG hi D hK hρ S Tp φ (((c.out : rationalSubgroup F G) : AdelicGroupPoints F G) * x)‖ₑ

include hν in
/-- The same absolute majorant holds on a full adelic radical orbit, by rational
invariance of the coset sum and compactness of the radical's rational quotient. -/
theorem exists_enorm_cutoffSeries_bound_on_radical
    (S : Finset (characterLattice T)) (hS : S ∈ (simpleFinset ν hG hi).powerset)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν) (Tp : V T)
    (φ : AdelicGroupPoints F G → ℂ) (hφ : IsLocallyBoundedInvariant (rationalSubgroup F G) φ)
    (x : AdelicGroupPoints F G) :
    ∃ B : ℝ≥0∞, B ≠ ∞ ∧
      ∀ v : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (Standard.unipotentHom i ν J)),
      cutoffSeriesEnorm hG hi D hK hρ (S : Set (characterLattice T)) Tp φ
        ((v : AdelicGroupPoints F G) * x) ≤ B := by
  let j := Standard.unipotentHom i ν J
  let A := AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range j)
  let f (v : A) : AdelicGroupPoints F G := (v : AdelicGroupPoints F G) * x
  let Φ := cutoffKernel hG hi D hK hρ (S : Set (characterLattice T)) Tp φ
  let p := Standard.parabolicHom i ν (S : Set (characterLattice T))
  let Pm := (rationalSubgroup F _).map (map F _ G p).toMonoidHom
  have hU := (Standard.parabolicStructure i ν hG hi hν J hJ).2.2.1.1
  obtain ⟨Ω, hΩ, hrep⟩ := AdelicSubgroupPoints.exists_isCompact_rational_mul_mem_range F j
    hU.smooth hU.connectedSpace hU.isUnipotent
  obtain ⟨B, hB, hbound⟩ := exists_enorm_cutoffSeries_bound hG hi hν D hK hρ S hS Tp φ hφ
    (f '' Ω) (hΩ.image (continuous_subtype_val.mul_const x))
  have hroots : (S : Set (characterLattice T)) ⊆ simpleRelativeRoots i ν :=
    fun a ha => (mem_simpleFinset hG hi).mp (Finset.mem_powerset.mp hS ha)
  have hnorm : ∀ z ∈ Pm, ∀ y, ‖Φ (z * y)‖ₑ = ‖Φ y‖ₑ := by
    intro z hz y
    have hz' : z ∈ parabolicRationalImage p := (mem_parabolicRationalImage_iff (i := i) (ν := ν) _ z).mpr
      ((rationalImage_eq_map p).symm ▸ hz)
    exact congrArg (‖·‖ₑ) (truncationKernel_parabolicRational_mul hG hi hν D hK hρ
      hroots Tp φ hφ.2.2 hz' y)
  refine ⟨B, hB, fun v => ?_⟩
  obtain ⟨δ, hδ, hδv⟩ := hrep v
  have hδG : ((δ : A) : AdelicGroupPoints F G) ∈ rationalSubgroup F G :=
    rationalImage_le_rationalSubgroup j ((mem_rationalSubgroup_range_iff j _).mp hδ)
  have heq := tsum_out_mul_left (P := Pm) (g := fun z => ‖Φ z‖ₑ) hnorm hδG (f v)
  have hmul : f (δ * v) = ((δ : A) : AdelicGroupPoints F G) * f v := by
    simp [f, mul_assoc]
  rw [← hmul] at heq
  unfold cutoffSeriesEnorm
  exact heq ▸ hbound _ ⟨δ * v, hδv, rfl⟩

end Cutoff

end Langlands.Global.ArthurTruncation.Idempotence
