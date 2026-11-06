import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictScalarIdealDescentStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteRadiusRealization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartScalarRetraction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartNormalizationMaps
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartIntersection
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain
import Langlands.Geometry.Analytic.StrictTestDomain.RationalTensorComparison

/-! # Strict scalar normalization descends rational ideal effectiveness -/

noncomputable section

universe u v

namespace Langlands.Analytic

namespace StrictScalarIdealDescent

/-- A bounded ring homomorphism is continuous for the two norm topologies. -/
theorem continuous_boundedRingHom {A : Type*} {B : Type*} [NormedCommRing A]
    [NormedCommRing B] (f : BoundedRingHom A B) : Continuous f := by
  obtain ⟨C, -, hC⟩ := f.bounded
  exact AddMonoidHomClass.continuous_of_bound f.toRingHom C hC

section Abstract

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S]

/-- The ideal of those `y` all of whose multiples retract into `M`. -/
def retractIdeal (ρ : S →+ R) (M : Ideal R) : Ideal S where
  carrier := {y | ∀ b, ρ (b * y) ∈ M}
  add_mem' := fun {x y} hx hy b => by
    rw [mul_add, map_add]
    exact M.add_mem (hx b) (hy b)
  zero_mem' := fun b => by
    rw [mul_zero, map_zero]
    exact M.zero_mem
  smul_mem' := fun a x hx b => by
    rw [smul_eq_mul, ← mul_assoc]
    exact hx (b * a)

theorem mem_retractIdeal {ρ : S →+ R} {M : Ideal R} {y : S} :
    y ∈ retractIdeal ρ M ↔ ∀ b, ρ (b * y) ∈ M :=
  Iff.rfl

theorem retract_mem_of_mem_retractIdeal {ρ : S →+ R} {M : Ideal R} {y : S}
    (hy : y ∈ retractIdeal ρ M) : ρ y ∈ M := by
  simpa using hy 1

theorem isClosed_retractIdeal [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing S]
    {ρ : S →+ R} (hρ : Continuous ρ) {M : Ideal R} (hM : IsClosed (M : Set R)) :
    IsClosed (retractIdeal ρ M : Set S) := by
  have heq : (retractIdeal ρ M : Set S) = ⋂ b, (fun y => ρ (b * y)) ⁻¹' (M : Set R) := by
    ext y
    simp only [SetLike.mem_coe, mem_retractIdeal, Set.mem_iInter, Set.mem_preimage]
  rw [heq]
  exact isClosed_iInter fun b => hM.preimage (hρ.comp (continuous_const.mul continuous_id))

/-- Closing before or after extension along a continuous map gives the same
closed ideal. -/
theorem topologicalClosure_map_topologicalClosure [TopologicalSpace R] [IsTopologicalRing R]
    [TopologicalSpace S] [IsTopologicalRing S] (g : R →+* S) (hg : Continuous g)
    (J : Ideal R) :
    (Ideal.map g J.topologicalClosure).topologicalClosure =
      (Ideal.map g J).topologicalClosure := by
  apply le_antisymm
  · refine Submodule.topologicalClosure_minimal _ ?_
      (Submodule.isClosed_topologicalClosure _)
    apply Ideal.map_le_iff_le_comap.mpr
    refine Submodule.topologicalClosure_minimal _ ?_
      ((Submodule.isClosed_topologicalClosure _).preimage hg)
    exact Ideal.map_le_iff_le_comap.mp (Submodule.le_topologicalClosure _)
  · exact Submodule.topologicalClosure_mono
      (Ideal.map_mono (Submodule.le_topologicalClosure _))

/-- Overlap compatibility of closed extensions is transported along a map of
overlaps through which both normalized restrictions factor. -/
theorem closure_map_compatible {Rd Re Ro Sd Se So : Type*}
    [CommRing Rd] [TopologicalSpace Rd] [IsTopologicalRing Rd]
    [CommRing Re] [TopologicalSpace Re] [IsTopologicalRing Re]
    [CommRing Ro] [TopologicalSpace Ro] [IsTopologicalRing Ro]
    [CommRing Sd] [TopologicalSpace Sd] [IsTopologicalRing Sd]
    [CommRing Se] [TopologicalSpace Se] [IsTopologicalRing Se]
    [CommRing So] [TopologicalSpace So] [IsTopologicalRing So]
    (l : Rd →+* Ro) (r : Re →+* Ro) (Fd : Rd →+* Sd) (Fe : Re →+* Se)
    (md : Sd →+* So) (me : Se →+* So) (G : Ro →+* So)
    (hmd : Continuous md) (hme : Continuous me) (hG : Continuous G)
    (hl : md.comp Fd = G.comp l) (hr : me.comp Fe = G.comp r)
    (Id : Ideal Rd) (Ie : Ideal Re)
    (h : (Ideal.map l Id).topologicalClosure = (Ideal.map r Ie).topologicalClosure) :
    (Ideal.map md (Ideal.map Fd Id).topologicalClosure).topologicalClosure =
      (Ideal.map me (Ideal.map Fe Ie).topologicalClosure).topologicalClosure := by
  rw [topologicalClosure_map_topologicalClosure md hmd,
    topologicalClosure_map_topologicalClosure me hme, Ideal.map_map, Ideal.map_map, hl, hr,
    ← Ideal.map_map, ← Ideal.map_map, ← topologicalClosure_map_topologicalClosure G hG,
    ← topologicalClosure_map_topologicalClosure G hG (Ideal.map r Ie), h]

variable [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing S]
  {Q : Type*} [CommRing Q]
  (F : R →+* S) (β : Q →+* S) (ρ : S →+ R) (hρ : Continuous ρ)
  (hmul : ∀ a b, ρ (F a * b) = a * ρ b)

include hρ hmul in
/-- A continuous `F`-linear retraction sends the closed extension of a closed
ideal back into that ideal. -/
theorem retract_mem_of_mem_closure_map (I : Ideal R) (hI : IsClosed (I : Set R)) {y : S}
    (hy : y ∈ (Ideal.map F I).topologicalClosure) : ρ y ∈ I := by
  apply retract_mem_of_mem_retractIdeal
  refine (Ideal.map F I).topologicalClosure_minimal ?_ (isClosed_retractIdeal hρ hI) hy
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha b
  change ρ (b * F a) ∈ I
  rw [mul_comm, hmul]
  exact I.mul_mem_right _ ha

include hρ hmul in
/-- Density of the fractions `β s ^ (-r) β a` and linearity over `F` propagate the
retraction condition from the elements `β q` to all their multiples. -/
theorem retract_mul_mem_of_dense (M : Ideal R) (hM : IsClosed (M : Set R)) (J : Ideal Q)
    (hJ : ∀ q ∈ J, ρ (β q) ∈ M) (s : Q) (w : R) (hw : F w * β s = 1)
    (hdense : Dense {x : S | ∃ r : ℕ, ∃ a : Q, β s ^ r * x = β a})
    {q : Q} (hq : q ∈ J) (b : S) : ρ (b * β q) ∈ M := by
  have hS : IsClosed ((fun x => ρ (x * β q)) ⁻¹' (M : Set R)) :=
    hM.preimage (hρ.comp (continuous_id.mul continuous_const))
  have hsub : {x : S | ∃ r : ℕ, ∃ a : Q, β s ^ r * x = β a} ⊆
      (fun x => ρ (x * β q)) ⁻¹' (M : Set R) := by
    rintro x ⟨r, a, ha⟩
    have hx : x = F (w ^ r) * β a := by
      calc
        x = (F w * β s) ^ r * x := by rw [hw, one_pow, one_mul]
        _ = F w ^ r * (β s ^ r * x) := by rw [mul_pow, mul_assoc]
        _ = F (w ^ r) * β a := by rw [ha, map_pow]
    change ρ (x * β q) ∈ M
    rw [hx, mul_assoc, hmul, ← map_mul]
    exact M.mul_mem_left _ (hJ _ (J.mul_mem_left a hq))
  have hb : b ∈ closure {x : S | ∃ r : ℕ, ∃ a : Q, β s ^ r * x = β a} := by
    rw [hdense.closure_eq]
    exact Set.mem_univ b
  exact closure_minimal hsub hS hb

include hρ hmul in
/-- The abstract descent step: an ideal whose closed extension along `F` is the
closed extension of `J` along `β` lies in every closed ideal containing the
retractions of `β J`. -/
theorem le_of_closure_map_eq (hleft : ∀ a, ρ (F a) = a) (I M : Ideal R)
    (hM : IsClosed (M : Set R)) (J : Ideal Q) (hJ : ∀ q ∈ J, ρ (β q) ∈ M) (s : Q) (w : R)
    (hw : F w * β s = 1) (hdense : Dense {x : S | ∃ r : ℕ, ∃ a : Q, β s ^ r * x = β a})
    (heff : (Ideal.map β J).topologicalClosure = (Ideal.map F I).topologicalClosure) :
    I ≤ M := by
  intro x hx
  have hFx : F x ∈ (Ideal.map β J).topologicalClosure := by
    rw [heff]
    exact Submodule.le_topologicalClosure _ (Ideal.mem_map_of_mem F hx)
  have hmem : F x ∈ retractIdeal ρ M := by
    refine (Ideal.map β J).topologicalClosure_minimal ?_ (isClosed_retractIdeal hρ hM) hFx
    apply Ideal.map_le_iff_le_comap.mpr
    intro q hq b
    exact retract_mul_mem_of_dense F β ρ hρ hmul M hM J hJ s w hw hdense hq b
  have h := retract_mem_of_mem_retractIdeal hmem
  rwa [hleft] at h

end Abstract

end StrictScalarIdealDescent

namespace PresentedAffinoidAlgebra.RationalChart

open StrictScalarIdealDescent

section Retraction

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  {L : Type v} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
  (ι : K →+* L) (hι : ∀ a, ‖ι a‖ = ‖a‖)
  {c : Fin A.arity → L} (hc : ∀ i, ‖c i‖ = A.polyradius i)
  (d : RationalChart K A) {τ : Fin d.arity → L} (hτ : ∀ j, ‖τ j‖ = d.radii j)
  (π : L →+ K) (hπ : ∀ a x, π (ι a * x) = a * π x)
  {D : ℝ} (hD : 0 ≤ D) (hπD : ∀ x, ‖π x‖ ≤ D * ‖x‖)

/-- The normalized strict map over the strict scalar extension of the base. -/
abbrev scalarNormalizedStrictMap :
    BoundedRingHom d.algebra (d.scalarNormalizedStrict ι hι hc hτ).algebra :=
  d.normalizedStrictMap (strictBaseChange A ι hι hc) (strictBaseChangeBoundedHom A ι hι hc)
    (norm_strictBaseChangeHom_le A ι hι hc) τ hτ

theorem scalarNormalizedStrictMap_baseMap (a : A) :
    d.scalarNormalizedStrictMap ι hι hc hτ (d.baseMap a) =
      (d.scalarNormalizedStrict ι hι hc hτ).baseMap (strictBaseChangeHom A ι hι hc a) :=
  d.normalizedStrictMap_baseMap _ _ _ _ _ a

/-- The scalar retraction is linear over the normalized strict map. -/
theorem scalarRetraction_scalarNormalizedStrictMap_mul (a : d.algebra)
    (b : (d.scalarNormalizedStrict ι hι hc hτ).algebra) :
    d.scalarRetraction ι hι hc hτ π hπ hD hπD (d.scalarNormalizedStrictMap ι hι hc hτ a * b) =
      a * d.scalarRetraction ι hι hc hτ π hπ hD hπD b := by
  have h := congrArg
    (fun f : BoundedRingHom d.algebra (d.rawStrictScalarExtension ι hι hc hτ) => f a)
    (d.scalarComparison_comp_map ι hι hc hτ (d.scalarNormalizedStrictMap ι hι hc hτ)
      (d.scalarNormalizedStrictMap_baseMap ι hι hc hτ))
  change d.scalarComparison ι hι hc hτ (d.scalarNormalizedStrictMap ι hι hc hτ a) =
    strictBaseChangeHom d.algebra ι hι (Adjoin.norm_addCases A d.radii hc hτ) a at h
  change strictBaseChangeRetraction d.algebra ι hι (Adjoin.norm_addCases A d.radii hc hτ)
      π hπ hD hπD
      (d.scalarComparison ι hι hc hτ (d.scalarNormalizedStrictMap ι hι hc hτ a * b)) =
    a * strictBaseChangeRetraction d.algebra ι hι (Adjoin.norm_addCases A d.radii hc hτ)
      π hπ hD hπD (d.scalarComparison ι hι hc hτ b)
  rw [map_mul, h]
  exact strictBaseChangeRetraction_strictBaseChangeHom_mul d.algebra ι hι
    (Adjoin.norm_addCases A d.radii hc hτ) π hπ hD hπD a _

omit [CompleteSpace K] in
/-- The scalar retraction is continuous: it is a bounded additive map after the
bounded comparison. -/
theorem continuous_scalarRetraction :
    Continuous (d.scalarRetraction ι hι hc hτ π hπ hD hπD) :=
  (AddMonoidHomClass.continuous_of_bound
    (strictBaseChangeRetraction d.algebra ι hι (Adjoin.norm_addCases A d.radii hc hτ)
      π hπ hD hπD) D
    (norm_strictBaseChangeRetraction_le d.algebra ι hι (Adjoin.norm_addCases A d.radii hc hτ)
      π hπ hD hπD)).comp (d.scalarComparison ι hι hc hτ).continuous

/-- The image of the original denominator has an inverse after normalization. -/
theorem exists_scalarNormalizedStrictMap_mul_denominator :
    ∃ w : d.algebra, d.scalarNormalizedStrictMap ι hι hc hτ w *
      (d.scalarNormalizedStrict ι hι hc hτ).baseMap
        (d.scalarNormalizedStrict ι hι hc hτ).denominator = 1 := by
  obtain ⟨w, hw'⟩ : ∃ w : d.algebra, w * d.baseMap (presentationMap K A d.denominator) = 1 :=
    (RationalPresentation.isUnit_baseMap_denominator K A d.radii
      d.denominator d.numerators d.generates).exists_left_inv
  refine ⟨w, ?_⟩
  have h := congrArg (d.scalarNormalizedStrictMap ι hι hc hτ) hw'
  rw [map_mul, map_one, d.scalarNormalizedStrictMap_baseMap] at h
  exact h

/-- The core local descent: the original local ideal lies in every closed ideal
containing the descended base retractions of the strict global ideal. -/
theorem le_of_scalarNormalizedStrict_effective (hπ1 : π 1 = 1) (I M : Ideal d.algebra)
    (hM : IsClosed (M : Set d.algebra)) (J : Ideal (strictBaseChange A ι hι hc))
    (hJ : ∀ q ∈ J, d.baseMap (strictBaseChangeRetraction A ι hι hc π hπ hD hπD q) ∈ M)
    (heff : (d.scalarNormalizedStrict ι hι hc hτ).baseMap.closedIdealMap J =
      (Ideal.map (d.scalarNormalizedStrictMap ι hι hc hτ).toRingHom I).topologicalClosure) :
    I ≤ M := by
  obtain ⟨w, hw⟩ := d.exists_scalarNormalizedStrictMap_mul_denominator ι hι hc hτ
  exact le_of_closure_map_eq (d.scalarNormalizedStrictMap ι hι hc hτ).toRingHom
    (d.scalarNormalizedStrict ι hι hc hτ).baseMap.toAlgHom.toRingHom
    (d.scalarRetraction ι hι hc hτ π hπ hD hπD)
    (d.continuous_scalarRetraction ι hι hc hτ π hπ hD hπD)
    (d.scalarRetraction_scalarNormalizedStrictMap_mul ι hι hc hτ π hπ hD hπD)
    (d.scalarRetraction_map ι hι hc hτ π hπ hD hπD hπ1
      (d.scalarNormalizedStrictMap ι hι hc hτ) (d.scalarNormalizedStrictMap_baseMap ι hι hc hτ))
    I M hM J
    (fun q hq => by
      change d.scalarRetraction ι hι hc hτ π hπ hD hπD
        ((d.scalarNormalizedStrict ι hι hc hτ).baseMap q) ∈ M
      rw [d.scalarRetraction_baseMap]
      exact hJ q hq)
    (d.scalarNormalizedStrict ι hι hc hτ).denominator w hw
    (StrictTestDomain.RationalData.dense_fractionSubalgebra
      (d.scalarNormalizedStrict ι hι hc hτ))
    heff

end Retraction

section Overlap

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  {L : Type v} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
  (d e : RationalChart K A) (Q : PresentedStrictAffinoidAlgebra L)
  (ψ : BoundedRingHom A Q) (hψ : ∀ a, ‖ψ a‖ ≤ ‖a‖)
  {τ : Fin d.arity → L} (hτ : ∀ j, ‖τ j‖ = d.radii j)
  {τ' : Fin e.arity → L} (hτ' : ∀ j, ‖τ' j‖ = e.radii j)
  {υ : Fin (d.inter e).arity → L} (hυ : ∀ j, ‖υ j‖ = (d.inter e).radii j)

omit [CompleteSpace K] in
/-- The strict intersection of two normalized charts lies in the normalization
of their rational intersection chart; both loci are the inverse image of the
original intersection. -/
theorem normalizedStrict_inter_subset :
    ((d.normalizedStrict Q ψ τ hτ).inter (e.normalizedStrict Q ψ τ' hτ')).locus ⊆
      ((d.inter e).normalizedStrict Q ψ υ hυ).locus := by
  rw [StrictTestDomain.RationalData.locus_inter, normalizedStrict_locus, normalizedStrict_locus,
    normalizedStrict_locus, locus_inter, Set.preimage_inter]

/-- The restriction from the full-domain intersection to the rational
intersection chart, which has the same locus. -/
def interChartInclusion : (d.inter e).toDomain ⟶ d.toDomain.inter e.toDomain :=
  Domain.inclusionOfSubset (d.inter e).toDomain (d.toDomain.inter e.toDomain)
    (locus_inter d e).le

/-- The strict restriction from the normalized intersection chart to the strict
intersection of the normalized charts. -/
def normalizedInterInclusion :
    (d.normalizedStrict Q ψ τ hτ).inter (e.normalizedStrict Q ψ τ' hτ') ⟶
      (d.inter e).normalizedStrict Q ψ υ hυ :=
  ⟨d.normalizedStrict_inter_subset e Q ψ hτ hτ' hυ⟩

/-- The original full-domain intersection maps to the strict intersection of the
normalized charts: restrict to the rational intersection chart, normalize it, and
restrict along the equal strict loci. -/
def scalarOverlapMap :
    BoundedRingHom (d.toDomain.inter e.toDomain).algebra
      ((d.normalizedStrict Q ψ τ hτ).inter (e.normalizedStrict Q ψ τ' hτ')).algebra :=
  (d.normalizedInterInclusion e Q ψ hτ hτ' hυ).restriction.toBoundedRingHom.comp
    (((d.inter e).normalizedStrictMap Q ψ hψ υ hυ).comp
      (d.interChartInclusion e).restriction.toBoundedRingHom)

theorem scalarOverlapMap_baseMap (a : A) :
    d.scalarOverlapMap e Q ψ hψ hτ hτ' hυ ((d.toDomain.inter e.toDomain).baseMap a) =
      ((d.normalizedStrict Q ψ τ hτ).inter (e.normalizedStrict Q ψ τ' hτ')).baseMap (ψ a) := by
  have h1 : (d.interChartInclusion e).restriction ((d.toDomain.inter e.toDomain).baseMap a) =
      (d.inter e).baseMap a :=
    congrArg (fun f : BoundedAlgHom K A (d.inter e).algebra => f a)
      (d.interChartInclusion e).comp_baseMap
  have h2 := congrArg (fun f : BoundedAlgHom L Q
      ((d.normalizedStrict Q ψ τ hτ).inter (e.normalizedStrict Q ψ τ' hτ')).algebra => f (ψ a))
    (d.normalizedInterInclusion e Q ψ hτ hτ' hυ).restriction_comp_baseMap
  change (d.normalizedInterInclusion e Q ψ hτ hτ' hυ).restriction
    ((d.inter e).normalizedStrictMap Q ψ hψ υ hυ
      ((d.interChartInclusion e).restriction ((d.toDomain.inter e.toDomain).baseMap a))) = _
  rw [h1, normalizedStrictMap_baseMap]
  exact h2

theorem scalarOverlapMap_interLeft :
    (d.scalarOverlapMap e Q ψ hψ hτ hτ' hυ).comp
        (d.toDomain.interLeft e.toDomain).restriction.toBoundedRingHom =
      (StrictTestDomain.RationalData.interLeft (d.normalizedStrict Q ψ τ hτ)
        (e.normalizedStrict Q ψ τ' hτ')).restriction.toBoundedRingHom.comp
        (d.normalizedStrictMap Q ψ hψ τ hτ) := by
  apply d.ringHom_ext_over_base _
    (((d.normalizedStrict Q ψ τ hτ).inter
      (e.normalizedStrict Q ψ τ' hτ')).baseMap.toBoundedRingHom.comp ψ)
    (fun a => (RationalLocalization.norm_baseMap_le L Q _ _ _ (ψ a)).trans (hψ a))
  · intro a
    have h1 : (d.toDomain.interLeft e.toDomain).restriction (d.baseMap a) =
        (d.toDomain.inter e.toDomain).baseMap a :=
      congrArg (fun f : BoundedAlgHom K A (d.toDomain.inter e.toDomain).algebra => f a)
        (d.toDomain.interLeft e.toDomain).comp_baseMap
    change d.scalarOverlapMap e Q ψ hψ hτ hτ' hυ
      ((d.toDomain.interLeft e.toDomain).restriction (d.baseMap a)) = _
    rw [h1]
    exact d.scalarOverlapMap_baseMap e Q ψ hψ hτ hτ' hυ a
  · intro a
    change (StrictTestDomain.RationalData.interLeft (d.normalizedStrict Q ψ τ hτ)
      (e.normalizedStrict Q ψ τ' hτ')).restriction
        (d.normalizedStrictMap Q ψ hψ τ hτ (d.baseMap a)) = _
    rw [normalizedStrictMap_baseMap]
    exact congrArg (fun f : BoundedAlgHom L Q
        ((d.normalizedStrict Q ψ τ hτ).inter (e.normalizedStrict Q ψ τ' hτ')).algebra =>
          f (ψ a))
      (StrictTestDomain.RationalData.interLeft (d.normalizedStrict Q ψ τ hτ)
        (e.normalizedStrict Q ψ τ' hτ')).restriction_comp_baseMap

theorem scalarOverlapMap_interRight :
    (d.scalarOverlapMap e Q ψ hψ hτ hτ' hυ).comp
        (d.toDomain.interRight e.toDomain).restriction.toBoundedRingHom =
      (StrictTestDomain.RationalData.interRight (d.normalizedStrict Q ψ τ hτ)
        (e.normalizedStrict Q ψ τ' hτ')).restriction.toBoundedRingHom.comp
        (e.normalizedStrictMap Q ψ hψ τ' hτ') := by
  apply e.ringHom_ext_over_base _
    (((d.normalizedStrict Q ψ τ hτ).inter
      (e.normalizedStrict Q ψ τ' hτ')).baseMap.toBoundedRingHom.comp ψ)
    (fun a => (RationalLocalization.norm_baseMap_le L Q _ _ _ (ψ a)).trans (hψ a))
  · intro a
    have h1 : (d.toDomain.interRight e.toDomain).restriction (e.baseMap a) =
        (d.toDomain.inter e.toDomain).baseMap a :=
      congrArg (fun f : BoundedAlgHom K A (d.toDomain.inter e.toDomain).algebra => f a)
        (d.toDomain.interRight e.toDomain).comp_baseMap
    change d.scalarOverlapMap e Q ψ hψ hτ hτ' hυ
      ((d.toDomain.interRight e.toDomain).restriction (e.baseMap a)) = _
    rw [h1]
    exact d.scalarOverlapMap_baseMap e Q ψ hψ hτ hτ' hυ a
  · intro a
    change (StrictTestDomain.RationalData.interRight (d.normalizedStrict Q ψ τ hτ)
      (e.normalizedStrict Q ψ τ' hτ')).restriction
        (e.normalizedStrictMap Q ψ hψ τ' hτ' (e.baseMap a)) = _
    rw [normalizedStrictMap_baseMap]
    exact congrArg (fun f : BoundedAlgHom L Q
        ((d.normalizedStrict Q ψ τ hτ).inter (e.normalizedStrict Q ψ τ' hτ')).algebra =>
          f (ψ a))
      (StrictTestDomain.RationalData.interRight (d.normalizedStrict Q ψ τ hτ)
        (e.normalizedStrict Q ψ τ' hτ')).restriction_comp_baseMap

include hυ in
/-- Compatibility of closed local extensions on the original full-domain
intersection gives compatibility of the closed normalized extensions on the
strict intersection. -/
theorem normalizedStrict_closedIdealMap_compatible (Id : Ideal d.algebra) (Ie : Ideal e.algebra)
    (h : (d.toDomain.interLeft e.toDomain).restriction.closedIdealMap Id =
      (d.toDomain.interRight e.toDomain).restriction.closedIdealMap Ie) :
    (StrictTestDomain.RationalData.interLeft (d.normalizedStrict Q ψ τ hτ)
        (e.normalizedStrict Q ψ τ' hτ')).restriction.closedIdealMap
      (Ideal.map (d.normalizedStrictMap Q ψ hψ τ hτ).toRingHom Id).topologicalClosure =
    (StrictTestDomain.RationalData.interRight (d.normalizedStrict Q ψ τ hτ)
        (e.normalizedStrict Q ψ τ' hτ')).restriction.closedIdealMap
      (Ideal.map (e.normalizedStrictMap Q ψ hψ τ' hτ').toRingHom Ie).topologicalClosure :=
  closure_map_compatible
    (d.toDomain.interLeft e.toDomain).restriction.toAlgHom.toRingHom
    (d.toDomain.interRight e.toDomain).restriction.toAlgHom.toRingHom
    (d.normalizedStrictMap Q ψ hψ τ hτ).toRingHom
    (e.normalizedStrictMap Q ψ hψ τ' hτ').toRingHom
    (StrictTestDomain.RationalData.interLeft (d.normalizedStrict Q ψ τ hτ)
      (e.normalizedStrict Q ψ τ' hτ')).restriction.toAlgHom.toRingHom
    (StrictTestDomain.RationalData.interRight (d.normalizedStrict Q ψ τ hτ)
      (e.normalizedStrict Q ψ τ' hτ')).restriction.toAlgHom.toRingHom
    (d.scalarOverlapMap e Q ψ hψ hτ hτ' hυ).toRingHom
    (BoundedAlgHom.continuous _) (BoundedAlgHom.continuous _)
    (continuous_boundedRingHom _)
    (congrArg BoundedRingHom.toRingHom (d.scalarOverlapMap_interLeft e Q ψ hψ hτ hτ' hυ)).symm
    (congrArg BoundedRingHom.toRingHom (d.scalarOverlapMap_interRight e Q ψ hψ hτ hτ' hυ)).symm
    Id Ie h

end Overlap

end PresentedAffinoidAlgebra.RationalChart

namespace PresentedAffinoidAlgebra.Domain.FiniteCover

/-- Rational ideal effectiveness for one realization of all base, chart and
overlap radii in a complete nontrivially normed extension with a bounded
coefficient retraction. -/
theorem rationalIdealEffective_of_realization
    (hS : StrictRationalIdealEffectivenessStatement.{u})
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {A : PresentedAffinoidAlgebra K} {n : ℕ} (D : Fin n → RationalChart K A)
    (hD : ∀ x : BanachSpectrum A, ∃ i, x ∈ (D i).locus)
    (I : ∀ i : Fin n, Ideal (D i).algebra) (hIc : ∀ i, IsClosed (I i : Set (D i).algebra))
    (hcompat : (ofRationalCharts D hD).IdealCompatible I)
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (hL : ∃ x : L, 1 < ‖x‖) (ι : K →+* L) (hι : ∀ a, ‖ι a‖ = ‖a‖)
    {c : Fin A.arity → L} (hc : ∀ j, ‖c j‖ = A.polyradius j)
    {τ : ∀ j, Fin (D j).arity → L} (hτ : ∀ j k, ‖τ j k‖ = (D j).radii k)
    {υ : ∀ p : Fin n × Fin n, Fin ((D p.1).inter (D p.2)).arity → L}
    (hυ : ∀ p k, ‖υ p k‖ = ((D p.1).inter (D p.2)).radii k)
    (π : L →+ K) (hπ : ∀ a x, π (ι a * x) = a * π x) (hπ1 : π 1 = 1)
    {B : ℝ} (hB : 0 < B) (hπB : ∀ x, ‖π x‖ ≤ B * ‖x‖) (i : Fin n) :
    (D i).baseMap.closedIdealMap ((ofRationalCharts D hD).idealContraction I) = I i := by
  have hψ : ∀ a, ‖strictBaseChangeBoundedHom A ι hι hc a‖ ≤ ‖a‖ :=
    norm_strictBaseChangeHom_le A ι hι hc
  let δ : Fin n → StrictTestDomain.RationalData L (strictBaseChange A ι hι hc) :=
    fun j => (D j).scalarNormalizedStrict ι hι hc (hτ j)
  let I' : ∀ j, Ideal (δ j).algebra := fun j =>
    (Ideal.map ((D j).scalarNormalizedStrictMap ι hι hc (hτ j)).toRingHom
      (I j)).topologicalClosure
  have hI'c : ∀ j, IsClosed (I' j : Set (δ j).algebra) :=
    fun j => Submodule.isClosed_topologicalClosure _
  have hδ : ∀ x : BanachSpectrum (strictBaseChange A ι hι hc), ∃ j, x ∈ (δ j).locus :=
    RationalChart.normalizedStrict_cover (strictBaseChange A ι hι hc)
      (strictBaseChangeBoundedHom A ι hι hc) D τ hτ hD
  have hcompat' : ∀ j k,
      (StrictTestDomain.RationalData.interLeft (δ j) (δ k)).restriction.closedIdealMap
          (I' j) =
        (StrictTestDomain.RationalData.interRight (δ j) (δ k)).restriction.closedIdealMap
          (I' k) := fun j k =>
    RationalChart.normalizedStrict_closedIdealMap_compatible (D j) (D k)
      (strictBaseChange A ι hι hc) (strictBaseChangeBoundedHom A ι hι hc) hψ
      (hτ j) (hτ k) (hυ (j, k)) (I j) (I k) (hcompat j k)
  have heff := hS L hL (strictBaseChange A ι hι hc) n δ hδ I' hI'c hcompat'
  have hRJ : ∀ q ∈ ⨅ j, Ideal.comap (δ j).baseMap.toAlgHom.toRingHom (I' j),
      strictBaseChangeRetraction A ι hι hc π hπ hB.le hπB q ∈
        (ofRationalCharts D hD).idealContraction I := by
    intro q hq
    refine ((ofRationalCharts D hD).mem_idealContraction I _).mpr fun j => ?_
    have h1 : (δ j).baseMap q ∈ I' j := Ideal.mem_iInf.mp hq j
    have h2 := StrictScalarIdealDescent.retract_mem_of_mem_closure_map
      ((D j).scalarNormalizedStrictMap ι hι hc (hτ j)).toRingHom
      ((D j).scalarRetraction ι hι hc (hτ j) π hπ hB.le hπB)
      ((D j).continuous_scalarRetraction ι hι hc (hτ j) π hπ hB.le hπB)
      ((D j).scalarRetraction_scalarNormalizedStrictMap_mul ι hι hc (hτ j) π hπ hB.le hπB)
      (I j) (hIc j) h1
    rw [RationalChart.scalarRetraction_baseMap] at h2
    exact h2
  apply le_antisymm ((ofRationalCharts D hD).closedIdealMap_idealContraction_le I hIc i)
  exact (D i).le_of_scalarNormalizedStrict_effective ι hι hc (hτ i) π hπ hB.le hπB hπ1
    (I i) _ ((D i).baseMap.isClosed_closedIdealMap _) _
    (fun q hq => (D i).baseMap.mem_closedIdealMap (hRJ q hq)) (heff i)

/-- The strict nontrivially valued rational theorem implies the general
positive-polyradius rational theorem over every complete ultrametric field. -/
theorem strictScalarIdealDescent : StrictScalarIdealDescentStatement.{u} := by
  intro hS K _ _ _ A n D hD I hIc hcompat i
  let D' : Fin n ⊕ (Fin n × Fin n) → RationalChart K A :=
    Sum.elim D fun p => (D p.1).inter (D p.2)
  let t : RationalChart.FamilyRadiusIndex D' ⊕ Unit → ℝ :=
    Sum.elim (RationalChart.familyRadius D') fun _ => 2
  have ht : ∀ s, 0 < t s := by
    rintro (s | s)
    · exact RationalChart.familyRadius_pos D' s
    · exact two_pos
  obtain ⟨⟨L, ι, hι, cc, hcc, π, hπ, hπ1, B, hB, hπB⟩⟩ :=
    FiniteRadiusRealization.nonempty (K := K) t ht
  have hL : ∃ x : L, 1 < ‖x‖ := by
    refine ⟨cc (Sum.inr ()), ?_⟩
    rw [hcc]
    show (1 : ℝ) < 2
    norm_num
  exact rationalIdealEffective_of_realization hS D hD I hIc hcompat hL ι hι
    (c := fun j => cc (Sum.inl (Sum.inl j))) (fun j => hcc _)
    (τ := fun j k => cc (Sum.inl (Sum.inr ⟨Sum.inl j, k⟩))) (fun j k => hcc _)
    (υ := fun p k => cc (Sum.inl (Sum.inr ⟨Sum.inr p, k⟩))) (fun p k => hcc _)
    π hπ hπ1 hB hπB i

end PresentedAffinoidAlgebra.Domain.FiniteCover

end Langlands.Analytic
