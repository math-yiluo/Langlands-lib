import Langlands.Geometry.Analytic.ChosenAtlasLocallyConstantAction
import Langlands.Topology.GroupAction.CompactLocallyConstantAction
import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer

/-! # Compact-open original domains and continuous section actions -/

noncomputable section

universe u v w z t

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set Topology Filter CompactAction
open scoped Pointwise

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type t} [Group G]
  (X : Action (AffinoidAtlasPresentation.{u, v, w} K) G)

/-- Every original-domain section whose actual domain is compact and open. -/
structure CompactOpenOriginalDomainSection
    (A : AffinoidAtlasPresentation.{u, v, w} K) (D : Type z) where
  toOriginalDomainSection : OriginalDomainSection A D
  isCompact_domain : IsCompact (toOriginalDomainSection.domain : Set A.space)
  isOpen_domain : IsOpen (toOriginalDomainSection.domain : Set A.space)

namespace CompactOpenOriginalDomainSection

variable {A : AffinoidAtlasPresentation.{u, v, w} K} {D : Type z}

@[ext]
theorem ext {s r : CompactOpenOriginalDomainSection A D}
    (h : s.toOriginalDomainSection = r.toOriginalDomainSection) : s = r := by
  cases s
  cases r
  cases h
  rfl

instance : TopologicalSpace (CompactOpenOriginalDomainSection A D) := ⊥

instance : DiscreteTopology (CompactOpenOriginalDomainSection A D) := ⟨rfl⟩

end CompactOpenOriginalDomainSection

namespace ChosenAtlasSectionAction

/-- The original pair action preserves compactness and openness through the
actual base homeomorphisms. -/
instance compactOpenMulAction (D : Type z) :
    MulAction G (CompactOpenOriginalDomainSection X.V D) where
  smul g s :=
    { toOriginalDomainSection := ((action X D).ρ g).hom s.toOriginalDomainSection
      isCompact_domain := s.isCompact_domain.image (isoHomeomorph (X.ρAut g)).continuous
      isOpen_domain := (isoHomeomorph (X.ρAut g)).isOpenMap _ s.isOpen_domain }
  one_smul s := by
    apply CompactOpenOriginalDomainSection.ext
    change OriginalDomainSection.transport (X.ρAut 1) s.toOriginalDomainSection = _
    rw [map_one]
    exact OriginalDomainSection.transport_refl _
  mul_smul g h s := by
    apply CompactOpenOriginalDomainSection.ext
    change OriginalDomainSection.transport (X.ρAut (g * h)) s.toOriginalDomainSection =
      OriginalDomainSection.transport (X.ρAut g)
        (OriginalDomainSection.transport (X.ρAut h) s.toOriginalDomainSection)
    rw [map_mul]
    exact OriginalDomainSection.transport_trans (X.ρAut h) (X.ρAut g) _

@[simp]
theorem compactOpen_smul_pair {D : Type z} (g : G)
    (s : CompactOpenOriginalDomainSection X.V D) :
    (g • s).toOriginalDomainSection =
      ((action X D).ρ g).hom s.toOriginalDomainSection := rfl

local instance : MulAction G X.V.space :=
  inferInstanceAs (MulAction G
    ((forget₂ (Action TopCat.{v} G) TopCat.{v}).obj
      ((spaceFunctor.mapAction G).obj X)))

/-- The full setwise stabilizer of the actual original-domain subset. -/
def domainStabilizer (S : X.V.atlas.OriginalChartDomain) : Subgroup G :=
  MulAction.stabilizer G (S : Set X.V.space)

theorem mem_domainStabilizer (S : X.V.atlas.OriginalChartDomain) (g : G) :
    g ∈ domainStabilizer X S ↔ isoOriginalDomain (X.ρAut g) S = S := by
  change g • (S : Set X.V.space) = (S : Set X.V.space) ↔ _
  constructor
  · exact fun h => SetLike.coe_injective h
  · exact fun h => congrArg (fun T : X.V.atlas.OriginalChartDomain =>
      (T : Set X.V.space)) h

local instance (S : X.V.atlas.OriginalChartDomain) :
    MulAction (domainStabilizer X S) S :=
  inferInstanceAs (MulAction (MulAction.stabilizer G (S : Set X.V.space))
    (S : Set X.V.space))

@[simp]
theorem domain_smul_val (S : X.V.atlas.OriginalChartDomain)
    (g : domainStabilizer X S) (x : S) :
    (g • x : S).val = (X.ρ (g : G)).baseMap x.val := rfl

local instance (S : X.V.atlas.OriginalChartDomain) :
    ContinuousConstSMul (domainStabilizer X S) S where
  continuous_const_smul g :=
    ((X.ρ (g : G)).baseMap.continuous.comp continuous_subtype_val).subtype_mk _

variable [TopologicalSpace G] [IsTopologicalGroup G]

local instance (S : X.V.atlas.OriginalChartDomain) :
    IsTopologicalGroup (domainStabilizer X S) :=
  Topology.IsInducing.subtypeVal.isTopologicalGroup
    (SubgroupClass.subtype (domainStabilizer X S))

omit [IsTopologicalGroup G] in
/-- The original joint point continuity restricts to the exact set stabilizer,
with the original subspace topologies on the group and the domain. -/
theorem continuous_domain_smul
    (hX : Continuous (fun p : G × X.V.space => (X.ρ p.1).baseMap p.2))
    (S : X.V.atlas.OriginalChartDomain) :
    Continuous (fun p : domainStabilizer X S × S => p.1 • p.2) := by
  have h : Continuous (fun p : domainStabilizer X S × S =>
      (X.ρ (p.1 : G)).baseMap (p.2 : X.V.space)) := hX.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
  exact h.subtype_mk _

/-- Compactness and openness of the actual subset construct an open setwise
stabilizer; no domain invariance is supplied. -/
theorem domainStabilizer_isOpen
    (hX : Continuous (fun p : G × X.V.space => (X.ρ p.1).baseMap p.2))
    (S : X.V.atlas.OriginalChartDomain)
    (hS : IsCompact (S : Set X.V.space)) (hO : IsOpen (S : Set X.V.space)) :
    IsOpen (domainStabilizer X S : Set G) := by
  have h : ∀ᶠ g in 𝓝 (1 : G), ∀ x ∈ (S : Set X.V.space), g • x ∈ S := by
    apply hS.eventually_forall_of_forall_eventually
    intro x hx
    apply (hO.preimage hX).mem_nhds
    simpa using hx
  have hi : ∀ᶠ g in 𝓝 (1 : G), ∀ x ∈ (S : Set X.V.space), g⁻¹ • x ∈ S := by
    have ht : Tendsto (fun g : G => g⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using continuous_inv.tendsto (1 : G)
    exact ht.eventually h
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  filter_upwards [h, hi] with g hg hgi
  change g • (S : Set X.V.space) = (S : Set X.V.space)
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hg x hx
  · intro x hx
    exact ⟨g⁻¹ • x, hgi x hx, smul_inv_smul g x⟩

/-- The open subgroup is the entire setwise stabilizer, not a chosen subgroup. -/
def domainOpenStabilizer
    (hX : Continuous (fun p : G × X.V.space => (X.ρ p.1).baseMap p.2))
    (S : X.V.atlas.OriginalChartDomain)
    (hS : IsCompact (S : Set X.V.space)) (hO : IsOpen (S : Set X.V.space)) :
    OpenSubgroup G :=
  ⟨domainStabilizer X S, domainStabilizer_isOpen X hX S hS hO⟩

/-- The entire discrete function space of a compact original domain has a
jointly continuous action of its exact setwise stabilizer. -/
def domainLocallyConstantAction
    (hX : Continuous (fun p : G × X.V.space => (X.ρ p.1).baseMap p.2))
    (S : X.V.atlas.OriginalChartDomain)
    (hS : IsCompact (S : Set X.V.space)) (D : Type z) :
    ContAction TopCat.{max v z} (domainStabilizer X S) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  letI : ContinuousSMul (domainStabilizer X S) S :=
    ⟨continuous_domain_smul X hX S⟩
  exact DiscreteLocallyConstant.continuousAction (X := S) (A := D)
    (domainStabilizer X S)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Fixed-domain inverse precomposition agrees with the existing action on
entire varying domain-section pairs. -/
theorem action_domain_section_pair
    (S : X.V.atlas.OriginalChartDomain) {D : Type z}
    (g : domainStabilizer X S) (f : DiscreteLocallyConstant S D) :
    ((action X D).ρ (g : G)).hom
        (⟨S, f.toLocallyConstant⟩ : OriginalDomainSection X.V D) =
      ⟨S, (g • f).toLocallyConstant⟩ := by
  apply OriginalDomainSection.ext
  · exact (mem_domainStabilizer X S g).mp g.property
  · intro x hs hr
    rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The full varying-pair stabilizer is the image of the full fixed-domain
function stabilizer in the exact domain stabilizer. -/
theorem sectionStabilizer_eq_image {D : Type z} (s : OriginalDomainSection X.V D) :
    {g : G | ((action X D).ρ g).hom s = s} =
      Subtype.val '' (MulAction.stabilizer (domainStabilizer X s.domain)
        (⟨s.value⟩ : DiscreteLocallyConstant s.domain D) :
          Set (domainStabilizer X s.domain)) := by
  rcases s with ⟨S, value⟩
  ext g
  constructor
  · intro hg
    have hd : g ∈ domainStabilizer X S :=
      (mem_domainStabilizer X S g).mpr
        (congrArg OriginalDomainSection.domain hg)
    let k : domainStabilizer X S := ⟨g, hd⟩
    let f : DiscreteLocallyConstant S D := ⟨value⟩
    refine ⟨k, ?_, rfl⟩
    change k • f = f
    have hp := (action_domain_section_pair X S k f).symm.trans hg
    have hv : (k • f).toLocallyConstant = f.toLocallyConstant := by
      injection hp
    exact DiscreteLocallyConstant.equiv.injective hv
  · rintro ⟨k, hk, rfl⟩
    have hp := action_domain_section_pair X S k
      (⟨value⟩ : DiscreteLocallyConstant S D)
    change k • (⟨value⟩ : DiscreteLocallyConstant S D) =
      (⟨value⟩ : DiscreteLocallyConstant S D) at hk
    change ((action X D).ρ (k : G)).hom ⟨S, value⟩ = ⟨S, value⟩
    rw [hk] at hp
    exact hp

/-- Compact-open domain and compact function stabilizers together make the
entire varying-pair stabilizer open in the original group. -/
theorem compactOpen_stabilizer_isOpen
    (hX : Continuous (fun p : G × X.V.space => (X.ρ p.1).baseMap p.2))
    {D : Type z} (s : CompactOpenOriginalDomainSection X.V D) :
    IsOpen (MulAction.stabilizer G s : Set G) := by
  let S := s.toOriginalDomainSection.domain
  have : CompactSpace S := isCompact_iff_compactSpace.mp s.isCompact_domain
  have : ContinuousSMul (domainStabilizer X S) S :=
    ⟨continuous_domain_smul X hX S⟩
  have hpair : (MulAction.stabilizer G s : Set G) =
      {g : G | ((action X D).ρ g).hom s.toOriginalDomainSection =
        s.toOriginalDomainSection} := by
    ext g
    exact ⟨fun h => congrArg CompactOpenOriginalDomainSection.toOriginalDomainSection h,
      fun h => CompactOpenOriginalDomainSection.ext h⟩
  rw [hpair, sectionStabilizer_eq_image]
  apply (domainStabilizer_isOpen X hX S s.isCompact_domain
    s.isOpen_domain).isOpenMap_subtype_val
  rw [DiscreteLocallyConstant.stabilizer_eq]
  exact functionStabilizer_isOpen (domainStabilizer X S)
    s.toOriginalDomainSection.value

/-- Joint continuity on the full discrete type of compact-open domain-section
pairs, for the original topology on the group. -/
theorem continuous_compactOpen_smul
    (hX : Continuous (fun p : G × X.V.space => (X.ρ p.1).baseMap p.2))
    (D : Type z) :
    Continuous (fun p : G × CompactOpenOriginalDomainSection X.V D => p.1 • p.2) := by
  have : ContinuousSMul G (CompactOpenOriginalDomainSection X.V D) :=
    continuousSMul_iff_stabilizer_isOpen.mpr (compactOpen_stabilizer_isOpen X hX)
  exact continuous_smul

/-- The complete compact-open section-pair action as an actual continuous
action object. -/
def compactOpenAction
    (hX : Continuous (fun p : G × X.V.space => (X.ρ p.1).baseMap p.2))
    (D : Type z) : ContAction TopCat.{max v z} G :=
  ⟨{ V := TopCat.of (CompactOpenOriginalDomainSection X.V D)
     ρ :=
       { toFun g := TopCat.ofHom ⟨fun s => g • s, continuous_of_discreteTopology⟩
         map_one' := by
           apply TopCat.ext
           intro s
           exact one_smul G s
         map_mul' g h := by
           apply TopCat.ext
           intro s
           exact mul_smul g h s } },
    (Action.isContinuous_def _).mpr (continuous_compactOpen_smul X hX D)⟩

end ChosenAtlasSectionAction

end Langlands.Analytic.AffinoidAtlasPresentation
