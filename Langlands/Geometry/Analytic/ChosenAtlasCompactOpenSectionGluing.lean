import Langlands.Geometry.Analytic.ChosenAtlasCompactOpenSectionAction
import Langlands.Geometry.Analytic.ChosenAtlasLocallyConstantGluingAction

/-! # Coefficients and finite simultaneous stabilizers for actual sheaf glue -/

noncomputable section

universe u v w z t r

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory Set IndexedAffinoidAtlas.OriginalChartDomain
open scoped Pointwise

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : AffinoidAtlasPresentation.{u, v, w} K} {D E : Type z}

namespace CompactOpenOriginalDomainSection

/-- Arbitrary coefficient postcomposition on all compact-open section pairs. -/
def map (φ : D → E) (s : CompactOpenOriginalDomainSection A D) :
    CompactOpenOriginalDomainSection A E :=
  ⟨OriginalDomainSection.map φ s.toOriginalDomainSection,
    s.isCompact_domain, s.isOpen_domain⟩

@[simp]
theorem map_pair (φ : D → E) (s : CompactOpenOriginalDomainSection A D) :
    (map φ s).toOriginalDomainSection =
      OriginalDomainSection.map φ s.toOriginalDomainSection := rfl

@[simp]
theorem map_id (s : CompactOpenOriginalDomainSection A D) : map id s = s := by
  apply ext
  exact OriginalDomainSection.map_id _

theorem map_comp {F : Type z} (φ : D → E) (ψ : E → F)
    (s : CompactOpenOriginalDomainSection A D) :
    map (ψ ∘ φ) s = map ψ (map φ s) := by
  apply ext
  exact OriginalDomainSection.map_comp φ ψ _

end CompactOpenOriginalDomainSection

namespace ChosenAtlasSectionAction

variable {G : Type t} [Group G]
  (X : Action (AffinoidAtlasPresentation.{u, v, w} K) G)

local instance : MulAction G X.V.space :=
  inferInstanceAs (MulAction G
    ((forget₂ (Action TopCat.{v} G) TopCat.{v}).obj
      ((spaceFunctor.mapAction G).obj X)))

local instance (S : X.V.atlas.OriginalChartDomain) :
    MulAction (domainStabilizer X S) S :=
  inferInstanceAs (MulAction (MulAction.stabilizer G (S : Set X.V.space))
    (S : Set X.V.space))

local instance (S : X.V.atlas.OriginalChartDomain) :
    ContinuousConstSMul (domainStabilizer X S) S where
  continuous_const_smul g :=
    ((X.ρ (g : G)).baseMap.continuous.comp continuous_subtype_val).subtype_mk _

theorem compactOpen_smul_map (φ : D → E) (g : G)
    (s : CompactOpenOriginalDomainSection X.V D) :
    g • CompactOpenOriginalDomainSection.map φ s =
      CompactOpenOriginalDomainSection.map φ (g • s) := by
  apply CompactOpenOriginalDomainSection.ext
  exact OriginalDomainSection.transport_map (X.ρAut g) φ _

variable [TopologicalSpace G] [IsTopologicalGroup G]
  (hX : Continuous (fun p : G × X.V.space => (X.ρ p.1).baseMap p.2))

/-- Coefficient postcomposition is an actual continuous equivariant morphism. -/
def compactOpenCoefficientMap (φ : D → E) :
    compactOpenAction X hX D ⟶ compactOpenAction X hX E :=
  ObjectProperty.homMk
    { hom := TopCat.ofHom ⟨CompactOpenOriginalDomainSection.map φ,
        continuous_of_discreteTopology⟩
      comm g := by
        apply TopCat.ext
        intro s
        exact compactOpen_smul_map X φ g s }

/-- The full compact-open section actions vary functorially in coefficients. -/
def compactOpenCoefficientFunctor : Type z ⥤ ContAction TopCat.{max v z} G where
  obj D := compactOpenAction X hX D
  map φ := compactOpenCoefficientMap X hX (fun x => φ x)
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply TopCat.ext
    intro s
    exact CompactOpenOriginalDomainSection.map_id s
  map_comp φ ψ := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply TopCat.ext
    intro s
    exact CompactOpenOriginalDomainSection.map_comp (fun x => φ x) (fun x => ψ x) s

/-- The entire section-pair stabilizer, as a constructed open subgroup. -/
def compactOpenSectionOpenStabilizer (s : CompactOpenOriginalDomainSection X.V D) :
    OpenSubgroup G :=
  ⟨MulAction.stabilizer G s, compactOpen_stabilizer_isOpen X hX s⟩

/-- A prescribed open subgroup refined by every full stabilizer in a finite
family of complete local domain-section pairs. -/
def finiteSectionOpenStabilizer {ι : Type r} [Finite ι]
    (U : OpenSubgroup G) (s : ι → CompactOpenOriginalDomainSection X.V D) :
    OpenSubgroup G :=
  U ⊓ OpenSubgroup.iInfOfFinite (fun i => compactOpenSectionOpenStabilizer X hX (s i))

@[simp]
theorem mem_finiteSectionOpenStabilizer {ι : Type r} [Finite ι]
    (U : OpenSubgroup G) (s : ι → CompactOpenOriginalDomainSection X.V D) (g : G) :
    g ∈ finiteSectionOpenStabilizer X hX U s ↔ g ∈ U ∧ ∀ i, g • s i = s i := by
  change (g ∈ U ∧ g ∈ (⨅ i, (compactOpenSectionOpenStabilizer X hX (s i)).toSubgroup)) ↔ _
  simp only [Subgroup.mem_iInf]
  rfl

theorem finiteSectionOpenStabilizer_le {ι : Type r} [Finite ι]
    (U : OpenSubgroup G) (s : ι → CompactOpenOriginalDomainSection X.V D) :
    finiteSectionOpenStabilizer X hX U s ≤ U := inf_le_left

/-- Every simultaneous original stabilizer also fixes all coefficient-mapped
pairs, with the prescribed subgroup retained. -/
theorem finiteSectionOpenStabilizer_map_le {ι : Type r} [Finite ι]
    (U : OpenSubgroup G) (s : ι → CompactOpenOriginalDomainSection X.V D)
    (φ : D → E) :
    finiteSectionOpenStabilizer X hX U s ≤
      finiteSectionOpenStabilizer X hX U
        (fun i => CompactOpenOriginalDomainSection.map φ (s i)) := by
  intro g hg
  obtain ⟨hU, hs⟩ := (mem_finiteSectionOpenStabilizer X hX U s g).mp hg
  apply (mem_finiteSectionOpenStabilizer X hX U _ g).mpr
  refine ⟨hU, fun i => ?_⟩
  rw [compactOpen_smul_map, hs i]

section FiniteSieve

variable {S : X.V.atlas.OriginalChartDomain} {R : Sieve S}
  (p : Presieve.FamilyOfElements (locallyConstantPresheaf X.V.atlas D) R.arrows)
  (hp : p.Compatible) (hR : IsCovering R)
  {ι : Type r} [Finite ι]
  (T : ι → X.V.atlas.OriginalChartDomain) (f : ∀ i, T i ⟶ S)
  (hf : ∀ i, R (f i))
  (hC : ∀ i, IsCompact (T i : Set X.V.space))
  (hO : ∀ i, IsOpen (T i : Set X.V.space))
  (hcover : (⋃ i, (T i : Set X.V.space)) = (S : Set X.V.space))

/-- The selected local functions retain their entire actual domains. -/
def finiteSieveLocalSections (i : ι) : CompactOpenOriginalDomainSection X.V D :=
  ⟨⟨T i, (p (f i) (hf i) : LocallyConstant (T i) D)⟩, hC i, hO i⟩

/-- Compactness and openness of the target are derived from the finite
selected local domains, then attached to the actual arbitrary-sieve glue. -/
def finiteSieveGlue : CompactOpenOriginalDomainSection X.V D :=
  ⟨OriginalDomainSection.sieveGlue p hp hR,
    hcover ▸ isCompact_iUnion hC, hcover ▸ isOpen_iUnion hO⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The complete finite-cover glue pair commutes with coefficient
postcomposition and the full coefficient-mapped matching family. -/
theorem finiteSieveGlue_map (φ : D → E) :
    CompactOpenOriginalDomainSection.map φ
        (finiteSieveGlue X p hp hR T hC hO hcover) =
      finiteSieveGlue X (p.map (locallyConstantCoefficientMap φ))
        (hp.map (locallyConstantCoefficientMap φ)) hR T hC hO hcover := by
  apply CompactOpenOriginalDomainSection.ext
  exact OriginalDomainSection.sieveGlue_map p hp hR φ

/-- This open subgroup is constructed solely from the prescribed subgroup
and the finitely many selected local pairs. -/
def finiteSieveGlueOpenStabilizer (U : OpenSubgroup G) : OpenSubgroup G :=
  finiteSectionOpenStabilizer X hX U (finiteSieveLocalSections X p T f hf hC hO)

/-- The common local stabilizer fixes the actual whole glue. The source
sieve and its full matching family can be arbitrary. -/
theorem finiteSieveGlue_fixed (U : OpenSubgroup G) (g : G)
    (hg : g ∈ finiteSieveGlueOpenStabilizer X hX p T f hf hC hO U) :
    g • finiteSieveGlue X p hp hR T hC hO hcover =
      finiteSieveGlue X p hp hR T hC hO hcover := by
  have hlocals : ∀ i, g • finiteSieveLocalSections X p T f hf hC hO i =
      finiteSieveLocalSections X p T f hf hC hO i :=
    (mem_finiteSectionOpenStabilizer X hX U _ g).mp hg |>.2
  have hdomains (i : ι) :
      (isoOriginalDomain (X.ρAut g) (T i) : Set X.V.space) = (T i : Set X.V.space) :=
    congrArg (fun s : CompactOpenOriginalDomainSection X.V D =>
      (s.toOriginalDomainSection.domain : Set X.V.space)) (hlocals i)
  have hdomain : isoOriginalDomain (X.ρAut g) S = S := by
    apply SetLike.coe_injective
    change isoHomeomorph (X.ρAut g) '' (S : Set X.V.space) = (S : Set X.V.space)
    rw [← hcover, Set.image_iUnion]
    exact iUnion_congr hdomains
  apply CompactOpenOriginalDomainSection.ext
  apply OriginalDomainSection.ext
  · exact hdomain
  · intro x hx hs
    change x ∈ (S : Set X.V.space) at hs
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ hs)
    have hd : g ∈ domainStabilizer X (T i) :=
      (mem_domainStabilizer X (T i) g).mpr (SetLike.coe_injective (hdomains i))
    let k : domainStabilizer X (T i) := ⟨g, hd⟩
    let q : CompactAction.DiscreteLocallyConstant (T i) D :=
      ⟨(p (f i) (hf i) : LocallyConstant (T i) D)⟩
    have hpair : ((action X D).ρ g).hom
        (⟨T i, q.toLocallyConstant⟩ : OriginalDomainSection X.V D) =
          ⟨T i, q.toLocallyConstant⟩ :=
      congrArg CompactOpenOriginalDomainSection.toOriginalDomainSection (hlocals i)
    have hq : k • q = q := by
      apply CompactAction.DiscreteLocallyConstant.equiv.injective
      change (k • q).toLocallyConstant = q.toLocallyConstant
      have he := (action_domain_section_pair X (T i) k q).symm.trans hpair
      injection he
    let y : T i := ⟨x, hi⟩
    have hvalue := congrArg (fun a : CompactAction.DiscreteLocallyConstant (T i) D =>
      a y) hq
    exact (locallyConstantSieveGlue_apply p hp hR (f i) (hf i) (k⁻¹ • y)).trans
      (hvalue.trans (locallyConstantSieveGlue_apply p hp hR (f i) (hf i) y).symm)

/-- The constructed common local open subgroup lies in the entire glue
stabilizer, without a supplied global fixedness condition. -/
theorem finiteSieveGlueOpenStabilizer_le (U : OpenSubgroup G) :
    (finiteSieveGlueOpenStabilizer X hX p T f hf hC hO U).toSubgroup ≤
      MulAction.stabilizer G (finiteSieveGlue X p hp hR T hC hO hcover) := by
  intro g hg
  exact finiteSieveGlue_fixed X hX p hp hR T f hf hC hO hcover U g hg

end FiniteSieve

end ChosenAtlasSectionAction

end Langlands.Analytic.AffinoidAtlasPresentation
