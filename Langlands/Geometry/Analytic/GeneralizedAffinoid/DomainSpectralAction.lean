import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralTopology
import Mathlib.Topology.Algebra.Group.Neighborhood

/-! # Continuous actions for the represented domain spectral topology -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism

open CategoryTheory
open scoped Topology

attribute [local instance] domainSpectralTopology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (P : PresentedAffinoidAlgebra K)

/-- The actual setwise represented-locus stabilizer, bundled as an open subgroup. -/
def domainLocusOpenSubgroup (d : Domain K P) :
    @OpenSubgroup (Aut P) _ (domainSpectralTopology P) where
  toSubgroup := locusStabilizer d
  isOpen' := isOpen_locusStabilizer P d

variable {G : Type v} [Group G] [TopologicalSpace G]

/-- Continuity into the represented domain spectral topology is exactly continuity of
every finite test at one. The index universe zero already supplies the full basis. -/
theorem continuous_domainSpectralTopology_iff [IsTopologicalGroup G] (ρ : G →* Aut P) :
    @Continuous G (Aut P) _ (domainSpectralTopology P) ρ ↔
      ∀ (ι : Type) (_ : Finite ι) (tests : ι → DomainSpectralTest K P),
        ρ ⁻¹' (finiteDomainSpectralSubgroup tests : Set (Aut P)) ∈ 𝓝 (1 : G) := by
  let := domainSpectralTopology P
  let := domainSpectralTopology_isTopologicalGroup P
  constructor
  · intro h ι hι tests
    have ht := finiteDomainSpectralSubgroup_mem_nhds_one P tests
    have hρ : Filter.Tendsto ρ (𝓝 (1 : G)) (𝓝 (1 : Aut P)) := by
      simpa only [map_one] using (h.continuousAt (x := (1 : G))).tendsto
    exact hρ ht
  · intro h
    apply continuous_of_tendsto_nhds_one ρ
    rw [Filter.tendsto_def]
    intro U hU
    obtain ⟨ι, hι, tests, hsub⟩ :=
      (mem_nhds_one_domainSpectralTopology P U).mp hU
    exact Filter.mem_of_superset (h ι hι tests) (Set.preimage_mono hsub)

/-- An action by actual bounded algebra automorphisms, continuous for the
represented domain spectral topology. Comparison with all compact analytic domains is separate. -/
structure DomainSpectralAction (G : Type v) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (P : PresentedAffinoidAlgebra K) where
  toMonoidHom : G →* Aut P
  continuous_toMonoidHom :
    @Continuous G (Aut P) _ (domainSpectralTopology P) toMonoidHom

namespace DomainSpectralAction

variable {P} [IsTopologicalGroup G]

/-- Construct a continuous represented-domain action by checking the finite tests at one. -/
def ofFiniteTests (ρ : G →* Aut P)
    (hρ : ∀ (ι : Type) (_ : Finite ι) (tests : ι → DomainSpectralTest K P),
      ρ ⁻¹' (finiteDomainSpectralSubgroup tests : Set (Aut P)) ∈ 𝓝 (1 : G)) :
    DomainSpectralAction G P :=
  ⟨ρ, (continuous_domainSpectralTopology_iff P ρ).mpr hρ⟩

/-- The trivial action is continuous. -/
def trivial : DomainSpectralAction G P :=
  ⟨1, continuous_const⟩

/-- Pull back a represented-domain action along a continuous homomorphism of groups. -/
def precomp {H : Type w} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (ρ : DomainSpectralAction G P) (f : H →* G) (hf : Continuous f) :
    DomainSpectralAction H P where
  toMonoidHom := ρ.toMonoidHom.comp f
  continuous_toMonoidHom := ρ.continuous_toMonoidHom.comp hf

/-- The inverse image of a finite test subgroup is an actual open subgroup of G.
Finite index types in every universe are allowed. -/
def testOpenSubgroup (ρ : DomainSpectralAction G P)
    {ι : Type w} [Finite ι] (tests : ι → DomainSpectralTest K P) :
    OpenSubgroup G where
  toSubgroup := (finiteDomainSpectralSubgroup tests).comap ρ.toMonoidHom
  isOpen' := (isOpen_finiteDomainSpectralSubgroup P tests).preimage
    ρ.continuous_toMonoidHom

@[simp] theorem mem_testOpenSubgroup (ρ : DomainSpectralAction G P)
    {ι : Type w} [Finite ι] (tests : ι → DomainSpectralTest K P) (g : G) :
    g ∈ ρ.testOpenSubgroup tests ↔
      ρ.toMonoidHom g ∈ finiteDomainSpectralSubgroup tests := Iff.rfl

/-- The subgroup of G preserving a fixed represented locus is open. -/
def locusOpenSubgroup (ρ : DomainSpectralAction G P) (d : Domain K P) :
    OpenSubgroup G where
  toSubgroup := (locusStabilizer d).comap ρ.toMonoidHom
  isOpen' := (isOpen_locusStabilizer P d).preimage
    ρ.continuous_toMonoidHom

@[simp] theorem mem_locusOpenSubgroup (ρ : DomainSpectralAction G P)
    (d : Domain K P) (g : G) :
    g ∈ ρ.locusOpenSubgroup d ↔
      (fun x : BanachSpectrum P => ρ.toMonoidHom g • x) '' d.locus = d.locus :=
  Iff.rfl

/-- Map the open subgroup into the actual ambient represented-locus stabilizer. -/
def stabilizerHom (ρ : DomainSpectralAction G P) (d : Domain K P) :
    ρ.locusOpenSubgroup d →* locusStabilizer d where
  toFun g := ⟨ρ.toMonoidHom g, g.property⟩
  map_one' := Subtype.ext (map_one ρ.toMonoidHom)
  map_mul' g h := Subtype.ext (map_mul ρ.toMonoidHom (g : G) (h : G))

/-- The open locus stabilizer acts on the actual fixed represented section algebra.
No continuity of this homomorphism in a section topology is asserted. -/
def sectionAction (ρ : DomainSpectralAction G P) (d : Domain K P) :
    ρ.locusOpenSubgroup d →* Aut d.algebra :=
  (stabilizerSectionAction d).comp (ρ.stabilizerHom d)

/-- The local action extends the given forward action on base-algebra sections. -/
@[simp] theorem sectionAction_baseMap (ρ : DomainSpectralAction G P)
    (d : Domain K P) (g : ρ.locusOpenSubgroup d) (a : P) :
    (ρ.sectionAction d g).hom.toAlgHom (d.baseMap a) =
      d.baseMap ((ρ.toMonoidHom g).hom.toAlgHom a) :=
  stabilizerSectionAction_baseMap d (ρ.stabilizerHom d g) a

end DomainSpectralAction

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism
