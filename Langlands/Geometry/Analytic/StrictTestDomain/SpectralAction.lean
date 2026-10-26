import Langlands.Geometry.Analytic.StrictTestDomain.SpectralTopology
import Mathlib.Topology.Algebra.Group.Neighborhood

/-! # Continuous actions for the restricted rational spectral topology -/

noncomputable section

universe u v w

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism

open CategoryTheory
open scoped Topology

attribute [local instance] rationalSpectralTopology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (P : PresentedStrictAffinoidAlgebra K)

/-- A single positive-radius rational spectral test is open. -/
theorem isOpen_rationalSpectralSubgroup (d : RationalData K P) (b : d.algebra)
    (r : ℝ) (hr : 0 < r) :
    @IsOpen (Aut P) (rationalSpectralTopology P)
      (rationalSpectralSubgroup d b r hr.le : Set (Aut P)) := by
  let t : RationalSpectralTest K P := ⟨d, b, r, hr⟩
  simpa [finiteRationalSpectralSubgroup, t] using
    isOpen_finiteRationalSpectralSubgroup P (fun _ : Unit => t)

/-- Zero-section tests make every rational-locus stabilizer open in this topology. -/
theorem isOpen_locusStabilizer_rationalSpectralTopology (d : RationalData K P) :
    @IsOpen (Aut P) (rationalSpectralTopology P) (locusStabilizer d : Set (Aut P)) := by
  simpa only [rationalSpectralSubgroup_zero] using
    isOpen_rationalSpectralSubgroup P d 0 1 zero_lt_one

/-- The actual setwise rational-locus stabilizer, bundled as an open subgroup. -/
def rationalLocusOpenSubgroup (d : RationalData K P) :
    @OpenSubgroup (Aut P) _ (rationalSpectralTopology P) where
  toSubgroup := locusStabilizer d
  isOpen' := isOpen_locusStabilizer_rationalSpectralTopology P d

variable {G : Type v} [Group G] [TopologicalSpace G]

/-- Continuity into the rational spectral topology is exactly continuity of
every finite test at one. The index universe zero already supplies the full basis. -/
theorem continuous_rationalSpectralTopology_iff [IsTopologicalGroup G] (ρ : G →* Aut P) :
    @Continuous G (Aut P) _ (rationalSpectralTopology P) ρ ↔
      ∀ (ι : Type) (_ : Finite ι) (tests : ι → RationalSpectralTest K P),
        ρ ⁻¹' (finiteRationalSpectralSubgroup tests : Set (Aut P)) ∈ 𝓝 (1 : G) := by
  let := rationalSpectralTopology P
  let := rationalSpectralTopology_isTopologicalGroup P
  constructor
  · intro h ι hι tests
    have ht := finiteRationalSpectralSubgroup_mem_nhds_one P tests
    have hρ : Filter.Tendsto ρ (𝓝 (1 : G)) (𝓝 (1 : Aut P)) := by
      simpa only [map_one] using (h.continuousAt (x := (1 : G))).tendsto
    exact hρ ht
  · intro h
    apply continuous_of_tendsto_nhds_one ρ
    rw [Filter.tendsto_def]
    intro U hU
    obtain ⟨ι, hι, tests, hsub⟩ :=
      (mem_nhds_one_rationalSpectralTopology P U).mp hU
    exact Filter.mem_of_superset (h ι hι tests) (Set.preimage_mono hsub)

/-- An action by actual bounded algebra automorphisms, continuous for the
restricted rational spectral topology. This does not assert full analytic continuity. -/
structure RationalSpectralAction (G : Type v) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (P : PresentedStrictAffinoidAlgebra K) where
  toMonoidHom : G →* Aut P
  continuous_toMonoidHom :
    @Continuous G (Aut P) _ (rationalSpectralTopology P) toMonoidHom

namespace RationalSpectralAction

variable {P} [IsTopologicalGroup G]

/-- Construct a continuous rational action by checking the finite tests at one. -/
def ofFiniteTests (ρ : G →* Aut P)
    (hρ : ∀ (ι : Type) (_ : Finite ι) (tests : ι → RationalSpectralTest K P),
      ρ ⁻¹' (finiteRationalSpectralSubgroup tests : Set (Aut P)) ∈ 𝓝 (1 : G)) :
    RationalSpectralAction G P :=
  ⟨ρ, (continuous_rationalSpectralTopology_iff P ρ).mpr hρ⟩

/-- The trivial action is continuous. -/
def trivial : RationalSpectralAction G P :=
  ⟨1, continuous_const⟩

/-- Pull back a rational action along a continuous homomorphism of groups. -/
def precomp {H : Type w} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (ρ : RationalSpectralAction G P) (f : H →* G) (hf : Continuous f) :
    RationalSpectralAction H P where
  toMonoidHom := ρ.toMonoidHom.comp f
  continuous_toMonoidHom := ρ.continuous_toMonoidHom.comp hf

/-- The inverse image of a finite test subgroup is an actual open subgroup of G.
Finite index types in every universe are allowed. -/
def testOpenSubgroup (ρ : RationalSpectralAction G P)
    {ι : Type w} [Finite ι] (tests : ι → RationalSpectralTest K P) :
    OpenSubgroup G where
  toSubgroup := (finiteRationalSpectralSubgroup tests).comap ρ.toMonoidHom
  isOpen' := (isOpen_finiteRationalSpectralSubgroup P tests).preimage
    ρ.continuous_toMonoidHom

@[simp] theorem mem_testOpenSubgroup (ρ : RationalSpectralAction G P)
    {ι : Type w} [Finite ι] (tests : ι → RationalSpectralTest K P) (g : G) :
    g ∈ ρ.testOpenSubgroup tests ↔
      ρ.toMonoidHom g ∈ finiteRationalSpectralSubgroup tests := Iff.rfl

/-- The subgroup of G preserving a fixed rational locus is open. -/
def locusOpenSubgroup (ρ : RationalSpectralAction G P) (d : RationalData K P) :
    OpenSubgroup G where
  toSubgroup := (locusStabilizer d).comap ρ.toMonoidHom
  isOpen' := (isOpen_locusStabilizer_rationalSpectralTopology P d).preimage
    ρ.continuous_toMonoidHom

@[simp] theorem mem_locusOpenSubgroup (ρ : RationalSpectralAction G P)
    (d : RationalData K P) (g : G) :
    g ∈ ρ.locusOpenSubgroup d ↔
      (fun x : BanachSpectrum P => ρ.toMonoidHom g • x) '' d.locus = d.locus :=
  Iff.rfl

/-- Map the open subgroup into the actual ambient rational-locus stabilizer. -/
def stabilizerHom (ρ : RationalSpectralAction G P) (d : RationalData K P) :
    ρ.locusOpenSubgroup d →* locusStabilizer d where
  toFun g := ⟨ρ.toMonoidHom g, g.property⟩
  map_one' := Subtype.ext (map_one ρ.toMonoidHom)
  map_mul' g h := Subtype.ext (map_mul ρ.toMonoidHom (g : G) (h : G))

/-- The open locus stabilizer acts on the actual fixed rational quotient.
No continuity of this homomorphism in a section topology is asserted. -/
def sectionAction (ρ : RationalSpectralAction G P) (d : RationalData K P) :
    ρ.locusOpenSubgroup d →* Aut d.algebra :=
  (stabilizerSectionAction d).comp (ρ.stabilizerHom d)

/-- The local action extends the given forward action on base-algebra sections. -/
@[simp] theorem sectionAction_baseMap (ρ : RationalSpectralAction G P)
    (d : RationalData K P) (g : ρ.locusOpenSubgroup d) (a : P) :
    (ρ.sectionAction d g).hom.toAlgHom (d.baseMap a) =
      d.baseMap ((ρ.toMonoidHom g).hom.toAlgHom a) :=
  stabilizerSectionAction_baseMap d (ρ.stabilizerHom d g) a

end RationalSpectralAction

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism
