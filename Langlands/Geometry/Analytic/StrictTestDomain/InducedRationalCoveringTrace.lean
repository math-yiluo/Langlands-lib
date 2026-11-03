import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCompactSupport
import Langlands.Representation.LocallyConstant.CoveringTrace

/-! # Finite-covering trace on actual induced rational spectra -/

noncomputable section

universe u v r w

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology
open Langlands.LocallyConstantCovering

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type r} [CommRing R]

namespace OpenSubgroupTransport.Hom

open CompactSections
open Langlands.CompactAction.LocallyConstantModule

variable {X Y Z : ρ.OpenSubgroupTransport}

/-- Literal sum on fibers of the original induced map, under genuine covering
and finite-fiber hypotheses. -/
def compactSupportTrace (f : X ⟶ Y) [∀ y, Finite (f.inducedMap ⁻¹' {y})]
    (hf : IsCoveringMap f.inducedMap) (M : SmoothRep.{r, v, w} R G) :
    smoothRepresentation X M ⟶ smoothRepresentation Y M :=
  CompactSupport.smoothTrace M f.inducedMap hf f.inducedMap_smul

@[simp]
theorem compactSupportTrace_apply (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})]
    (hf : IsCoveringMap f.inducedMap) (M : SmoothRep.{r, v, w} R G)
    (s : Functions (R := R) (V := M) X) (y : Y.InducedSpectrum) :
    (SmoothRep.hom (f.compactSupportTrace hf M) s).val y =
      fiberSum f.inducedMap s.val y := rfl

/-- All original smooth coefficient intertwiners commute with trace. -/
theorem compactSupportTrace_naturality (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] (hf : IsCoveringMap f.inducedMap)
    {M N : SmoothRep.{r, v, w} R G} (a : M ⟶ N) :
    (coefficientFunctor X).map a ≫ f.compactSupportTrace hf N =
      f.compactSupportTrace hf M ≫ (coefficientFunctor Y).map a :=
  CompactSupport.smoothTrace_naturality f.inducedMap hf f.inducedMap_smul a

/-- The original identity map has actual finite fibers. -/
theorem finite_inducedMap_id_fiber (X : ρ.OpenSubgroupTransport) (x : X.InducedSpectrum) :
    Finite ((𝟙 X : X ⟶ X).inducedMap ⁻¹' {x}) := by
  have h : ⇑(𝟙 X : X ⟶ X).inducedMap = id := funext (inducedMap_id X)
  rw [h]
  exact finite_id_fiber x

/-- The original identity transport map is a one-sheeted covering. -/
theorem isCoveringMap_inducedMap_id (X : ρ.OpenSubgroupTransport) :
    IsCoveringMap (𝟙 X : X ⟶ X).inducedMap := by
  have h : ⇑(𝟙 X : X ⟶ X).inducedMap = id := funext (inducedMap_id X)
  rw [h]
  exact isCoveringMap_id

@[simp]
theorem compactSupportTrace_id [∀ x, Finite ((𝟙 X : X ⟶ X).inducedMap ⁻¹' {x})]
    (M : SmoothRep.{r, v, w} R G) :
    (𝟙 X : X ⟶ X).compactSupportTrace (isCoveringMap_inducedMap_id X) M =
      𝟙 (smoothRepresentation X M) := by
  ext s
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  let : ∀ x : X.InducedSpectrum, Finite ((id : X.InducedSpectrum → X.InducedSpectrum) ⁻¹' {x}) :=
    finite_id_fiber
  exact (fiberSum_congr (p := id) (funext (inducedMap_id X)) s.val x).trans
    (fiberSum_id s.val x)

/-- Actual finite fibers are closed under original rational transport composition. -/
theorem finite_inducedMap_comp_fiber (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] [∀ z, Finite (g.inducedMap ⁻¹' {z})]
    (z : Z.InducedSpectrum) : Finite ((f ≫ g).inducedMap ⁻¹' {z}) := by
  have h : ⇑(f ≫ g).inducedMap = g.inducedMap ∘ f.inducedMap :=
    funext (inducedMap_comp f g)
  rw [h]
  exact finite_comp_fiber f.inducedMap g.inducedMap z

/-- Composition is the sum on fibers of the original composite, whenever
that composite also satisfies the actual covering predicate. -/
theorem compactSupportTrace_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] [∀ z, Finite (g.inducedMap ⁻¹' {z})]
    [∀ z, Finite ((f ≫ g).inducedMap ⁻¹' {z})]
    (hf : IsCoveringMap f.inducedMap) (hg : IsCoveringMap g.inducedMap)
    (hfg : IsCoveringMap (f ≫ g).inducedMap) (M : SmoothRep.{r, v, w} R G) :
    (f ≫ g).compactSupportTrace hfg M =
      f.compactSupportTrace hf M ≫ g.compactSupportTrace hg M := by
  ext s
  apply Subtype.ext
  apply LocallyConstant.ext
  intro z
  let : ∀ z : Z.InducedSpectrum, Finite ((g.inducedMap ∘ f.inducedMap) ⁻¹' {z}) :=
    finite_comp_fiber f.inducedMap g.inducedMap
  exact (fiberSum_congr (p := g.inducedMap ∘ f.inducedMap)
    (funext (inducedMap_comp f g)) s.val z).trans
    (fiberSum_comp f.inducedMap g.inducedMap s.val z)

/-- Trace on the entire original smooth coefficient functor. -/
def compactSupportTraceNatTrans (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] (hf : IsCoveringMap f.inducedMap) :
    (coefficientFunctor X :
      SmoothRep.{r, v, w} R G ⥤ SmoothRep.{r, v, max u v w} R G) ⟶ coefficientFunctor Y :=
  CompactSupport.traceNatTrans f.inducedMap hf f.inducedMap_smul

@[simp]
theorem compactSupportTraceNatTrans_app (f : X ⟶ Y)
    [∀ y, Finite (f.inducedMap ⁻¹' {y})] (hf : IsCoveringMap f.inducedMap)
    (M : SmoothRep.{r, v, w} R G) :
    (f.compactSupportTraceNatTrans (R := R) hf).app M = f.compactSupportTrace hf M := rfl

end OpenSubgroupTransport.Hom

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
