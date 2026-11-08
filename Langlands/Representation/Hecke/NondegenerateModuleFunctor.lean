import Langlands.Algebra.NonUnitalModule
import Langlands.Algebra.CompatibleNonUnitalAction
import Langlands.Representation.Hecke.ActionProjection
import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.FixedVectors.OrderProof
import Langlands.Topology.CompactOpen.NeighborhoodBasis

/-! # Smooth representations as nondegenerate modules over the Hecke algebra (Renard III.1.4)

A smooth complex representation of a locally compact nonarchimedean group `G` is a module over
the Haar Hecke algebra `H(G) = HeckeAlgebra μ` through the integrated action
`heckeAction μ ρ`; this module is nondegenerate, and intertwiners are module maps. This gives
the functor `heckeNondegenerateModuleFunctor μ` from smooth representations to Renard's
category `M(H(G))` of nondegenerate modules.
-/

noncomputable section

universe u v

open CategoryTheory MeasureTheory

namespace Langlands.Hecke

variable {G : Type u} [Group G] [TopologicalSpace G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]

/-- The module structure of the Hecke algebra on a smooth representation, through the
integrated action `heckeAction μ ρ hρ`. -/
abbrev heckeNonUnitalModule {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) :
    Algebra.NonUnitalModule (HeckeAlgebra μ) V :=
  Algebra.NonUnitalModule.ofLinearEndHom (heckeAction μ ρ hρ)

/-- Every vector of a smooth representation is fixed by the normalized indicator of a
compact open subgroup, an idempotent of the Hecke algebra: the module is nondegenerate. -/
theorem heckeNonUnitalModule_isNondegenerate {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) :
    @Algebra.IsNondegenerate (HeckeAlgebra μ) V _ _ (heckeNonUnitalModule μ ρ hρ) := by
  intro x
  obtain ⟨U, hU⟩ := hρ x
  obtain ⟨K, hKc, hKU⟩ :=
    compactOpenSubgroupBasis G (U : Set G) (U.isOpen.mem_nhds U.one_mem)
  refine ⟨⟨HeckeAlgebra.normalizedIndicator μ K hKc,
    HeckeAlgebra.normalizedIndicator_idempotent μ K hKc⟩, ?_⟩
  have hx : x ∈ fixedVectors ρ K.toSubgroup :=
    fixedVectors_antitone ρ (fun g hg => hKU hg) hU
  exact heckeAction_normalizedIndicator_of_fixed μ ρ hρ K hKc hx

/-- The nondegenerate Hecke module of a smooth representation. -/
def heckeNondegenerateModule (A : SmoothRep.{0, u, v} ℂ G) :
    Algebra.NondegenerateModuleCat.{u, v} (HeckeAlgebra μ) :=
  ⟨@Algebra.NonUnitalModuleCat.of (HeckeAlgebra μ) _ A _
      (heckeNonUnitalModule μ A.representation A.isSmooth),
    heckeNonUnitalModule_isNondegenerate μ A.representation A.isSmooth⟩

/-- An intertwiner of smooth representations as a map of Hecke modules. -/
def heckeNondegenerateModuleMap {A B : SmoothRep.{0, u, v} ℂ G} (f : A ⟶ B) :
    heckeNondegenerateModule μ A ⟶ heckeNondegenerateModule μ B :=
  ObjectProperty.homMk
    (@Algebra.NonUnitalModuleHom.mk (HeckeAlgebra μ) A B _ _ _
      (heckeNonUnitalModule μ A.representation A.isSmooth)
      (heckeNonUnitalModule μ B.representation B.isSmooth)
      (SmoothRep.hom f).toLinearMap.toAddMonoidHom
      (fun a x => integratedAction_intertwiner μ A.isSmooth B.isSmooth (SmoothRep.hom f)
        (HeckeAlgebra.toTestFunction μ a) x))

/-- The functor from smooth complex representations of `G` to nondegenerate modules over the
Hecke algebra `HeckeAlgebra μ`: a representation goes to its carrier with the action
`heckeAction μ`, an intertwiner to the same additive map. -/
def heckeNondegenerateModuleFunctor :
    SmoothRep.{0, u, v} ℂ G ⥤ Algebra.NondegenerateModuleCat.{u, v} (HeckeAlgebra μ) where
  obj A := heckeNondegenerateModule μ A
  map f := heckeNondegenerateModuleMap μ f
  map_id _ := rfl
  map_comp _ _ := rfl

end Langlands.Hecke
