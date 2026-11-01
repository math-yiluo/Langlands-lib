import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainContinuousLocus
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainFiniteInvariantCover
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Jointly continuous finite spectrum quotient covers -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory Topology

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

private theorem continuous_fiberwise_sigma {A I : Type*} [TopologicalSpace A]
    {X : I → Type*} [∀ i, TopologicalSpace (X i)]
    (F : ∀ i, A × X i → X i) (hF : ∀ i, Continuous (F i)) :
    Continuous (fun p : A × (Σ i, X i) => Sigma.mk p.2.1 (F p.2.1 (p.1, p.2.2))) := by
  have hc : Continuous (fun p : Σ i, X i × A =>
      Sigma.mk p.1 (F p.1 (p.2.2, p.2.1))) :=
    continuous_sigma fun i =>
      continuous_sigmaMk.comp ((hF i).comp (continuous_snd.prodMk continuous_fst))
  exact hc.comp
    ((Homeomorph.sigmaProdDistrib (X := X) (Y := A)).continuous.comp continuous_swap)

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)
  (H : OpenSubgroup G) (d : ρ.InvariantDomain H) (c : Domain.FiniteCover d.obj)

/-- Joint continuity of the existing finite disjoint-union action follows
from joint continuity on each original component spectrum. -/
theorem finiteCoverSpectrumAction_isContinuous :
    (ρ.finiteCoverSpectrumAction H d c).IsContinuous := by
  apply (Action.isContinuous_def _).mpr
  exact continuous_fiberwise_sigma
    (fun i p => ConcreteCategory.hom ((ρ.finiteCoverComponentAction H d c i).ρ p.1) p.2)
    (fun i => (Action.isContinuous_def
      (ρ.finiteCoverComponentAction H d c i)).mp
        (ρ.invariantSpectrumAction_isContinuous
          (ρ.finiteFamilyOpenSubgroup H c.obj) (ρ.finiteInvariantFamily H c.obj i)))

/-- The exact original finite disjoint union with proved joint continuity. -/
def finiteCoverSpectrum : ContAction TopCat.{u} (ρ.finiteFamilyOpenSubgroup H c.obj) :=
  ⟨ρ.finiteCoverSpectrumAction H d c, ρ.finiteCoverSpectrumAction_isContinuous H d c⟩

@[simp]
theorem finiteCoverSpectrum_toAction :
    (ρ.finiteCoverSpectrum H d c).obj = ρ.finiteCoverSpectrumAction H d c := rfl

@[simp]
theorem finiteCoverSpectrum_mk (g : ρ.finiteFamilyOpenSubgroup H c.obj)
    (i : Fin c.size) (x : BanachSpectrum (c.obj i).algebra) :
    ConcreteCategory.hom ((ρ.finiteCoverSpectrum H d c).obj.ρ g) ⟨i, x⟩ =
      Sigma.mk i
        (ConcreteCategory.hom ((ρ.finiteCoverComponentAction H d c i).ρ g) x) := rfl

/-- The original bounded component map into the target locus is now a morphism
of jointly continuous actions. -/
def finiteCoverComponentContinuous (i : Fin c.size) :
    (ρ.invariantSpectrumFunctor (ρ.finiteFamilyOpenSubgroup H c.obj)).obj
        (ρ.finiteInvariantFamily H c.obj i) ⟶
      (ρ.invariantLocusFunctor (ρ.finiteFamilyOpenSubgroup H c.obj)).obj
        (ρ.finiteInvariantTarget H d c.obj) :=
  ObjectProperty.homMk (ρ.finiteCoverComponent H d c i)

@[simp]
theorem finiteCoverComponentContinuous_apply (i : Fin c.size)
    (x : BanachSpectrum (c.obj i).algebra) :
    (ρ.finiteCoverComponentContinuous H d c i).hom.hom x = c.componentMap i x := rfl

/-- The unchanged finite spectrum quotient is a morphism of jointly
continuous actions onto the actual target represented locus. -/
def finiteCoverQuotientContinuous :
    ρ.finiteCoverSpectrum H d c ⟶
      (ρ.invariantLocusFunctor (ρ.finiteFamilyOpenSubgroup H c.obj)).obj
        (ρ.finiteInvariantTarget H d c.obj) :=
  ObjectProperty.homMk (ρ.finiteCoverQuotient H d c)

@[simp]
theorem finiteCoverQuotientContinuous_toAction :
    (ρ.finiteCoverQuotientContinuous H d c).hom = ρ.finiteCoverQuotient H d c := rfl

@[simp]
theorem finiteCoverQuotientContinuous_hom :
    (ρ.finiteCoverQuotientContinuous H d c).hom.hom = TopCat.ofHom c.totalMap := rfl

theorem finiteCoverQuotientContinuous_surjective :
    Function.Surjective (ρ.finiteCoverQuotientContinuous H d c).hom.hom :=
  c.totalMap_surjective

theorem finiteCoverQuotientContinuous_isClosedMap :
    IsClosedMap (ρ.finiteCoverQuotientContinuous H d c).hom.hom :=
  c.totalMap_isClosedMap

theorem finiteCoverQuotientContinuous_isQuotientMap :
    IsQuotientMap (ρ.finiteCoverQuotientContinuous H d c).hom.hom :=
  c.totalMap_isQuotientMap

theorem finiteCoverQuotientContinuous_isOpen_iff (s : Set d.obj.locus) :
    IsOpen s ↔ ∀ i, IsOpen ((ρ.finiteCoverComponentContinuous H d c i).hom.hom ⁻¹' s) :=
  c.isOpen_iff s

theorem finiteCoverQuotientContinuous_isClosed_iff (s : Set d.obj.locus) :
    IsClosed s ↔ ∀ i, IsClosed ((ρ.finiteCoverComponentContinuous H d c i).hom.hom ⁻¹' s) :=
  c.isClosed_iff s

/-- No equivariance is required of the map whose continuity is tested. -/
theorem finiteCoverQuotientContinuous_continuous_iff {Y : Type w} [TopologicalSpace Y]
    (f : d.obj.locus → Y) :
    Continuous f ↔ ∀ i,
      Continuous (f ∘ (ρ.finiteCoverComponentContinuous H d c i).hom.hom) :=
  c.continuous_iff f

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
