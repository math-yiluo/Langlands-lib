import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainContinuousFiniteCover
import Langlands.Topology.GroupAction.QuotientCoequalizer

/-! # Actual finite spectrum covers as continuous-action coequalizers -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory CategoryTheory.Limits Topology

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)
  (H : OpenSubgroup G) (d : ρ.InvariantDomain H) (c : Domain.FiniteCover d.obj)

/-- Pairs of actual component-spectrum points with the same target locus point.
The original product subspace topology is retained. -/
abbrev FiniteCoverRelation :=
  ContinuousQuotient.Relation (ρ.finiteCoverQuotientContinuous H d c)

/-- The fiber relation carries the original componentwise diagonal action. -/
def finiteCoverRelation :
    ContAction TopCat.{u} (ρ.finiteFamilyOpenSubgroup H c.obj) :=
  ContinuousQuotient.relation (ρ.finiteCoverQuotientContinuous H d c)

/-- The first actual spectrum-union projection. -/
def finiteCoverRelationFst :
    ρ.finiteCoverRelation H d c ⟶ ρ.finiteCoverSpectrum H d c :=
  ContinuousQuotient.fst (ρ.finiteCoverQuotientContinuous H d c)

/-- The second actual spectrum-union projection. -/
def finiteCoverRelationSnd :
    ρ.finiteCoverRelation H d c ⟶ ρ.finiteCoverSpectrum H d c :=
  ContinuousQuotient.snd (ρ.finiteCoverQuotientContinuous H d c)

@[simp]
theorem finiteCoverRelationFst_apply (p : ρ.FiniteCoverRelation H d c) :
    (ρ.finiteCoverRelationFst H d c).hom.hom p = p.val.1 := rfl

@[simp]
theorem finiteCoverRelationSnd_apply (p : ρ.FiniteCoverRelation H d c) :
    (ρ.finiteCoverRelationSnd H d c).hom.hom p = p.val.2 := rfl

/-- Membership is literal equality of the original structural pullbacks
in the represented target locus. No spectrum injectivity is assumed. -/
theorem finiteCoverRelation_iff
    (x y : Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra) :
    c.totalMap x = c.totalMap y ↔
      Nonempty {p : ρ.FiniteCoverRelation H d c // p.val = (x, y)} := by
  constructor
  · intro h
    exact ⟨⟨⟨(x, y), h⟩, rfl⟩⟩
  · rintro ⟨⟨p, hp⟩⟩
    have h := p.property
    change c.totalMap p.val.1 = c.totalMap p.val.2 at h
    simpa only [hp] using h

/-- The original diagonal relation is the actual categorical kernel pair of
the unchanged finite spectrum quotient. -/
def finiteCoverQuotientKernelPair :
    IsLimit (ContinuousQuotient.pullbackCone
      (ρ.finiteCoverQuotientContinuous H d c)) :=
  ContinuousQuotient.isLimit (ρ.finiteCoverQuotientContinuous H d c)

/-- Retain the existing target represented locus and exact quotient map. -/
def finiteCoverQuotientCofork :
    Cofork (ρ.finiteCoverRelationFst H d c) (ρ.finiteCoverRelationSnd H d c) :=
  ContinuousQuotient.cofork (ρ.finiteCoverQuotientContinuous H d c)

@[simp]
theorem finiteCoverQuotientCofork_π :
    (ρ.finiteCoverQuotientCofork H d c).π =
      ρ.finiteCoverQuotientContinuous H d c := rfl

/-- The actual target locus is the coequalizer of the actual spectrum-cover
fiber relation among all jointly continuous actions. -/
def finiteCoverQuotientIsColimit :
    IsColimit (ρ.finiteCoverQuotientCofork H d c) :=
  ContinuousQuotient.isColimit (ρ.finiteCoverQuotientContinuous H d c)
    (ρ.finiteCoverQuotientContinuous_isQuotientMap H d c)

variable {Z : ContAction TopCat.{u} (ρ.finiteFamilyOpenSubgroup H c.obj)}
  (f : ρ.finiteCoverSpectrum H d c ⟶ Z)
  (hf : ρ.finiteCoverRelationFst H d c ≫ f =
    ρ.finiteCoverRelationSnd H d c ≫ f)

/-- Explicit descent of fiber-compatible maps on the actual spectra to an
arbitrary jointly continuous target action. -/
def finiteCoverQuotientDesc :
    (ρ.invariantLocusFunctor (ρ.finiteFamilyOpenSubgroup H c.obj)).obj
        (ρ.finiteInvariantTarget H d c.obj) ⟶ Z :=
  ContinuousQuotient.desc (ρ.finiteCoverQuotientContinuous H d c)
    (ρ.finiteCoverQuotientContinuous_isQuotientMap H d c) f hf

@[simp]
theorem finiteCoverQuotientDesc_apply (i : Fin c.size)
    (x : BanachSpectrum (c.obj i).algebra) :
    (ρ.finiteCoverQuotientDesc H d c f hf).hom.hom (c.componentMap i x) =
      f.hom.hom ⟨i, x⟩ :=
  ContinuousQuotient.liftMap_apply (ρ.finiteCoverQuotientContinuous H d c)
    (ρ.finiteCoverQuotientContinuous_isQuotientMap H d c) f hf ⟨i, x⟩

theorem finiteCoverQuotientDesc_fac :
    ρ.finiteCoverQuotientContinuous H d c ≫
      ρ.finiteCoverQuotientDesc H d c f hf = f :=
  ContinuousQuotient.fac (ρ.finiteCoverQuotientContinuous H d c)
    (ρ.finiteCoverQuotientContinuous_isQuotientMap H d c) f hf

theorem finiteCoverQuotientDesc_unique
    (k : (ρ.invariantLocusFunctor (ρ.finiteFamilyOpenSubgroup H c.obj)).obj
      (ρ.finiteInvariantTarget H d c.obj) ⟶ Z)
    (hk : ρ.finiteCoverQuotientContinuous H d c ≫ k = f) :
    k = ρ.finiteCoverQuotientDesc H d c f hf :=
  ContinuousQuotient.desc_unique (ρ.finiteCoverQuotientContinuous H d c)
    (ρ.finiteCoverQuotientContinuous_isQuotientMap H d c) f hf k hk

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
