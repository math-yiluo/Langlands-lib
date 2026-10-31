import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainTopology

/-! # Full domains inside actual rational charts -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}

omit [CompleteSpace K] in
private theorem spectrum_comp (i : BoundedAlgHom K A B) (j : BoundedAlgHom K B C)
    (x : BanachSpectrum C) :
    BanachSpectrum.comap (j.comp i).toBoundedRingHom x =
      BanachSpectrum.comap i.toBoundedRingHom
        (BanachSpectrum.comap j.toBoundedRingHom x) := by
  apply BanachSpectrum.ext
  intro a
  rfl

/-- Composition of full domain representations is again a full representation
when the outer structural spectrum map is injective. -/
theorem Represents.comp_of_injective {i : BoundedAlgHom K A B}
    {j : BoundedAlgHom K B C} {U : Set (BanachSpectrum A)}
    {V : Set (BanachSpectrum B)} (hi : Represents K i U) (hj : Represents K j V)
    (hinj : Function.Injective (BanachSpectrum.comap i.toBoundedRingHom)) :
    Represents K (j.comp i) (BanachSpectrum.comap i.toBoundedRingHom '' V) := by
  refine ⟨(hj.1.isCompact.image
    (BanachSpectrum.comapContinuous i.toBoundedRingHom).continuous).isClosed, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨BanachSpectrum.comap j.toBoundedRingHom y, hj.hasImageIn y,
        (spectrum_comp i j y).symm⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz⟩ := hj.2.1.symm ▸ hy
      exact ⟨z, (spectrum_comp i j z).trans (congrArg _ hz)⟩
  · intro R φ hφ
    have hU : HasImageIn K φ U := by
      intro x
      obtain ⟨y, _, hy⟩ := hφ x
      exact hy ▸ hi.hasImageIn y
    obtain ⟨ψ, hψ, hψuniq⟩ := hi.2.2 R φ hU
    have hV : HasImageIn K ψ V := by
      intro x
      obtain ⟨y, hy, hbase⟩ := hφ x
      have heq : BanachSpectrum.comap i.toBoundedRingHom
          (BanachSpectrum.comap ψ.toBoundedRingHom x) =
          BanachSpectrum.comap i.toBoundedRingHom y := by
        rw [← spectrum_comp, hψ]
        exact hbase.symm
      rw [hinj heq]
      exact hy
    obtain ⟨θ, hθ, hθuniq⟩ := hj.2.2 R ψ hV
    refine ⟨θ, ?_, ?_⟩
    · change (θ.comp j).comp i = φ
      rw [hθ, hψ]
    · intro θ' hθ'
      apply hθuniq θ'
      exact hψuniq (θ'.comp j) hθ'

namespace RationalChart

omit [CompleteSpace K] in
/-- Injectivity here is supplied by the proved actual rational-spectrum
homeomorphism, with no additional representation hypothesis. -/
theorem spectrumMap_injective (d : RationalChart K A) :
    Function.Injective d.spectrumMap := by
  intro x y h
  exact d.locusHomeomorph.injective (Subtype.ext h)

/-- An actual full domain over a rational quotient gives a full domain over
the original base, with its algebra unchanged and structural map composed. -/
def extendDomain (d : RationalChart K A) (U : Domain K d.algebra) : Domain K A where
  algebra := U.algebra
  baseMap := U.baseMap.comp d.baseMap
  locus := d.spectrumMap '' U.locus
  represents := d.represents.comp_of_injective U.represents d.spectrumMap_injective

@[simp] theorem extendDomain_algebra (d : RationalChart K A)
    (U : Domain K d.algebra) : (d.extendDomain U).algebra = U.algebra := rfl

@[simp] theorem extendDomain_baseMap (d : RationalChart K A)
    (U : Domain K d.algebra) :
    (d.extendDomain U).baseMap = U.baseMap.comp d.baseMap := rfl

@[simp] theorem extendDomain_locus (d : RationalChart K A)
    (U : Domain K d.algebra) :
    (d.extendDomain U).locus = d.spectrumMap '' U.locus := rfl

theorem extendDomain_locus_subset (d : RationalChart K A) (U : Domain K d.algebra) :
    (d.extendDomain U).locus ⊆ d.locus := by
  rintro _ ⟨x, _, rfl⟩
  exact (d.locusHomeomorph x).property

/-- The actual inclusion into the outer rational chart stores precisely the
inner domain's structural bounded map. -/
def extendDomainInclusion (d : RationalChart K A) (U : Domain K d.algebra) :
    d.extendDomain U ⟶ d.toDomain where
  restriction := U.baseMap
  comp_baseMap := rfl

@[simp] theorem extendDomainInclusion_restriction (d : RationalChart K A)
    (U : Domain K d.algebra) :
    (d.extendDomainInclusion U).restriction = U.baseMap := rfl

/-- Actual inner restrictions remain actual restrictions after composing their
structural maps with the outer rational quotient map. -/
def extendDomainFunctor (d : RationalChart K A) : Domain K d.algebra ⥤ Domain K A where
  obj := d.extendDomain
  map {U V} f := ⟨f.restriction, by
    change f.restriction.comp (V.baseMap.comp d.baseMap) = U.baseMap.comp d.baseMap
    rw [← BoundedAlgHom.comp_assoc, f.comp_baseMap]⟩
  map_id _ := Domain.Inclusion.ext rfl
  map_comp _ _ := Domain.Inclusion.ext rfl

@[simp] theorem extendDomainFunctor_map_restriction (d : RationalChart K A)
    {U V : Domain K d.algebra} (f : U ⟶ V) :
    ((d.extendDomainFunctor).map f).restriction = f.restriction := rfl

/-- The original rational quotient's proved bounded-map uniqueness recovers
the inner base equation from the equation over the original base. -/
def fullyFaithfulExtendDomain (d : RationalChart K A) : d.extendDomainFunctor.FullyFaithful where
  preimage {U V} f := ⟨f.restriction, by
    apply RationalPresentation.hom_ext_base K A d.radii d.denominator d.numerators
      U.algebra d.generates
    exact f.comp_baseMap⟩
  map_preimage _ := Domain.Inclusion.ext rfl
  preimage_map _ := Domain.Inclusion.ext rfl

instance (d : RationalChart K A) : d.extendDomainFunctor.Full :=
  d.fullyFaithfulExtendDomain.full

instance (d : RationalChart K A) : d.extendDomainFunctor.Faithful :=
  d.fullyFaithfulExtendDomain.faithful

/-- Composition keeps the actual represented algebras and bounded
restriction maps definitionally. -/
theorem extendDomainFunctor_comp_toAffinoidSpace (d : RationalChart K A) :
    d.extendDomainFunctor ⋙ Domain.toAffinoidSpace K A =
      Domain.toAffinoidSpace K d.algebra := rfl

theorem extendDomainFunctor_comp_toTopologicalSpace (d : RationalChart K A) :
    d.extendDomainFunctor ⋙ Domain.toTopologicalSpace K A =
      Domain.toTopologicalSpace K d.algebra := rfl

end RationalChart
end Langlands.Analytic.PresentedAffinoidAlgebra
