import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalRepresentationProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainComparison
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Rational charts as actual represented affinoid domains -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

/-- The proved full representation property makes the actual chart quotient
and its structural map a domain representation. -/
def toDomain (d : RationalChart K A) : Domain K A where
  algebra := d.algebra
  baseMap := d.baseMap
  locus := d.locus
  represents := d.represents

@[simp] theorem toDomain_algebra (d : RationalChart K A) :
    d.toDomain.algebra = d.algebra := rfl

@[simp] theorem toDomain_baseMap (d : RationalChart K A) :
    d.toDomain.baseMap = d.baseMap := rfl

@[simp] theorem toDomain_locus (d : RationalChart K A) :
    d.toDomain.locus = d.locus := rfl

/-- Actual bounded restrictions give the same arrows between the corresponding
full domain representations. -/
def toDomainFunctor (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : PresentedAffinoidAlgebra K) : RationalChart K A ⥤ Domain K A where
  obj d := d.toDomain
  map f := ⟨f.restriction, f.comp_baseMap⟩
  map_id _ := Domain.Inclusion.ext rfl
  map_comp _ _ := Domain.Inclusion.ext rfl

@[simp] theorem toDomainFunctor_map_restriction {d e : RationalChart K A} (f : d ⟶ e) :
    ((toDomainFunctor K A).map f).restriction = f.restriction := rfl

/-- The inverse on homs retains the actual bounded algebra map and its equation
over the base, rather than choosing a map from a subset inclusion. -/
def fullyFaithfulToDomain (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (A : PresentedAffinoidAlgebra K) :
    (toDomainFunctor K A).FullyFaithful where
  preimage f := ⟨f.restriction, f.comp_baseMap⟩
  map_preimage _ := Domain.Inclusion.ext rfl
  preimage_map _ := Restriction.ext rfl

instance : (toDomainFunctor K A).Full := (fullyFaithfulToDomain K A).full

instance : (toDomainFunctor K A).Faithful := (fullyFaithfulToDomain K A).faithful

/-- The full domain universal property constructs the actual bounded
restriction associated to containment of rational loci. -/
def restrictionOfSubset (d e : RationalChart K A) (h : d.locus ⊆ e.locus) : d ⟶ e :=
  (fullyFaithfulToDomain K A).preimage
    (Domain.inclusionOfSubset d.toDomain e.toDomain h)

@[simp] theorem restrictionOfSubset_restriction (d e : RationalChart K A)
    (h : d.locus ⊆ e.locus) :
    (restrictionOfSubset d e h).restriction =
      (Domain.inclusionOfSubset d.toDomain e.toDomain h).restriction := rfl

theorem nonempty_hom_iff_subset (d e : RationalChart K A) :
    Nonempty (d ⟶ e) ↔ d.locus ⊆ e.locus :=
  ⟨fun ⟨f⟩ => f.subset, fun h => ⟨restrictionOfSubset d e h⟩⟩

@[simp] theorem restrictionOfSubset_self (d : RationalChart K A) :
    restrictionOfSubset d d (Set.Subset.refl _) = 𝟙 d :=
  @Subsingleton.elim (Restriction d d) inferInstance _ _

theorem restrictionOfSubset_comp (d e f : RationalChart K A)
    (h : d.locus ⊆ e.locus) (k : e.locus ⊆ f.locus) :
    restrictionOfSubset d e h ≫ restrictionOfSubset e f k =
      restrictionOfSubset d f (h.trans k) :=
  @Subsingleton.elim (Restriction d f) inferInstance _ _

/-- Equal rational loci give an isomorphism of the actual chart presentations,
by constructing bounded restrictions in both directions. -/
def isoOfLocusEq (d e : RationalChart K A) (h : d.locus = e.locus) : d ≅ e :=
  (fullyFaithfulToDomain K A).preimageIso
    (Domain.isoOfLocusEq d.toDomain e.toDomain h)

omit [CompleteSpace K] in
theorem locus_eq_of_iso {d e : RationalChart K A} (i : d ≅ e) :
    d.locus = e.locus :=
  Set.Subset.antisymm i.hom.subset i.inv.subset

theorem nonempty_iso_iff_locus_eq (d e : RationalChart K A) :
    Nonempty (d ≅ e) ↔ d.locus = e.locus :=
  ⟨fun ⟨i⟩ => locus_eq_of_iso i, fun h => ⟨isoOfLocusEq d e h⟩⟩

/-- The actual quotient algebras of equal-locus charts are boundedly equivalent
over the fixed base. -/
def boundedEquivOfLocusEq (d e : RationalChart K A) (h : d.locus = e.locus) :
    BoundedAlgEquiv K d.algebra e.algebra :=
  Domain.boundedEquivOfLocusEq d.toDomain e.toDomain h

@[simp] theorem boundedEquivOfLocusEq_apply (d e : RationalChart K A)
    (h : d.locus = e.locus) (a : d.algebra) :
    boundedEquivOfLocusEq d e h a = (isoOfLocusEq d e h).inv.restriction a := rfl

@[simp] theorem boundedEquivOfLocusEq_symm_apply (d e : RationalChart K A)
    (h : d.locus = e.locus) (b : e.algebra) :
    (boundedEquivOfLocusEq d e h).symm b = (isoOfLocusEq d e h).hom.restriction b := rfl

theorem boundedEquivOfLocusEq_comp_baseMap (d e : RationalChart K A)
    (h : d.locus = e.locus) :
    (boundedEquivOfLocusEq d e h).toBoundedAlgHom.comp d.baseMap = e.baseMap :=
  Domain.boundedEquivOfLocusEq_comp_baseMap d.toDomain e.toDomain h

theorem boundedEquivOfLocusEq_symm_comp_baseMap (d e : RationalChart K A)
    (h : d.locus = e.locus) :
    (boundedEquivOfLocusEq d e h).symm.toBoundedAlgHom.comp e.baseMap = d.baseMap :=
  Domain.boundedEquivOfLocusEq_symm_comp_baseMap d.toDomain e.toDomain h

theorem boundedHom_eq_boundedEquivOfLocusEq (d e : RationalChart K A)
    (h : d.locus = e.locus) (f : BoundedAlgHom K d.algebra e.algebra)
    (hf : f.comp d.baseMap = e.baseMap) :
    f = (boundedEquivOfLocusEq d e h).toBoundedAlgHom :=
  Domain.boundedHom_eq_boundedEquivOfLocusEq d.toDomain e.toDomain h f hf

/-- The bounded comparison induces a spectrum homeomorphism in the chart
direction. Its forward map comaps the inverse algebra comparison. -/
def spectrumHomeomorphOfLocusEq (d e : RationalChart K A) (h : d.locus = e.locus) :
    BanachSpectrum d.algebra ≃ₜ BanachSpectrum e.algebra :=
  Domain.spectrumHomeomorphOfLocusEq d.toDomain e.toDomain h

theorem spectrumHomeomorphOfLocusEq_over_base (d e : RationalChart K A)
    (h : d.locus = e.locus) (x : BanachSpectrum d.algebra) :
    e.spectrumMap (spectrumHomeomorphOfLocusEq d e h x) = d.spectrumMap x :=
  Domain.spectrumHomeomorphOfLocusEq_over_base d.toDomain e.toDomain h x

/-- The bridge retains the actual affinoid-space realization definitionally. -/
theorem toDomainFunctor_comp_toAffinoidSpace (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (A : PresentedAffinoidAlgebra K) :
    toDomainFunctor K A ⋙ Domain.toAffinoidSpace K A = toAffinoidSpace K A := rfl

/-- The bridge retains the actual bounded-seminorm spectrum realization. -/
theorem toDomainFunctor_comp_toTopologicalSpace (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (A : PresentedAffinoidAlgebra K) :
    toDomainFunctor K A ⋙ Domain.toTopologicalSpace K A = toTopologicalSpace K A := rfl

/-- The represented subspaces and their continuous inclusion maps are retained. -/
theorem toDomainFunctor_comp_locusFunctor (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] (A : PresentedAffinoidAlgebra K) :
    toDomainFunctor K A ⋙ Domain.locusFunctor K A = locusFunctor K A := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
