import Langlands.Geometry.Analytic.GeneralizedAffinoid.Domain

/-! # Actual bounded comparisons of full affinoid-domain representations -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

/-- Equal represented loci construct an isomorphism of the actual domain
representations, using the full universal properties in both directions. -/
def isoOfLocusEq (U V : Domain K A) (h : U.locus = V.locus) : U ≅ V where
  hom := inclusionOfSubset U V (fun _ hx => h ▸ hx)
  inv := inclusionOfSubset V U (fun _ hx => h.symm ▸ hx)
  hom_inv_id := (inferInstance : Subsingleton (Inclusion U U)).elim _ _
  inv_hom_id := (inferInstance : Subsingleton (Inclusion V V)).elim _ _

/-- An isomorphism entails equality of the actual represented subsets. -/
theorem locus_eq_of_iso {U V : Domain K A} (e : U ≅ V) :
    U.locus = V.locus :=
  Set.Subset.antisymm e.hom.subset e.inv.subset

theorem nonempty_iso_iff_locus_eq (U V : Domain K A) :
    Nonempty (U ≅ V) ↔ U.locus = V.locus :=
  ⟨fun ⟨e⟩ => locus_eq_of_iso e, fun h => ⟨isoOfLocusEq U V h⟩⟩

/-- The inverse space arrow supplies the forward bounded algebra map.
Both inverse identities are consequences of the actual domain category. -/
def boundedEquivOfIso {U V : Domain K A} (e : U ≅ V) :
    BoundedAlgEquiv K U.algebra V.algebra :=
  BoundedAlgEquiv.ofHomInv e.inv.restriction e.hom.restriction
    (fun a => congrArg (fun f : U ⟶ U => f.restriction a) e.hom_inv_id)
    (fun b => congrArg (fun f : V ⟶ V => f.restriction b) e.inv_hom_id)

@[simp] theorem boundedEquivOfIso_apply {U V : Domain K A} (e : U ≅ V)
    (a : U.algebra) :
    boundedEquivOfIso e a = e.inv.restriction a := rfl

@[simp] theorem boundedEquivOfIso_symm_apply {U V : Domain K A} (e : U ≅ V)
    (b : V.algebra) :
    (boundedEquivOfIso e).symm b = e.hom.restriction b := rfl

theorem boundedEquivOfIso_comp_baseMap {U V : Domain K A} (e : U ≅ V) :
    (boundedEquivOfIso e).toBoundedAlgHom.comp U.baseMap = V.baseMap := by
  change e.inv.restriction.comp U.baseMap = V.baseMap
  exact e.inv.comp_baseMap

theorem boundedEquivOfIso_symm_comp_baseMap {U V : Domain K A} (e : U ≅ V) :
    (boundedEquivOfIso e).symm.toBoundedAlgHom.comp V.baseMap = U.baseMap := by
  change e.hom.restriction.comp V.baseMap = U.baseMap
  exact e.hom.comp_baseMap

/-- The actual quotient algebras of equal-locus representations are boundedly
equivalent over the base. The bounds come from their constructed restrictions. -/
def boundedEquivOfLocusEq (U V : Domain K A) (h : U.locus = V.locus) :
    BoundedAlgEquiv K U.algebra V.algebra :=
  boundedEquivOfIso (isoOfLocusEq U V h)

theorem boundedEquivOfLocusEq_comp_baseMap (U V : Domain K A)
    (h : U.locus = V.locus) :
    (boundedEquivOfLocusEq U V h).toBoundedAlgHom.comp U.baseMap = V.baseMap :=
  boundedEquivOfIso_comp_baseMap (isoOfLocusEq U V h)

theorem boundedEquivOfLocusEq_symm_comp_baseMap (U V : Domain K A)
    (h : U.locus = V.locus) :
    (boundedEquivOfLocusEq U V h).symm.toBoundedAlgHom.comp V.baseMap = U.baseMap :=
  boundedEquivOfIso_symm_comp_baseMap (isoOfLocusEq U V h)

/-- The representation property gives uniqueness even among all bounded maps
over the base, without requiring a competing map to be invertible. -/
theorem boundedHom_eq_of_over_base (U V : Domain K A)
    (f g : BoundedAlgHom K U.algebra V.algebra)
    (hf : f.comp U.baseMap = V.baseMap) (hg : g.comp U.baseMap = V.baseMap) :
    f = g := by
  have h : (⟨f, hf⟩ : Inclusion V U) = ⟨g, hg⟩ := Subsingleton.elim _ _
  exact congrArg Inclusion.restriction h

theorem boundedHom_eq_boundedEquivOfLocusEq (U V : Domain K A)
    (h : U.locus = V.locus) (f : BoundedAlgHom K U.algebra V.algebra)
    (hf : f.comp U.baseMap = V.baseMap) :
    f = (boundedEquivOfLocusEq U V h).toBoundedAlgHom :=
  boundedHom_eq_of_over_base U V f _ hf (boundedEquivOfLocusEq_comp_baseMap U V h)

/-- The same actual quotient rings have homeomorphic norm topologies.
No isometric or contractive comparison is asserted. -/
def algebraHomeomorphOfLocusEq (U V : Domain K A) (h : U.locus = V.locus) :
    U.algebra ≃ₜ V.algebra :=
  (boundedEquivOfLocusEq U V h).toHomeomorph

/-- Contravariant comap along the bounded comparison gives an actual spectrum
homeomorphism in the space direction. -/
def spectrumHomeomorphOfLocusEq (U V : Domain K A) (h : U.locus = V.locus) :
    BanachSpectrum U.algebra ≃ₜ BanachSpectrum V.algebra :=
  (boundedEquivOfLocusEq U V h).spectrumHomeomorph.symm

theorem spectrumHomeomorphOfLocusEq_over_base (U V : Domain K A)
    (h : U.locus = V.locus) (x : BanachSpectrum U.algebra) :
    V.spectrumMap (spectrumHomeomorphOfLocusEq U V h x) = U.spectrumMap x := by
  apply BanachSpectrum.ext
  intro a
  exact congrArg (fun f : BoundedAlgHom K A U.algebra => x (f a))
    (boundedEquivOfLocusEq_symm_comp_baseMap U V h)

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
