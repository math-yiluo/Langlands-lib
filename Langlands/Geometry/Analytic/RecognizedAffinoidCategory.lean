import Langlands.Geometry.Analytic.SpecialAffinoidRecognition
import Langlands.Geometry.Analytic.SaturatedAtlasDomainClosure
import Mathlib.Topology.Category.TopCat.ULift

/-! # Actual bounded restrictions and full-net recognized affinoid subsets -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Literal special subsets satisfying the three intrinsic recognition
conditions, with no supplied presented-algebra or chart output. -/
abbrev RecognizedSubset := {W : a.SpecialSubset // W.IsRecognized}

namespace RecognizedSubset

variable {a} (U V W : a.RecognizedSubset)

def locus : Set X := U.val.val

instance : CompactSpace U.locus := inferInstanceAs (CompactSpace U.val.val)

instance : T2Space U.locus := inferInstanceAs (T2Space U.val.val)

abbrev algebra : PresentedAffinoidAlgebra K := U.property.algebra

def chart : C(BanachSpectrum U.algebra, X) := U.property.chart

theorem isEmbedding_chart : Topology.IsEmbedding U.chart := U.property.isEmbedding_chart

theorem range_chart : Set.range U.chart = U.locus := U.property.range_chart

def coordinates : U.locus ≃ₜ BanachSpectrum U.algebra :=
  U.val.coordinates U.property.affinoid U.property.bijective

/-- Conjugate the already constructed special-section restriction by
the two constructed bounded finite-presentation equivalences. -/
def restriction (h : U.locus ⊆ V.locus) : BoundedAlgHom K V.algebra U.algebra :=
  U.property.algebraEquiv.symm.toBoundedAlgHom.comp
    ((U.val.restriction V.val h).comp V.property.algebraEquiv.toBoundedAlgHom)

@[simp]
theorem restriction_self :
    U.restriction U Subset.rfl = BoundedAlgHom.id K U.algebra := by
  apply BoundedAlgHom.ext
  intro b
  change U.property.algebraEquiv.symm
    (U.val.restriction U.val Subset.rfl (U.property.algebraEquiv b)) = b
  rw [U.val.restriction_self, BoundedAlgHom.id_apply,
    U.property.algebraEquiv.symm_apply_apply]

theorem restriction_comp (hUV : U.locus ⊆ V.locus) (hVW : V.locus ⊆ W.locus) :
    (U.restriction V hUV).comp (V.restriction W hVW) =
      U.restriction W (hUV.trans hVW) := by
  apply BoundedAlgHom.ext
  intro b
  change U.property.algebraEquiv.symm
    (U.val.restriction V.val hUV
      (V.property.algebraEquiv
        (V.property.algebraEquiv.symm
          (V.val.restriction W.val hVW (W.property.algebraEquiv b))))) =
    U.property.algebraEquiv.symm
      (U.val.restriction W.val (hUV.trans hVW) (W.property.algebraEquiv b))
  rw [V.property.algebraEquiv.apply_symm_apply]
  exact congrArg U.property.algebraEquiv.symm
    (congrArg
      (fun f : BoundedAlgHom K W.val.SectionAlgebra U.val.SectionAlgebra =>
        f (W.property.algebraEquiv b))
      (W.val.restriction_comp U.val V.val hUV hVW))

/-- The actual bounded restrictions identify canonical coordinates along
the literal subspace inclusion. -/
theorem coordinates_restriction (h : U.locus ⊆ V.locus) (x : U.locus) :
    BanachSpectrum.comap (U.restriction V h).toBoundedRingHom (U.coordinates x) =
      V.coordinates ⟨x.val, h x.property⟩ := by
  apply BanachSpectrum.ext
  intro b
  change U.val.spectrumMap x
    (U.property.algebraEquiv
      (U.property.algebraEquiv.symm
        (U.val.restriction V.val h (V.property.algebraEquiv b)))) =
    V.val.spectrumMap ⟨x.val, h x.property⟩ (V.property.algebraEquiv b)
  rw [U.property.algebraEquiv.apply_symm_apply]
  exact congrArg (fun y : BanachSpectrum V.val.SectionAlgebra =>
    y (V.property.algebraEquiv b)) (U.val.comap_spectrumMap V.val h x)

theorem chart_restriction (h : U.locus ⊆ V.locus) (x : BanachSpectrum U.algebra) :
    V.chart (BanachSpectrum.comap (U.restriction V h).toBoundedRingHom x) =
      U.chart x := by
  let y := U.coordinates.symm x
  have hx : U.coordinates y = x := U.coordinates.apply_symm_apply x
  rw [← hx, U.coordinates_restriction V h y]
  change (V.coordinates.symm (V.coordinates ⟨y.val, h y.property⟩)).val =
    (U.coordinates.symm (U.coordinates y)).val
  rw [V.coordinates.symm_apply_apply, U.coordinates.symm_apply_apply]

/-- An inclusion determines its actual bounded restriction by construction. -/
structure Inclusion (U V : a.RecognizedSubset) : Type where
  subset : U.locus ⊆ V.locus

namespace Inclusion

variable {U V W}

instance : Subsingleton (Inclusion U V) := ⟨fun f g => by cases f; cases g; rfl⟩

def restriction (f : Inclusion U V) : BoundedAlgHom K V.algebra U.algebra :=
  U.restriction V f.subset

end Inclusion

/-- The thin category realizes every literal inclusion by its constructed
bounded contravariant algebra map. -/
instance : Category (a.RecognizedSubset) where
  Hom := Inclusion
  id _ := ⟨Subset.rfl⟩
  comp f g := ⟨f.subset.trans g.subset⟩
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

namespace Inclusion

variable {U V W}

@[simp]
theorem restriction_id :
    (𝟙 U : U ⟶ U).restriction = BoundedAlgHom.id K U.algebra :=
  U.restriction_self

@[simp]
theorem restriction_comp (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).restriction = f.restriction.comp g.restriction :=
  (U.restriction_comp V W f.subset g.subset).symm

def spectrumMap (f : U ⟶ V) : C(BanachSpectrum U.algebra, BanachSpectrum V.algebra) :=
  BanachSpectrum.comapContinuous f.restriction.toBoundedRingHom

def locusMap (f : U ⟶ V) : C(U.locus, V.locus) where
  toFun x := ⟨x.val, f.subset x.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

theorem chart_naturality (f : U ⟶ V) (x : BanachSpectrum U.algebra) :
    V.chart (f.spectrumMap x) = U.chart x :=
  U.chart_restriction V f.subset x

theorem coordinates_naturality (f : U ⟶ V) (x : U.locus) :
    f.spectrumMap (U.coordinates x) = V.coordinates (f.locusMap x) :=
  U.coordinates_restriction V f.subset x

end Inclusion

variable (a)

/-- Realization by the actual finite quotient algebras and full bounded maps. -/
def toAffinoidSpace : a.RecognizedSubset ⥤ PresentedAffinoidSpace K where
  obj U := Opposite.op U.algebra
  map f := Quiver.Hom.op f.restriction
  map_id U := congrArg Quiver.Hom.op (Inclusion.restriction_id (U := U))
  map_comp f g := congrArg Quiver.Hom.op (Inclusion.restriction_comp f g)

def toTopologicalSpace : a.RecognizedSubset ⥤ TopCat.{u} :=
  toAffinoidSpace a ⋙ affinoidSpectrumFunctor K

def boundedPresheaf : (a.RecognizedSubset)ᵒᵖ ⥤ PresentedAffinoidAlgebra K where
  obj U := U.unop.algebra
  map f := f.unop.restriction
  map_id U := Inclusion.restriction_id (U := U.unop)
  map_comp f g := Inclusion.restriction_comp g.unop f.unop

def locusFunctor : a.RecognizedSubset ⥤ TopCat.{v} where
  obj U := TopCat.of U.locus
  map f := TopCat.ofHom f.locusMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Coordinates identify the entire actual inclusion diagram with the
spectra of its constructed presented algebras. -/
def coordinatesNatIso :
    locusFunctor a ⋙ TopCat.uliftFunctor.{u, v} ≅
      toTopologicalSpace a ⋙ TopCat.uliftFunctor.{v, u} :=
  NatIso.ofComponents (fun U => TopCat.isoOfHomeo
    ((TopCat.of U.locus).uliftFunctorObjHomeo.symm.trans
      (U.coordinates.trans (TopCat.of (BanachSpectrum U.algebra)).uliftFunctorObjHomeo)))
    (by
      intro U V f
      apply TopCat.ext
      intro x
      change ULift.up (V.coordinates (f.locusMap x.down)) =
        ULift.up (f.spectrumMap (U.coordinates x.down))
      exact congrArg ULift.up (f.coordinates_naturality x.down).symm)

end RecognizedSubset

/-- Special subsets for the already constructed enlarged full local-domain
atlas: this realizes covers from the barred net in the source. -/
abbrev FullSpecialSubset := a.saturatedAtlas.SpecialSubset

/-- Apply the three-condition recognition construction to special covers
from the full local-domain net, rather than the smaller original net. -/
abbrev RecognizedAffinoidSubset := a.saturatedAtlas.RecognizedSubset

/-- Every actual original local-domain presentation determines a recognized
subset of the full-net family, using its singleton special covering. -/
def recognizedLocalDomain (U : LocalDomain a) : a.RecognizedAffinoidSubset :=
  ⟨SpecialSubset.original a.saturatedAtlas ⟨U.locus, ⟨U, rfl⟩⟩,
    SpecialSubset.original_isRecognized a.saturatedAtlas ⟨U.locus, ⟨U, rfl⟩⟩⟩

theorem recognizedLocalDomain_locus (U : LocalDomain a) :
    (a.recognizedLocalDomain U).locus = U.locus :=
  a.range_saturatedChart ⟨U.locus, ⟨U, rfl⟩⟩

/-- Its presented algebra is actually bounded equivalent to the unchanged
local-domain algebra; both comparisons are constructed. -/
def recognizedLocalDomainAlgebraEquiv (U : LocalDomain a) :
    BoundedAlgEquiv K U.algebra (a.recognizedLocalDomain U).algebra :=
  (a.localDomainSaturatedEquiv U).trans
    ((SpecialSubset.originalAlgebraEquiv a.saturatedAtlas ⟨U.locus, ⟨U, rfl⟩⟩).trans
      (a.recognizedLocalDomain U).property.algebraEquiv.symm)

def recognizedAffinoidFamily : Set (Set X) :=
  Set.range (fun W : a.RecognizedAffinoidSubset => W.locus)

theorem localDomainFamily_subset_recognizedAffinoidFamily :
    a.localDomainFamily ⊆ a.recognizedAffinoidFamily := by
  rintro S ⟨U, rfl⟩
  exact ⟨a.recognizedLocalDomain U, a.recognizedLocalDomain_locus U⟩

/-- The full recognized family is a quasinet since it contains the
already proved enlarged full-domain net. -/
theorem isQuasinet_recognizedAffinoidFamily :
    AtlasTopology.IsQuasinet a.recognizedAffinoidFamily :=
  a.isQuasinet_localDomainFamily.mono a.localDomainFamily_subset_recognizedAffinoidFamily

theorem isCompactFamily_recognizedAffinoidFamily :
    AtlasTopology.IsCompactFamily a.recognizedAffinoidFamily := by
  rintro S ⟨W, rfl⟩
  exact ⟨isCompact_iff_compactSpace.mpr inferInstance, inferInstance⟩

end Langlands.Analytic.IndexedAffinoidAtlas
