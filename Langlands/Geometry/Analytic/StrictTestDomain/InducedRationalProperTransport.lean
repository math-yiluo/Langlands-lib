import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCompactSupport
import Langlands.Sheaf.Equivariant.SmoothPart
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Proper transport of the actual induced rational spectra -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Langlands.Sheaf.Equivariant

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace OpenSubgroupTransport

/-- Properness is tested on the already constructed map of balanced rational spectra. -/
def properInducedMap (ρ : RationalSpectralAction G P) :
    MorphismProperty ρ.OpenSubgroupTransport :=
  fun _ _ f => IsProperMap f.inducedMap

instance properInducedMap_isMultiplicative (ρ : RationalSpectralAction G P) :
    (properInducedMap ρ).IsMultiplicative where
  id_mem X := Hom.isProperMap_inducedMap_id X
  comp_mem f g hf hg := Hom.isProperMap_inducedMap_comp f g hf hg

/-- All original rational transport objects, retaining exactly the proper induced arrows. -/
abbrev ProperTransport (ρ : RationalSpectralAction G P) :=
  WideSubcategory (properInducedMap ρ)

/-- Forget the properness witness, retaining the original rational transport arrow. -/
def properTransportInclusion (ρ : RationalSpectralAction G P) :
    ProperTransport ρ ⥤ ρ.OpenSubgroupTransport :=
  wideSubcategoryInclusion (properInducedMap ρ)

instance instInducedRationalProperTransport1 (ρ : RationalSpectralAction G P) : (properTransportInclusion ρ).Faithful :=
  inferInstanceAs (wideSubcategoryInclusion (properInducedMap ρ)).Faithful

/-- The stable-neighbourhood property is a property of the actual induced spectrum. -/
def stableProperTransportProperty (ρ : RationalSpectralAction G P) :
    ObjectProperty (ProperTransport ρ) :=
  fun X => HasStableNeighbourhoods G X.obj.InducedSpectrum

/-- The full subcategory on actual spectra with stable neighbourhoods. -/
abbrev SmoothProperTransport (ρ : RationalSpectralAction G P) :=
  (stableProperTransportProperty ρ).FullSubcategory

namespace SmoothProperTransport

variable {ρ : RationalSpectralAction G P}

/-- Recover the original subgroup and rational-domain transport object. -/
abbrev transport (X : SmoothProperTransport ρ) : ρ.OpenSubgroupTransport :=
  X.obj.obj

instance instInducedRationalProperTransport2 (X : SmoothProperTransport ρ) :
    HasStableNeighbourhoods G X.transport.InducedSpectrum :=
  X.property

/-- Include an original object when its actual spectrum has stable neighbourhoods. -/
def ofTransport (X : ρ.OpenSubgroupTransport)
    [HasStableNeighbourhoods G X.InducedSpectrum] : SmoothProperTransport ρ :=
  ⟨⟨X⟩, show HasStableNeighbourhoods G X.InducedSpectrum from inferInstance⟩

/-- The faithful forgetful functor retains all original subgroup and domain data. -/
def forget (ρ : RationalSpectralAction G P) :
    SmoothProperTransport ρ ⥤ ρ.OpenSubgroupTransport :=
  (stableProperTransportProperty ρ).ι ⋙ properTransportInclusion ρ

instance instInducedRationalProperTransport3 : (forget ρ).Faithful :=
  inferInstanceAs ((stableProperTransportProperty ρ).ι ⋙ properTransportInclusion ρ).Faithful

namespace Hom

variable {X Y Z : SmoothProperTransport ρ}

/-- The original transport arrow underlying an arrow in the proper smooth category. -/
abbrev transport (f : X ⟶ Y) : X.transport ⟶ Y.transport :=
  f.hom.hom

theorem isProperMap_inducedMap (f : X ⟶ Y) : IsProperMap (transport f).inducedMap :=
  f.hom.property

/-- Every proper original transport arrow between these objects is retained. -/
def ofTransport (f : X.transport ⟶ Y.transport) (hf : IsProperMap f.inducedMap) : X ⟶ Y :=
  ObjectProperty.homMk ⟨f, hf⟩

@[simp]
theorem transport_id (X : SmoothProperTransport ρ) :
    transport (𝟙 X) = 𝟙 X.transport := rfl

@[simp]
theorem transport_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    transport (f ≫ g) = transport f ≫ transport g := rfl

@[simp]
theorem transport_ofTransport (f : X.transport ⟶ Y.transport)
    (hf : IsProperMap f.inducedMap) : transport (ofTransport f hf) = f := rfl

end Hom

/-- The original continuous full-group action diagram on the proper smooth category. -/
def spectrumDiagram (ρ : RationalSpectralAction G P) :
    SmoothProperTransport ρ ⥤ ContAction TopCat.{max u v} G :=
  forget ρ ⋙ inducedSpectrumFunctor

end SmoothProperTransport

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
