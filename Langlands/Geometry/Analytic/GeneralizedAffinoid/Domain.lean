import Langlands.Geometry.Analytic.GeneralizedAffinoid.Banach
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-! # Domain representations tested on all presented affinoids -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory CategoryTheory.Limits

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

/-- Image containment for the actual contravariant spectrum map. -/
def HasImageIn {A B : PresentedAffinoidAlgebra K}
    (φ : BoundedAlgHom K A B) (U : Set (BanachSpectrum A)) : Prop :=
  ∀ x : BanachSpectrum B, BanachSpectrum.comap φ.toBoundedRingHom x ∈ U

/-- A specified actual affinoid map represents a closed subset against every
finite positive-polyradius affinoid test, with no strictness restriction. -/
def Represents [CompleteSpace K] {A B : PresentedAffinoidAlgebra K}
    (i : BoundedAlgHom K A B) (U : Set (BanachSpectrum A)) : Prop :=
  IsClosed U ∧
  Set.range (BanachSpectrum.comap i.toBoundedRingHom) = U ∧
  ∀ (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K A R),
    HasImageIn K φ U →
    ∃! ψ : BoundedAlgHom K B R, ψ.comp i = φ

variable [CompleteSpace K]

/-- A chosen full domain representation over the actual fixed base algebra.
The carrier and bounded structural map are part of the data. -/
structure Domain (A : PresentedAffinoidAlgebra K) where
  algebra : PresentedAffinoidAlgebra K
  baseMap : BoundedAlgHom K A algebra
  locus : Set (BanachSpectrum A)
  represents : Represents K baseMap locus

variable {K}

omit [CompleteSpace K] in
private theorem spectrum_comp {A B C : PresentedAffinoidAlgebra K}
    (i : BoundedAlgHom K A B) (j : BoundedAlgHom K B C) (x : BanachSpectrum C) :
    BanachSpectrum.comap (j.comp i).toBoundedRingHom x =
      BanachSpectrum.comap i.toBoundedRingHom
        (BanachSpectrum.comap j.toBoundedRingHom x) := by
  apply BanachSpectrum.ext
  intro a
  rfl

/-- Every representing map has the stated spectrum image containment. -/
theorem Represents.hasImageIn {A B : PresentedAffinoidAlgebra K}
    {i : BoundedAlgHom K A B} {U : Set (BanachSpectrum A)}
    (hi : Represents K i U) : HasImageIn K i U := by
  intro x
  rw [← hi.2.1]
  exact ⟨x, rfl⟩

/-- The actual bounded identity represents the whole spectrum against every
positive-polyradius affinoid test. -/
theorem represents_id (A : PresentedAffinoidAlgebra K) :
    Represents K (BoundedAlgHom.id K A) Set.univ := by
  refine ⟨isClosed_univ, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    exact ⟨x, BanachSpectrum.ext fun _ => rfl⟩
  · intro R φ _
    exact ⟨φ, BoundedAlgHom.comp_id φ, fun ψ hψ => by simpa using hψ⟩

namespace Domain

variable {A : PresentedAffinoidAlgebra K}

/-- The structural continuous map on actual bounded multiplicative spectra. -/
def spectrumMap (U : Domain K A) :
    C(BanachSpectrum U.algebra, BanachSpectrum A) :=
  BanachSpectrum.comapContinuous U.baseMap.toBoundedRingHom

/-- The forward map to the represented closed subspace. -/
def spectrumToLocus (U : Domain K A) :
    C(BanachSpectrum U.algebra, U.locus) where
  toFun x := ⟨U.spectrumMap x, U.represents.hasImageIn x⟩
  continuous_toFun := U.spectrumMap.continuous.subtype_mk _

theorem spectrumToLocus_surjective (U : Domain K A) :
    Function.Surjective U.spectrumToLocus := by
  intro x
  have hx : (x : BanachSpectrum A) ∈
      Set.range (BanachSpectrum.comap U.baseMap.toBoundedRingHom) := by
    rw [U.represents.2.1]
    exact x.property
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

/-- Arrows store actual bounded restrictions in the opposite algebra direction,
with their equation over the fixed base. -/
structure Inclusion (U V : Domain K A) where
  restriction : BoundedAlgHom K V.algebra U.algebra
  comp_baseMap : restriction.comp V.baseMap = U.baseMap

namespace Inclusion

variable {U V W : Domain K A}

@[ext] theorem ext {f g : Inclusion U V}
    (h : f.restriction = g.restriction) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- An actual bounded restriction entails containment of the represented loci. -/
theorem subset (f : Inclusion U V) : U.locus ⊆ V.locus := by
  intro x hx
  obtain ⟨y, rfl⟩ := U.represents.2.1.symm ▸ hx
  have h := V.represents.hasImageIn
    (BanachSpectrum.comap f.restriction.toBoundedRingHom y)
  rw [← spectrum_comp, f.comp_baseMap] at h
  exact h

/-- The full affinoid-test universal property proves uniqueness of restrictions. -/
instance : Subsingleton (Inclusion U V) := ⟨fun f g => by
  apply ext
  exact (V.represents.2.2 U.algebra U.baseMap
    (fun x => f.subset (U.represents.hasImageIn x))).unique
      f.comp_baseMap g.comp_baseMap⟩

end Inclusion

/-- The category of actual domain representations and bounded restrictions. -/
instance : Category (Domain K A) where
  Hom U V := Inclusion U V
  id U := ⟨BoundedAlgHom.id K U.algebra, by rfl⟩
  comp f g := ⟨f.restriction.comp g.restriction, by
    change f.restriction.comp (g.restriction.comp _) = _
    rw [g.comp_baseMap, f.comp_baseMap]⟩
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

/-- Full affinoid-test representation constructs the bounded restriction from
containment, by testing the larger locus on the smaller domain algebra. -/
def inclusionOfSubset (U V : Domain K A) (h : U.locus ⊆ V.locus) : U ⟶ V := by
  have hφ : HasImageIn K U.baseMap V.locus :=
    fun x => h (U.represents.hasImageIn x)
  have hex := V.represents.2.2 U.algebra U.baseMap hφ
  exact ⟨hex.choose, hex.choose_spec.1⟩

theorem nonempty_hom_iff_subset (U V : Domain K A) :
    Nonempty (U ⟶ V) ↔ U.locus ⊆ V.locus :=
  ⟨fun ⟨f⟩ => f.subset, fun h => ⟨inclusionOfSubset U V h⟩⟩

namespace Inclusion

variable {U V W : Domain K A}

@[simp] theorem restriction_id (U : Domain K A) :
    (𝟙 U : U ⟶ U).restriction = BoundedAlgHom.id K U.algebra := rfl

@[simp] theorem restriction_comp (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).restriction = f.restriction.comp g.restriction := rfl

/-- Pull back actual bounded multiplicative seminorms along the restriction. -/
def spectrumMap (f : U ⟶ V) :
    C(BanachSpectrum U.algebra, BanachSpectrum V.algebra) :=
  BanachSpectrum.comapContinuous f.restriction.toBoundedRingHom

theorem spectrumMap_over_base (f : U ⟶ V) (x : BanachSpectrum U.algebra) :
    V.spectrumMap (f.spectrumMap x) = U.spectrumMap x := by
  apply BanachSpectrum.ext
  intro a
  exact congrArg (fun φ : BoundedAlgHom K A U.algebra => x (φ a)) f.comp_baseMap

/-- The continuous inclusion of the represented base subspaces. -/
def locusMap (f : U ⟶ V) : C(U.locus, V.locus) where
  toFun x := ⟨x.val, f.subset x.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

theorem spectrumToLocus_naturality (f : U ⟶ V) (x : BanachSpectrum U.algebra) :
    V.spectrumToLocus (f.spectrumMap x) = f.locusMap (U.spectrumToLocus x) :=
  Subtype.ext (f.spectrumMap_over_base x)

end Inclusion

variable (K A)

/-- An actual full domain representation supplied by the base algebra itself. -/
def whole : Domain K A where
  algebra := A
  baseMap := BoundedAlgHom.id K A
  locus := Set.univ
  represents := represents_id A

/-- The constructed whole-spectrum domain is terminal for actual restrictions. -/
def wholeIsTerminal : IsTerminal (whole K A) :=
  IsTerminal.ofUniqueHom (fun U => inclusionOfSubset U (whole K A) (Set.subset_univ _))
    (fun U f => (inferInstance : Subsingleton (Inclusion U (whole K A))).elim f _)

/-- Realize domain representations by their actual quotient algebras and maps. -/
def toAffinoidSpace : Domain K A ⥤ PresentedAffinoidSpace K where
  obj U := Opposite.op U.algebra
  map f := Quiver.Hom.op f.restriction
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The actual spectrum realization of the category of domain representations. -/
def toTopologicalSpace : Domain K A ⥤ TopCat :=
  toAffinoidSpace K A ⋙ affinoidSpectrumFunctor K

/-- The represented closed subsets with their continuous inclusion maps. -/
def locusFunctor : Domain K A ⥤ TopCat where
  obj U := TopCat.of U.locus
  map f := TopCat.ofHom f.locusMap
  map_id U := by
    apply TopCat.ext
    intro x
    rfl
  map_comp f g := by
    apply TopCat.ext
    intro x
    rfl

/-- The structural spectrum maps form a natural transformation to the loci. -/
def spectrumToLocusNat : toTopologicalSpace K A ⟶ locusFunctor K A where
  app U := TopCat.ofHom U.spectrumToLocus
  naturality U V f := by
    apply TopCat.ext
    intro x
    exact f.spectrumToLocus_naturality x

end Domain
end Langlands.Analytic.PresentedAffinoidAlgebra
