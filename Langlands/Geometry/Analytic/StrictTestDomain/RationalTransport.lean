import Langlands.Geometry.Analytic.StrictTestDomain.RationalAutomorphism

/-! # The transport category of actual rational domains -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain

open CategoryTheory

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

/-- Chosen rational presentations, now regarded as objects admitting
automorphism-labelled maps of their actual loci. -/
structure RationalTransport (P : PresentedStrictAffinoidAlgebra K) where
  data : RationalData K P

namespace RationalTransport

open RationalAutomorphism

variable {K} {P : PresentedStrictAffinoidAlgebra K}

/-- A label is retained even if its action on the locus is not faithful. -/
structure Hom (U V : RationalTransport K P) where
  label : Aut P
  mapsTo : ∀ x ∈ U.data.locus, label • x ∈ V.data.locus

@[ext] theorem Hom.ext {U V : RationalTransport K P} {f g : Hom U V}
    (h : f.label = g.label) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Composition acts first by the source arrow's label. -/
instance : Category (RationalTransport K P) where
  Hom := Hom
  id U := ⟨1, by intro x hx; simpa using hx⟩
  comp f g := ⟨g.label * f.label, by
    intro x hx
    simpa only [mul_smul] using g.mapsTo _ (f.mapsTo _ hx)⟩
  id_comp f := Hom.ext (mul_one _)
  comp_id f := Hom.ext (one_mul _)
  assoc f g h := Hom.ext (mul_assoc _ _ _).symm

@[simp] theorem id_label (U : RationalTransport K P) :
    (𝟙 U : U ⟶ U).label = 1 := rfl

@[simp] theorem comp_label {U V W : RationalTransport K P}
    (f : U ⟶ V) (g : V ⟶ W) : (f ≫ g).label = g.label * f.label := rfl

/-- An ordinary rational inclusion has identity label. -/
def inclusion : RationalData K P ⥤ RationalTransport K P where
  obj d := ⟨d⟩
  map f := ⟨1, by intro x hx; simpa using f.subset hx⟩
  map_id _ := Hom.ext rfl
  map_comp _ _ := Hom.ext (one_mul _).symm

/-- Moving a presentation by an automorphism gives an isomorphic transport object. -/
def translationIso (g : Aut P) (U : RationalTransport K P) :
    U ≅ ⟨g • U.data⟩ where
  hom := ⟨g, fun x hx => (smul_mem_smul_locus_iff g U.data x).mpr hx⟩
  inv := ⟨g⁻¹, by
    intro x hx
    exact (smul_mem_smul_locus_iff g U.data (g⁻¹ • x)).mp (by simpa using hx)⟩
  hom_inv_id := Hom.ext (inv_mul_cancel g)
  inv_hom_id := Hom.ext (mul_inv_cancel g)

variable [CompleteSpace K]

namespace Hom

variable {U V W : RationalTransport K P}

/-- The twisted structural map has spectrum image in the target rational locus. -/
theorem twistedBaseMap_hasImageIn (f : U ⟶ V) :
    HasImageIn K (U.data.baseMap.comp f.label.inv) V.data.locus := by
  intro x
  exact f.mapsTo _ (U.data.baseMap_hasImageIn x)

/-- The rational universal property constructs the unique bounded algebra map
over the inverse algebra automorphism. -/
theorem existsUnique_restriction (f : U ⟶ V) :
    ∃! φ : BoundedAlgHom K V.data.algebra U.data.algebra,
      φ.comp V.data.baseMap = U.data.baseMap.comp f.label.inv :=
  (rationalRepresentation K P V.data).2.2 U.data.algebra
    (U.data.baseMap.comp f.label.inv) f.twistedBaseMap_hasImageIn

/-- Pull an actual quotient section back along a labelled rational-domain map. -/
def restriction (f : U ⟶ V) : BoundedAlgHom K V.data.algebra U.data.algebra :=
  f.existsUnique_restriction.choose

@[simp] theorem restriction_comp_baseMap (f : U ⟶ V) :
    f.restriction.comp V.data.baseMap = U.data.baseMap.comp f.label.inv :=
  f.existsUnique_restriction.choose_spec.1

theorem restriction_unique (f : U ⟶ V)
    {φ : BoundedAlgHom K V.data.algebra U.data.algebra}
    (hφ : φ.comp V.data.baseMap = U.data.baseMap.comp f.label.inv) :
    φ = f.restriction :=
  f.existsUnique_restriction.choose_spec.2 φ hφ

@[simp] theorem restriction_id (U : RationalTransport K P) :
    (𝟙 U : U ⟶ U).restriction = BoundedAlgHom.id K U.data.algebra := by
  apply ((𝟙 U : U ⟶ U).restriction_unique ?_).symm
  rfl

/-- The constructed maps are contravariantly functorial. -/
@[simp] theorem restriction_comp (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).restriction = f.restriction.comp g.restriction := by
  apply ((f ≫ g).restriction_unique ?_).symm
  calc
    (f.restriction.comp g.restriction).comp W.data.baseMap =
        f.restriction.comp (V.data.baseMap.comp g.label.inv) := by
          rw [BoundedAlgHom.comp_assoc, g.restriction_comp_baseMap]
    _ = (U.data.baseMap.comp f.label.inv).comp g.label.inv := by
          rw [← BoundedAlgHom.comp_assoc, f.restriction_comp_baseMap]
    _ = U.data.baseMap.comp (f ≫ g).label.inv := rfl

/-- On the actual quotient spectra, the restriction lies over the labelled
point action on the base spectrum. -/
theorem spectrumMap_restriction (f : U ⟶ V) (x : BanachSpectrum U.data.algebra) :
    V.data.spectrumMap (BanachSpectrum.comap f.restriction.toBoundedRingHom x) =
      f.label • U.data.spectrumMap x := by
  apply BanachSpectrum.ext
  intro a
  exact congrArg (fun φ : BoundedAlgHom K P U.data.algebra => x (φ a))
    f.restriction_comp_baseMap

end Hom

/-- Identity-labelled arrows recover the published bounded restrictions. -/
@[simp] theorem inclusion_restriction {d e : RationalData K P} (f : d ⟶ e) :
    (inclusion.map f).restriction = f.restriction := by
  apply ((inclusion.map f).restriction_unique ?_).symm
  exact f.restriction_comp_baseMap

/-- The inverse translation arrow pulls sections forward by the published
bounded comparison map. -/
@[simp] theorem translationIso_inv_restriction (g : Aut P) (U : RationalTransport K P) :
    (translationIso g U).inv.restriction = U.data.comparison g.hom := by
  apply ((translationIso g U).inv.restriction_unique ?_).symm
  exact U.data.comparison_comp_baseMap g.hom

/-- The rational transport category is realized by actual affinoid spectra and
the contravariant bounded maps of their constructed algebras. -/
def toAffinoidSpace : RationalTransport K P ⥤ PresentedStrictAffinoidSpace K where
  obj U := Opposite.op U.data.algebra
  map f := Quiver.Hom.op f.restriction
  map_id U := by
    change Quiver.Hom.op _ = Quiver.Hom.op _
    rw [Hom.restriction_id]
    rfl
  map_comp f g := by
    change Quiver.Hom.op _ = Quiver.Hom.op _
    rw [Hom.restriction_comp]
    rfl

/-- The actual multiplicative spectra and their continuous point maps. -/
def toTopologicalSpace : RationalTransport K P ⥤ TopCat :=
  toAffinoidSpace ⋙ strictAffinoidSpectrumFunctor K

/-- The bounded-algebra-valued presheaf on all labelled transport arrows. -/
def boundedPresheaf : (RationalTransport K P)ᵒᵖ ⥤ PresentedStrictAffinoidAlgebra K where
  obj U := U.unop.data.algebra
  map f := f.unop.restriction
  map_id U := Hom.restriction_id U.unop
  map_comp f g := Hom.restriction_comp g.unop f.unop

/-- Forgetting the norms retains an actual commutative algebra presheaf. -/
def algebraPresheaf : (RationalTransport K P)ᵒᵖ ⥤ CommAlgCat K :=
  boundedPresheaf ⋙ PresentedStrictAffinoidAlgebra.toCommAlgCat K

end RationalTransport
end Langlands.Analytic.StrictTestDomain
