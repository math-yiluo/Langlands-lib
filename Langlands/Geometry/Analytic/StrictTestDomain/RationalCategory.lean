import Langlands.Geometry.Analytic.StrictTestDomain.RationalRepresentationProof

/-! # Rational loci and their actual bounded restriction maps -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalData

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- An inclusion of the actual rational loci, directed as a map of spaces. -/
structure Inclusion (d e : RationalData K P) : Type u where
  subset : d.locus ⊆ e.locus

instance {d e : RationalData K P} : Subsingleton (Inclusion d e) :=
  ⟨fun f g => by cases f; cases g; rfl⟩

/-- Rational input presentations over a fixed base form the thin category of
inclusions of their actual loci. Equal loci need not be equal input data. -/
instance : Category (RationalData K P) where
  Hom d e := Inclusion d e
  id _ := ⟨fun _ hx => hx⟩
  comp f g := ⟨fun _ hx => g.subset (f.subset hx)⟩
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

/-- The constructed structural map has image in its rational locus. -/
theorem baseMap_hasImageIn (d : RationalData K P) :
    HasImageIn K d.baseMap d.locus := by
  intro x
  rw [← (rationalRepresentation K P d).2.1]
  exact ⟨x, rfl⟩

namespace Inclusion

variable {d e f : RationalData K P}

/-- Representability constructs a unique bounded restriction, with the
contravariant algebra direction and its required equation over the base. -/
theorem existsUnique_restriction (h : Inclusion d e) :
    ∃! φ : BoundedAlgHom K e.algebra d.algebra, φ.comp e.baseMap = d.baseMap :=
  (rationalRepresentation K P e).2.2 d.algebra d.baseMap
    (fun x => h.subset (d.baseMap_hasImageIn x))

/-- The actual bounded algebra map induced by a rational-locus inclusion. -/
def restriction (h : Inclusion d e) : BoundedAlgHom K e.algebra d.algebra :=
  h.existsUnique_restriction.choose

@[simp]
theorem restriction_comp_baseMap (h : Inclusion d e) :
    h.restriction.comp e.baseMap = d.baseMap :=
  h.existsUnique_restriction.choose_spec.1

/-- Commutation with the base maps determines the restriction. -/
theorem restriction_unique (h : Inclusion d e)
    {φ : BoundedAlgHom K e.algebra d.algebra}
    (hφ : φ.comp e.baseMap = d.baseMap) : φ = h.restriction :=
  h.existsUnique_restriction.choose_spec.2 φ hφ

@[simp]
theorem restriction_id (d : RationalData K P) :
    (𝟙 d : d ⟶ d).restriction = BoundedAlgHom.id K d.algebra :=
  ((𝟙 d : d ⟶ d).restriction_unique rfl).symm

@[simp]
theorem restriction_comp (h : d ⟶ e) (k : e ⟶ f) :
    (h ≫ k).restriction = h.restriction.comp k.restriction := by
  apply ((h ≫ k).restriction_unique ?_).symm
  calc
    (h.restriction.comp k.restriction).comp f.baseMap =
        h.restriction.comp (k.restriction.comp f.baseMap) := rfl
    _ = h.restriction.comp e.baseMap := by rw [k.restriction_comp_baseMap]
    _ = d.baseMap := h.restriction_comp_baseMap

/-- The induced spectrum map commutes with the actual maps to the base. -/
theorem spectrumMap_restriction (h : Inclusion d e) (x : BanachSpectrum d.algebra) :
    e.spectrumMap (BanachSpectrum.comap h.restriction.toBoundedRingHom x) =
      d.spectrumMap x := by
  apply BanachSpectrum.ext
  intro a
  exact congrArg (fun φ : BoundedAlgHom K P d.algebra => x (φ a))
    h.restriction_comp_baseMap

end Inclusion

/-- A bounded map between the two constructed quotients over the base entails
inclusion of their loci. Thus the inclusion category detects these actual maps. -/
theorem subset_of_restriction {d e : RationalData K P}
    (φ : BoundedAlgHom K e.algebra d.algebra)
    (hφ : φ.comp e.baseMap = d.baseMap) : d.locus ⊆ e.locus := by
  intro x hx
  rw [← (rationalRepresentation K P d).2.1] at hx
  obtain ⟨y, rfl⟩ := hx
  have he := e.baseMap_hasImageIn (BanachSpectrum.comap φ.toBoundedRingHom y)
  have heq : BanachSpectrum.comap e.baseMap.toBoundedRingHom
      (BanachSpectrum.comap φ.toBoundedRingHom y) =
      BanachSpectrum.comap d.baseMap.toBoundedRingHom y := by
    apply BanachSpectrum.ext
    intro a
    exact congrArg (fun ψ : BoundedAlgHom K P d.algebra => y (ψ a)) hφ
  rwa [heq] at he

/-- Inclusions correspond exactly to bounded algebra maps over the base. -/
def inclusionEquivRestriction (d e : RationalData K P) :
    (d ⟶ e) ≃ {φ : BoundedAlgHom K e.algebra d.algebra //
      φ.comp e.baseMap = d.baseMap} where
  toFun h := ⟨h.restriction, h.restriction_comp_baseMap⟩
  invFun φ := ⟨subset_of_restriction φ.val φ.property⟩
  left_inv _ := (inferInstance : Subsingleton (Inclusion d e)).elim _ _
  right_inv φ := Subtype.ext
    ((Inclusion.restriction_unique ⟨subset_of_restriction φ.val φ.property⟩ φ.property).symm)

/-- Realize each rational input by its constructed affinoid spectrum and each
inclusion by the actual contravariant bounded restriction map. -/
def toAffinoidSpace (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K) :
    RationalData K P ⥤ PresentedStrictAffinoidSpace K where
  obj d := Opposite.op d.algebra
  map h := Quiver.Hom.op h.restriction
  map_id d := by
    change Quiver.Hom.op _ = Quiver.Hom.op _
    rw [Inclusion.restriction_id]
    rfl
  map_comp h k := by
    change Quiver.Hom.op _ = Quiver.Hom.op _
    rw [Inclusion.restriction_comp]
    rfl

/-- The underlying topological spaces are genuine multiplicative spectra. -/
def toTopologicalSpace (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (P : PresentedStrictAffinoidAlgebra K) : RationalData K P ⥤ TopCat :=
  toAffinoidSpace K P ⋙ strictAffinoidSpectrumFunctor K

end Langlands.Analytic.StrictTestDomain.RationalData
