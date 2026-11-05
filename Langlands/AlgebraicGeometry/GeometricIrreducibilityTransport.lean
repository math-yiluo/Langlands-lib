import Langlands.AlgebraicGeometry.GeometricIrreducibilityAffine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

universe u v

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- A point inducing a whole-space generic point is itself generic. -/
theorem isGenericPoint_of_isInducing
    {T : Type u} {S : Type v} [TopologicalSpace T] [TopologicalSpace S]
    {g : T → S} (hg : Topology.IsInducing g) {η : T}
    (hη : IsGenericPoint (g η) univ) : IsGenericPoint η univ := by
  rw [isGenericPoint_iff_specializes]
  intro t
  exact ⟨fun _ => mem_univ _, fun _ => hg.specializes_iff.mp (hη.specializes (mem_univ _))⟩

/-- Geometric irreducibility is invariant under isomorphism of arrows. -/
theorem geometricallyIrreducible_arrowIso_iff
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) :
    GeometricallyIrreducible f ↔ GeometricallyIrreducible g := by
  rw [GeometricallyIrreducible.eq_geometrically]
  exact MorphismProperty.arrow_mk_iso_iff _ e

/-- A pullback carries geometric irreducibility of the fibre at the image
point to geometric irreducibility of its own actual fibre. -/
theorem geometricallyIrreducible_fiber_of_isPullback
    {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g) (y : Y)
    (hf : GeometricallyIrreducible (f.fiberToSpecResidueField (g y))) :
    GeometricallyIrreducible (b.fiberToSpecResidueField y) :=
  MorphismProperty.of_isPullback
    (isPullback_fiberToSpecResidueField_of_isPullback h y) hf

/-- An isomorphism of morphisms restricts to isomorphic morphisms over
corresponding open subsets of their targets. -/
noncomputable def arrowIso_morphismRestrict
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (a : X ≅ X') (b : Y ≅ Y') (h : a.hom ≫ g = f ≫ b.hom) (V : Y'.Opens) :
    Arrow.mk (f ∣_ b.hom ⁻¹ᵁ V) ≅ Arrow.mk (g ∣_ V) := by
  have hpre : f ⁻¹ᵁ b.hom ⁻¹ᵁ V = a.hom ⁻¹ᵁ g ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h]
  refine Arrow.isoMk (X.isoOfEq hpre ≪≫ a.hom.preimageIso (g ⁻¹ᵁ V))
    (b.hom.preimageIso V) ?_
  apply (cancel_mono V.ι).mp
  simp only [Arrow.mk_hom, Iso.trans_hom, Category.assoc, Scheme.Hom.preimageIso_hom_ι,
    morphismRestrict_ι, Scheme.Hom.preimageIso_hom_ι_assoc,
    Scheme.isoOfEq_hom_ι_assoc]
  rw [h, morphismRestrict_ι_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- An affine morphism missing a whole-space generic point has empty
preimage over an open neighbourhood of that point. -/
theorem exists_open_preimage_eq_bot_of_affine_not_mem_range
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (η : Y) (hη : IsGenericPoint η univ) (hmiss : η ∉ Set.range f) :
    ∃ V : Y.Opens, η ∈ V ∧ f ⁻¹ᵁ V = ⊥ := by
  let η' := Y.isoSpec.hom η
  have hη' : IsGenericPoint η' univ := by
    have himage := hη.image Y.isoSpec.hom.continuous
    have hrange : Set.range (fun y => Y.isoSpec.hom y) = univ :=
      Set.range_eq_univ.mpr Y.isoSpec.hom.homeomorph.surjective
    simpa only [Set.image_univ, hrange, closure_univ] using himage
  have hmiss' : η' ∉ Set.range (PrimeSpectrum.comap f.appTop.hom) := by
    rintro ⟨x, hx⟩
    have hpoint : f (X.isoSpec.inv x) = η := by
      apply Y.isoSpec.hom.homeomorph.injective
      change (X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom) x = _
      rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
      exact hx
    exact hmiss ⟨_, hpoint⟩
  obtain ⟨c, hc, he⟩ :=
    exists_basicOpen_preimage_eq_bot_of_not_mem_range f.appTop.hom η' hη' hmiss'
  let V : (Spec Γ(Y, ⊤)).Opens := PrimeSpectrum.basicOpen c
  refine ⟨Y.isoSpec.hom ⁻¹ᵁ V, hc, ?_⟩
  change Spec.map f.appTop ⁻¹ᵁ V = ⊥ at he
  rw [← Scheme.Hom.comp_preimage, ← Scheme.isoSpec_hom_naturality,
    Scheme.Hom.comp_preimage, he]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A nonempty open part of an actual geometrically irreducible fibre is
geometrically irreducible over the same residue field. -/
theorem geometricallyIrreducible_fiber_comp_openImmersion
    {U X Y : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (f : X ⟶ Y)
    (η : Y) (hgeneric : GeometricallyIrreducible (f.fiberToSpecResidueField η))
    (hne : η ∈ Set.range (i ≫ f)) :
    GeometricallyIrreducible ((i ≫ f).fiberToSpecResidueField η) := by
  let := hgeneric
  have hnonempty : Nonempty ((i ≫ f).fiber η) := by
    rw [((i ≫ f).fiberHomeo η).nonempty_congr, Set.nonempty_coe_sort]
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx⟩
  let e := pullbackRightPullbackFstIso f (Y.fromSpecResidueField η) i
  have : Nonempty ↥(pullback i (f.fiberι η)) :=
    e.hom.homeomorph.nonempty_congr.mpr hnonempty
  have hgeom : GeometricallyIrreducible
      (pullback.snd i (f.fiberι η) ≫ f.fiberToSpecResidueField η) := inferInstance
  apply (geometricallyIrreducible_arrowIso_iff
    (Arrow.isoMk e (Iso.refl _) ?_)).mp hgeom
  simp [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiberι, e]

/-- A quasi-compact source missing the generic point of an affine target has
empty preimage over some neighbourhood of that point. -/
theorem exists_open_preimage_eq_bot_of_compact_not_mem_range
    {X Y : Scheme.{u}} [CompactSpace X] [IsAffine Y] (f : X ⟶ Y)
    (η : Y) (hη : IsGenericPoint η univ) (hmiss : η ∉ Set.range f) :
    ∃ V : Y.Opens, η ∈ V ∧ f ⁻¹ᵁ V = ⊥ := by
  classical
  let 𝒰 := X.affineCover.finiteSubcover
  have hlocal : ∀ i : 𝒰.I₀, ∃ V : Y.Opens, η ∈ V ∧ (𝒰.f i ≫ f) ⁻¹ᵁ V = ⊥ := by
    intro i
    have : IsAffine (𝒰.X i) := by dsimp [𝒰]; infer_instance
    apply exists_open_preimage_eq_bot_of_affine_not_mem_range (𝒰.f i ≫ f) η hη
    rintro ⟨x, hx⟩
    exact hmiss ⟨𝒰.f i x, hx⟩
  choose V hV hpre using hlocal
  refine ⟨⨅ i, V i, ?_, ?_⟩
  · change η ∈ ((⨅ i, V i : Y.Opens) : Set Y)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hV
  · apply bot_unique
    intro x hx
    obtain ⟨i, z, hz⟩ := 𝒰.exists_eq x
    have hzi : z ∈ (𝒰.f i ≫ f) ⁻¹ᵁ V i := by
      change f (𝒰.f i z) ∈ V i
      rw [hz]
      exact (iInf_le V i) hx
    rw [hpre i] at hzi
    exact False.elim hzi

/-- Shrinking a target open preserves geometric irreducibility of the
restricted morphism. -/
theorem geometricallyIrreducible_restrict_of_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (hVU : V ≤ U)
    (hgeom : GeometricallyIrreducible (f ∣_ U)) :
    GeometricallyIrreducible (f ∣_ V) := by
  let := hgeom
  have heq : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVU]
  apply (geometricallyIrreducible_arrowIso_iff
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V) ≪≫ morphismRestrictEq f heq)).mp
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Isomorphic arrows have geometrically irreducible actual fibres at
corresponding points. -/
theorem geometricallyIrreducible_fiber_of_arrowIso
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (a : X ≅ X') (b : Y ≅ Y') (h : a.hom ≫ g = f ≫ b.hom)
    (η : Y) (hgeneric : GeometricallyIrreducible (f.fiberToSpecResidueField η)) :
    GeometricallyIrreducible (g.fiberToSpecResidueField (b.hom η)) := by
  have hsq : IsPullback a.inv g f b.inv := by
    apply IsPullback.of_horiz_isIso
    constructor
    apply (cancel_mono b.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← h, Iso.inv_hom_id_assoc]
  apply geometricallyIrreducible_fiber_of_isPullback hsq (b.hom η)
  have hb : b.inv (b.hom η) = η := by
    change (b.hom ≫ b.inv) η = η
    rw [Iso.hom_inv_id]
    rfl
  exact hb.symm ▸ hgeneric

/-- Two open subsets meeting a geometrically irreducible actual fibre meet
each other in that fibre. -/
theorem exists_overlap_point_of_geometricallyIrreducible_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) (η : Y)
    (hgeneric : GeometricallyIrreducible (f.fiberToSpecResidueField η))
    (U V : X.Opens) (hU : ∃ x : X, f x = η ∧ x ∈ U)
    (hV : ∃ x : X, f x = η ∧ x ∈ V) :
    ∃ x : X, f x = η ∧ x ∈ U ∧ x ∈ V := by
  let := hgeneric
  have : IrreducibleSpace (f.fiber η) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      (f.fiberToSpecResidueField η)
  have hirr : IsIrreducible (f ⁻¹' {η}) := by
    rw [← f.range_fiberι η, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image (f.fiberι η)
      (f.fiberι η).continuous.continuousOn
  obtain ⟨x, hxη, hxU, hxV⟩ :=
    hirr.isPreirreducible U V U.isOpen V.isOpen hU hV
  exact ⟨x, hxη, hxU, hxV⟩

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
