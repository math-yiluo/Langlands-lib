/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

import WeilConjectures.AlgebraicGeometry.GenericFlatFinitePresentation
import WeilConjectures.AlgebraicGeometry.RadicialGenericReducedPreparation

/-! # A generically geometrically reduced model after a radicial base change

Source: Stacks Project, Tag 0559, second proof, reductions and inseparable extension.
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

private theorem fiber_restrict_property_iff
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {Y S : Scheme.{u}} (g : Y ⟶ S) (W : S.Opens) (s : W.toScheme) :
    P ((g ∣_ W).fiberToSpecResidueField s) ↔
      P (g.fiberToSpecResidueField (W.ι s)) := by
  let h := isPullback_fiberToSpecResidueField_of_isPullback
    (isPullback_morphismRestrict g W).flip s
  have := h.isIso_fst_of_isIso
  rw [← P.cancel_right_of_respectsIso _ (Spec.map (W.ι.residueFieldMap s)),
    ← h.w, P.cancel_left_of_respectsIso]

/-- Replace an affine family by a reduced flat finitely presented affine family
with geometrically reduced generic fibre, without changing geometric fibre spaces.

Source: Stacks Project, Tag 0559, second proof, through the paragraph preceding
its separating transcendence basis construction; Tags 051T and 052A.
Proof: nonemptiness of the generic fibre puts the generic point in V. Factor
through V and reduce both affine schemes. The base reduction is integral and
both reduction maps are universal homeomorphisms. Generic flat finite
presentation, followed by a basic-open shrinking, makes the reduced family flat
and finitely presented over an integral affine base. Flatness embeds its reduced
coordinate ring in its generic fibre ring, which is a domain. Let L be its
fraction field and K the base fraction field. Choose a finite purely inseparable
extension K'/K such that the reduction of L tensor K' is separably generated.
Scale each generator b with b^q=a/d to db: its q-th power is a*d^(q-1) in the
base ring. Adjoining these scaled generators gives a finite radicial integral
base algebra with fraction field K'. Its spectrum is a universal homeomorphism.
Base change the source and reduce it. Its generic fibre is now geometrically
reduced: its function field is separably generated, and its coordinate ring
embeds in that field after all field extensions. Apply generic flat finite
presentation again. Choose a basic open of the original affine base contained
in the image of this shrinking; pull everything back to it. The new base S
and source Y are affine, S is integral, and Y is reduced. The unique point above
the original generic point is generic. Reduction and radicial base change
preserve all geometric fibre spaces, giving the displayed equivalence at every
point of S. This construction also works in characteristic zero (take K'=K),
and in relative dimension zero. The generic fibre hypothesis excludes an empty
source.

(blueprint: lem-sbc-generic-radicial-geometrically-reduced-model) -/
theorem exists_generic_radicial_geometrically_reduced_model
    {X T : Scheme.{u}} [IsAffine X] (f : X ⟶ T) [LocallyOfFiniteType f]
    (V : T.Opens) (hV : IsAffineOpen V) (himage : Set.range f ⊆ V)
    (η : T) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η)) :
    ∃ (U : T.Opens), η ∈ U ∧
      ∃ (S Y : Scheme.{u}) (q : S ⟶ U.toScheme) (g : Y ⟶ S),
        IsAffine S ∧ IsIntegral S ∧ IsAffine Y ∧ IsReduced Y ∧
        IsUniversalHomeomorphism q ∧ Flat g ∧ LocallyOfFinitePresentation g ∧
        ∃ η' : S, IsGenericPoint η' Set.univ ∧ (q ≫ U.ι) η' = η ∧
          GeometricallyReduced (g.fiberToSpecResidueField η') ∧
          ∀ s : S, GeometricallyIrreducible (g.fiberToSpecResidueField s) ↔
            GeometricallyIrreducible (f.fiberToSpecResidueField ((q ≫ U.ι) s)) := by
  obtain ⟨U₀, hηU₀, hU₀, S₀, Y₀, q₀, g₀, hS₀a, hS₀i, hY₀a, hY₀r,
    hq₀, hg₀, η₀, hη₀, hqη₀, hred₀, hcompare₀⟩ :=
    exists_radicial_generic_reduced_preparation f V hV himage η hη hgeom
  have : IsAffine U₀.toScheme := hU₀
  have := hS₀a
  have := hS₀i
  have := hY₀a
  have := hY₀r
  have := hq₀
  have := hg₀
  obtain ⟨W, hW, hflat, hfp⟩ := exists_nonempty_open_flat_finitePresentation_restrict g₀
  have hη₀W : η₀ ∈ W := by
    apply (hη₀.mem_open_set_iff W.isOpen).mpr
    simpa only [Set.univ_inter] using hW
  let O : U₀.toScheme.Opens := ⟨q₀ '' (W : Set S₀), q₀.isHomeomorph.isOpenMap _ W.isOpen⟩
  obtain ⟨b, hbO, hηb⟩ := (isAffineOpen_top U₀.toScheme).exists_basicOpen_le
    (⟨q₀ η₀, ⟨η₀, hη₀W, rfl⟩⟩ : O) (by trivial)
  let B : U₀.toScheme.Opens := U₀.toScheme.basicOpen b
  let A : S₀.Opens := q₀ ⁻¹ᵁ B
  have hAW : A ≤ W := by
    intro s hs
    obtain ⟨t, ht, hts⟩ := hbO hs
    exact q₀.injective hts ▸ ht
  have hη₀A : η₀ ∈ A := hηb
  let U : T.Opens := U₀.ι ''ᵁ B
  let q : A.toScheme ⟶ U.toScheme := (q₀ ∣_ B) ≫ (U₀.ι.isoImage B).hom
  let g : (g₀ ⁻¹ᵁ A).toScheme ⟶ A.toScheme := g₀ ∣_ A
  let η' : A.toScheme := ⟨η₀, hη₀A⟩
  have hq : IsUniversalHomeomorphism q := by
    have : IsUniversalHomeomorphism (q₀ ∣_ B) :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict q₀ B).flip hq₀
    infer_instance
  have hA : IsAffineOpen A := (isAffineOpen_top U₀.toScheme).basicOpen b |>.preimage q₀
  have : IsAffine A.toScheme := hA
  have : Nonempty A.toScheme := ⟨η'⟩
  have hAi : IsIntegral A.toScheme := isIntegral_of_isOpenImmersion A.ι
  have hYa : IsAffineOpen (g₀ ⁻¹ᵁ A) := hA.preimage g₀
  have hflat' : Flat g := by
    have h := IsZariskiLocalAtTarget.restrict hflat (W.ι ⁻¹ᵁ A)
    have h' := (MorphismProperty.arrow_mk_iso_iff @Flat
      (morphismRestrictRestrict g₀ W (W.ι ⁻¹ᵁ A))).mp h
    have e : W.ι ''ᵁ W.ι ⁻¹ᵁ A = A := by
      ext s
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ht
      · intro hs
        exact ⟨⟨s, hAW hs⟩, hs, rfl⟩
    rwa [e] at h'
  have hfp' : LocallyOfFinitePresentation g := by
    have h := IsZariskiLocalAtTarget.restrict hfp (W.ι ⁻¹ᵁ A)
    have h' := (MorphismProperty.arrow_mk_iso_iff @LocallyOfFinitePresentation
      (morphismRestrictRestrict g₀ W (W.ι ⁻¹ᵁ A))).mp h
    have e : W.ι ''ᵁ W.ι ⁻¹ᵁ A = A := by
      ext s
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ht
      · intro hs
        exact ⟨⟨s, hAW hs⟩, hs, rfl⟩
    rwa [e] at h'
  have hη' : IsGenericPoint η' Set.univ := by
    rw [isGenericPoint_iff_specializes]
    intro s
    simp only [Set.mem_univ, iff_true]
    exact A.ι.isOpenEmbedding.isInducing.specializes_iff.mp (hη₀.specializes (by trivial))
  have hqι : q ≫ U.ι = A.ι ≫ q₀ ≫ U₀.ι := by
    simp [q, U, A, Category.assoc, Scheme.Hom.isoImage_hom_ι, morphismRestrict_ι_assoc]
  refine ⟨U, ?_, A.toScheme, (g₀ ⁻¹ᵁ A).toScheme, q, g,
    hA, hAi, hYa, inferInstance, hq, hflat', hfp', η', hη', ?_, ?_, ?_⟩
  · have hmem : (q₀ ≫ U₀.ι) η₀ ∈ U := ⟨q₀ η₀, hηb, rfl⟩
    rwa [hqη₀] at hmem
  · rw [hqι, Scheme.Hom.comp_apply]
    exact hqη₀
  · exact (fiber_restrict_property_iff @GeometricallyReduced g₀ A η').mpr hred₀
  · intro s
    rw [fiber_restrict_property_iff @GeometricallyIrreducible g₀ A s, hcompare₀]
    rw [hqι, Scheme.Hom.comp_apply]
    rfl

end AlgebraicGeometry
