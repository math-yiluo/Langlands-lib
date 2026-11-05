import Langlands.AlgebraicGeometry.SchemeComponentGeometry
import Langlands.AlgebraicGeometry.FiniteSeparableComponentSplittingStatement
import Langlands.AlgebraicGeometry.FiniteSeparableGenericCoverStatement
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Actual generic-fibre comparison for finite étale component splitting -/

noncomputable section

universe u

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

variable {P Q X S T Z : Scheme.{u}}
  {a : P ⟶ X} {b : P ⟶ S} {c : Q ⟶ X} {d : Q ⟶ T}
  {f : X ⟶ Z} {g : S ⟶ Z} {k : T ⟶ Z}

/-- The actual map between two cartesian base changes when the base maps
are identified by a specified isomorphism over their common target. -/
def cartesianComparisonMapOfBaseIso (hP : IsPullback a b f g)
    (hQ : IsPullback c d f k) (e : S ≅ T) (he : e.hom ≫ k = g) : P ⟶ Q :=
  hQ.lift a (b ≫ e.hom) (by rw [Category.assoc, he]; exact hP.w)

/-- This comparison is itself the cartesian base change of the base isomorphism. -/
theorem isPullback_cartesianComparisonMapOfBaseIso (hP : IsPullback a b f g)
    (hQ : IsPullback c d f k) (e : S ≅ T) (he : e.hom ≫ k = g) :
    IsPullback (cartesianComparisonMapOfBaseIso hP hQ e he) b d e.hom := by
  have hP' : IsPullback a b f (e.hom ≫ k) := by rw [he]; exact hP
  exact hP'.of_right' hQ

/-- The comparison identifies the actual component geometry over the two bases. -/
theorem componentsGeometricallyIrreducible_iff_of_cartesian_baseIso
    (hP : IsPullback a b f g) (hQ : IsPullback c d f k)
    (e : S ≅ T) (he : e.hom ≫ k = g) :
    ComponentsGeometricallyIrreducible b ↔ ComponentsGeometricallyIrreducible d :=
  componentsGeometricallyIrreducible_iff_of_isPullback_of_isIso
    (isPullback_cartesianComparisonMapOfBaseIso hP hQ e he)

/-- A prescribed residue-field spectrum isomorphism compares a scalar extension
of an original fibre with the actual fibre in any cartesian cover diagram. -/
theorem fiberComponentsGeometricallyIrreducible_iff_of_generic_specIso
    {Y Y' : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (h : IsPullback a b f g)
    (η : Y) (η' : Y') (L : Type u) [Field L]
    (α : Spec (.of L) ⟶ Spec (Y.residueField η))
    (e : Spec (.of L) ≅ Spec (Y'.residueField η'))
    (he : e.hom ≫ Y'.fromSpecResidueField η' ≫ g =
      α ≫ Y.fromSpecResidueField η) :
    FiberComponentsGeometricallyIrreducible b η' ↔
      ComponentsGeometricallyIrreducible (pullback.snd (f.fiberToSpecResidueField η) α) := by
  have hL := (IsPullback.of_hasPullback (f.fiberToSpecResidueField η) α).paste_horiz
    (IsPullback.of_hasPullback f (Y.fromSpecResidueField η))
  have hP := (IsPullback.of_hasPullback b (Y'.fromSpecResidueField η')).paste_horiz h
  exact (componentsGeometricallyIrreducible_iff_of_cartesian_baseIso hL hP e he).symm

/-- Given the two substantial existence inputs, the final diagram and its
actual generic-fibre component condition follow with no hypothesis on the base
beyond irreducibility. This lemma does not supply either input. -/
theorem finiteTypeFiniteEtaleGenericComponentSplitting_of_fieldSplitting_and_cover
    (hsplit : FiniteSeparableComponentSplitting.{u})
    (hcover : FiniteSeparableGenericCover.{u}) :
    FiniteTypeFiniteEtaleGenericComponentSplitting.{u} := by
  intro X Y _ f _ _
  let η : Y := genericPoint Y
  have hη : IsGenericPoint η univ := genericPoint_spec Y
  let : LocallyOfFiniteType (f.fiberToSpecResidueField η) := by
    change LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField η))
    infer_instance
  let : IsNoetherian (f.fiber η) :=
    { toIsLocallyNoetherian :=
        LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField η)
      toCompactSpace := inferInstance }
  let := (NoetherianSpace.finite_irreducibleComponents (α := f.fiber η)).to_subtype
  obtain ⟨L, hL, hKL, hfinite, hsep, hgeom⟩ :=
    hsplit (Y.residueField η) (f.fiberToSpecResidueField η)
  let := hL
  let := hKL
  let := hfinite
  let := hsep
  obtain ⟨V, hV, Y', g, haff, hirr, hsurj, hfin, hetale, η', hη', e, he⟩ :=
    hcover η hη L
  let := hsurj
  let := hfin
  let := hetale
  refine ⟨V, hV, Y', g, haff, hirr, hsurj, hfin, hetale,
    inferInstance, inferInstance, inferInstance, η', hη', ?_⟩
  have hcart := (IsPullback.of_hasPullback (f ∣_ V) g).paste_horiz
    (isPullback_morphismRestrict f V).flip
  exact (fiberComponentsGeometricallyIrreducible_iff_of_generic_specIso hcart η η' L
    (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField η) L))) e he).mpr hgeom

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
