import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeTargetConnectedFibres

/-! # Actual families over affine target charts -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace AffineTargetFamily

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : (schemeYoneda S).obj V ⟶ Y.presheaf)

/-- Pull back to the target chart and view the result as an actual space over it. -/
def space : AlgebraicSpace V.left :=
  SchemeTargetRebase.space
    (FibreProduct.snd f (homMk b : (schemeToSpace S).obj V ⟶ Y))

/-- The actual target-chart family retains relative quasi-separatedness. -/
theorem isQuasiSeparated [IsAffine S] [IsAffine V.left]
    (hX : IsQuasiSeparated X) : IsQuasiSeparated (space f b) := by
  have : QuasiSeparated V.hom := inferInstance
  exact SchemeTargetRebase.isQuasiSeparated _
    (FibreProduct.isQuasiSeparated _ _ hX (isQuasiSeparated_schemeToSpace V))

/-- The family has a quasi-compact locally finitely presented atlas over the chart. -/
theorem hasAtlasProperty_finitePresentation [IsAffine S] [IsAffine V.left]
    [LocallyOfFinitePresentation V.hom]
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (hYqs : IsQuasiSeparated Y) :
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) (space f b) :=
  SchemeTargetRebase.hasAtlasProperty_finitePresentation _
    (FibreProduct.hasAtlasProperty_finitePresentation _ _ hX
      (HasAtlasProperty.of_scheme V ⟨inferInstance, inferInstance⟩) hY hYqs)

/-- An actual surjective etale target chart tests connectedness on its family. -/
theorem hasGeometricallyConnectedFibres_iff (hb : IsEtale b) (hs : IsSurjective b) :
    HasGeometricallyConnectedFibres f ↔
      HasGeometricallyConnectedFibres (structuralMorphism (space f b)) :=
  (hasGeometricallyConnectedFibres_iff_targetAtlas f b hb hs).trans
    (SchemeTargetRebase.hasGeometricallyConnectedFibres_iff _)

/-- On an affine target chart, the test is exactly geometric component count one. -/
theorem hasGeometricallyConnectedFibres_iff_componentCount [IsAffine S]
    (B : Type u) [CommRing B] (g : Spec (CommRingCat.of B) ⟶ S)
    [LocallyOfFinitePresentation g]
    (b : (schemeYoneda S).obj (Over.mk g) ⟶ Y.presheaf)
    (hb : IsEtale b) (hs : IsSurjective b)
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (hYqs : IsQuasiSeparated Y) :
    HasGeometricallyConnectedFibres f ↔
      ∀ p, geometricFibreComponentCount B (space f b) p = 1 := by
  have : IsAffine (Over.mk g).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of B)))
  have : LocallyOfFinitePresentation (Over.mk g).hom := inferInstanceAs
    (LocallyOfFinitePresentation g)
  exact (hasGeometricallyConnectedFibres_iff f b hb hs).trans
    (hasGeometricallyConnectedFibres_structural_iff_componentCount B (space f b)
      (hasAtlasProperty_finitePresentation f b hX hY hYqs))

end AffineTargetFamily

/-- A finite-presentation atlas can be chosen on an actual spectrum. -/
theorem exists_spec_finitePresentation_atlas {S : Scheme.{u}} [IsAffine S]
    (Y : AlgebraicSpace S)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y) :
    ∃ (B : Type u) (_ : CommRing B) (g : Spec (CommRingCat.of B) ⟶ S)
      (b : (schemeYoneda S).obj (Over.mk g) ⟶ Y.presheaf),
      IsEtale b ∧ IsSurjective b ∧ LocallyOfFinitePresentation g := by
  obtain ⟨V, b, hVa, hb, hs, hVl⟩ := exists_affine_finitePresentation_atlas Y hY
  let := hVa
  let := hVl
  let g : Spec Γ(V.left, ⊤) ⟶ S := V.left.isoSpec.inv ≫ V.hom
  let e : Over.mk g ≅ V := Over.isoMk V.left.isoSpec.symm rfl
  refine ⟨Γ(V.left, ⊤), inferInstance, g,
    (schemeYoneda S).map e.hom ≫ b, ?_, ?_, ?_⟩
  · exact hb.iso_comp ((schemeYoneda S).mapIso e)
  · exact (MorphismProperty.cancel_left_of_respectsIso
      ((MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).relative
        (schemeYoneda S)) ((schemeYoneda S).map e.hom) b).mpr hs
  · change LocallyOfFinitePresentation (V.left.isoSpec.inv ≫ V.hom)
    infer_instance

end Langlands.AlgebraicGeometry.AlgebraicSpace
