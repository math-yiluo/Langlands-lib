import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.FunctionDescent
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Geometric reducedness of a schematically dominant image over a field -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.SchemeImageGeometry

/-- Pullback along an epimorphism, as an embedding of global functions. -/
def globalSectionsEmbedding {X Y : Scheme.{u}} (m : X ⟶ Y) [Epi m] :
    Γ(Y, ⊤) ↪ Γ(X, ⊤) where
  toFun := m.appTop
  inj' := Langlands.Scheme.UnitCocycleDescent.appTop_injective_of_epi m

/-- An epimorphism with affine target is scheme-theoretically dominant. -/
theorem schematicallyDominant_of_epi {X Y : Scheme.{u}} (m : X ⟶ Y)
    [Epi m] [IsAffine Y] : IsSchemeTheoreticallyDominant m := by
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine,
    (RingHom.injective_iff_ker_eq_bot m.appTop.hom).mp
      (globalSectionsEmbedding m).injective]
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp

/-- Geometric reducedness descends along a quasi-compact schematically dominant map
between schemes over a field. -/
theorem geometricallyReduced_of_schematicallyDominant
    {k : Type u} [Field k] {X Y : Scheme.{u}} (m : X ⟶ Y)
    (f : Y ⟶ Spec (CommRingCat.of k)) [QuasiCompact m]
    [IsSchemeTheoreticallyDominant m] [GeometricallyReduced (m ≫ f)] :
    GeometricallyReduced f := by
  rw [GeometricallyReduced.eq_geometrically,
    geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ b
  have : IsReduced (pullback m (pullback.fst f b)) :=
    GeometricallyReduced.geometrically_isReduced (f := m ≫ f) b
      (pullback.fst m (pullback.fst f b))
      (pullback.snd m (pullback.fst f b) ≫ pullback.snd f b)
      ((IsPullback.of_hasPullback m (pullback.fst f b)).paste_vert
        (IsPullback.of_hasPullback f b))
  exact IsSchemeTheoreticallyDominant.isReduced (pullback.snd m (pullback.fst f b))

/-- For a morphism between affine schemes over a field, epimorphy suffices to
descend geometric reducedness. -/
theorem geometricallyReduced_of_epi
    {k : Type u} [Field k] {X Y : Scheme.{u}} (m : X ⟶ Y)
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsAffine X] [IsAffine Y]
    [Epi m] [GeometricallyReduced (m ≫ f)] : GeometricallyReduced f := by
  let : IsSchemeTheoreticallyDominant m := schematicallyDominant_of_epi m
  exact geometricallyReduced_of_schematicallyDominant m f

end Langlands.SchemeImageGeometry
