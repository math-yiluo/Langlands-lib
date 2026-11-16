import Langlands.AlgebraicGeometry.Picard.PresheafLineBundleAmpleCover
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.AlgebraicGeometry.Limits

/-! # Base change of representers and their actual universal line bundles -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

variable {S U : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}

/-- Restrict a supplied representation along a change of base. -/
def representableByBaseChange {N : Over S} (e : F.RepresentableBy N) (p : U ⟶ S) :
    ((Over.map p).op ⋙ F).RepresentableBy ((Over.pullback p).obj N) :=
  PresheafLineBundle.baseChangeRepresentation p e

namespace PresheafLineBundle

variable (L : PresheafLineBundle F) {N : Over S}

/-- The universal family after base change is the restriction of the original
universal family along the actual pullback projection. -/
theorem universalFamily_baseChange (e : F.RepresentableBy N) (p : U ⟶ S) :
    (representableByBaseChange e p).homEquiv (𝟙 _) =
      F.map ((Over.mapPullbackAdj p).counit.app N).op (e.homEquiv (𝟙 N)) := by
  change e.homEquiv _ = _
  rw [e.homEquiv_eq]
  congr 1

/-- The universal bundle of the base-changed representation is the actual
pullback of the original universal bundle. -/
def universalBaseChangePullbackIso (e : F.RepresentableBy N) (p : U ⟶ S) :
    (LineBundle.pullback (pullback.fst N.hom p)).obj (L.universal e) ≅
      (L.baseChange p).universal (representableByBaseChange e p) :=
  L.pullbackIso ((Over.mapPullbackAdj p).counit.app N) _ _
    (universalFamily_baseChange e p).symm

end PresheafLineBundle

end Langlands.AlgebraicGeometry.Picard
