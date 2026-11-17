import Langlands.AlgebraicGeometry.Picard.LocalRepresenterSheafComparison
import Langlands.AlgebraicGeometry.Picard.LocalRepresenterEquivariantBundle
import Langlands.AlgebraicGeometry.Picard.PolarizedEtaleRelationEffectivityStatement
import Langlands.AlgebraicGeometry.Picard.PolarizedRepresenterGeometricReflection
import Langlands.AlgebraicGeometry.Picard.PolarizedSmoothProperDescentStatement

/-! # Reduction of polarized representability descent to scheme effectivity -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

namespace LocalRepresenter

/-- Construct a global representation from geometric polarized effectivity
and the given local polarized smooth proper representation. -/
def descendedRepresenter (H : PolarizedEtaleRelationEffectivityStatement.{u})
    {S U : Scheme.{u}} [IsAffine S] [IsAffine U]
    (p : U ⟶ S) [Etale p] [Surjective p]
    {F : (Over S)ᵒᵖ ⥤ Type v}
    (hF : Presieve.IsSheaf (Scheme.etaleTopology.over S) F)
    (L : PresheafLineBundle F) {M : Over U}
    (e : ((Over.map p).op ⋙ F).RepresentableBy M)
    (hM : Smooth M.hom) (hP : IsProper M.hom)
    (hL : ((L.baseChange p).universal e).IsAmple) :
    Σ N : Over S, F.RepresentableBy N := by
  have hex := H S U inferInstance inferInstance p inferInstance inferInstance
    (etaleRelation p e) M.hom hM hP (cartesian p e) (equivariantBundle p e L) hL
  let N := Classical.choose hex
  let q := Classical.choose (Classical.choose_spec hex)
  have hq : IsPullback q M.hom N.hom p :=
    (Classical.choose_spec (Classical.choose_spec hex)).1
  have hi : first p ≫ q = second p e ≫ q :=
    (Classical.choose_spec (Classical.choose_spec hex)).2
  exact ⟨N, representableByDescent p e hF N q hq hi⟩

end LocalRepresenter

/-- Geometric polarized scheme effectivity supplies the full smooth proper
representability descent theorem, with independent scheme and value universes. -/
theorem polarizedSmoothProperEtaleDescent_of_effectivity :
    PolarizedEtaleRelationEffectivityStatement.{u} →
      PolarizedSmoothProperEtaleDescentStatement.{u, v} := by
  intro H S U hS hU p hp hs F hF L M e hM hP hL
  let : IsAffine S := hS
  let : IsAffine U := hU
  let : Etale p := hp
  let : Surjective p := hs
  let d := LocalRepresenter.descendedRepresenter H p hF L e hM hP hL
  exact ⟨d.1, d.2, geometricReflection_of_representable p L d.2 e hM hP hL⟩

end Langlands.AlgebraicGeometry.Picard
