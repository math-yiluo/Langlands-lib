import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.CategoryTheory.Filtered.Basic

/-! # Models of finitely presented étale scheme equivalence relations -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-- An étale equivalence relation with affine object scheme, locally finitely presented
structure map and quasi-compact relation over a cofiltered affine limit descends to an
actual stage, including the complete relation and the cartesian comparison. -/
def LimitModelExistence : Prop :=
  ∀ (I : Type u) [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (_hc : IsLimit c)
    (E : EtaleEquivalenceRelation.{u}) [IsAffine E.U]
    (b : E.U ⟶ c.pt) (_hb : E.t ≫ b = E.s ≫ b)
    [LocallyOfFinitePresentation b] [QuasiCompact (E.t ≫ b)],
    ∃ (i : I) (Ei : EtaleEquivalenceRelation.{u})
      (bi : Ei.U ⟶ D.obj i) (fU : E.U ⟶ Ei.U) (fR : E.R ⟶ Ei.R),
      IsAffine Ei.U ∧ LocallyOfFinitePresentation bi ∧
      QuasiCompact (Ei.t ≫ bi) ∧ Ei.t ≫ bi = Ei.s ≫ bi ∧
      IsPullback fU b bi (c.π.app i) ∧ E.IsCartesianHom Ei fU fR

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
