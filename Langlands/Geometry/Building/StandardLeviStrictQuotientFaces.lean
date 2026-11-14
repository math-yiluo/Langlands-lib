import Langlands.Geometry.Building.CocharacterUniformizerCone
import Langlands.Geometry.Building.StandardLeviStrictUniformizerStatement

/-! # Actual standard-Levi strict pieces in the common-uniformizer quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterUniformizer

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (A₀ : CommGroupScheme (Spec (CommRingCat.of F))) (f₀ : A₀ ⟶ T)

/-- The strict quotient piece indexed by `J`, using all actual closed
standard-Levi representatives and their compatible split components. -/
def standardLeviStrictQuotientFace (J : Set (characterLattice T)) :
    Set (rationalPoints T.toGrp ⧸
      (CA F A₀).map (rationalPoints.map (CommGroupScheme.groupHom f₀))) :=
  {x | J ⊆ simpleRelativeRoots i ν ∧
    ∃ (L : GroupScheme (Spec (CommRingCat.of F))) (j : L ⟶ G),
      IsClosedSubgroup j ∧ (standardLevi i ν J).IsRepresentedBy j ∧
      ∃ (B : CommGroupScheme (Spec (CommRingCat.of F))) (b : B.toGrp ⟶ L),
        IsSplitComponent b ∧ ∃ (g : B ⟶ T),
          CommGroupScheme.groupHom g ≫ i = b ≫ j ∧
          x ∈ (QuotientGroup.mk'
            ((CA F A₀).map (rationalPoints.map (CommGroupScheme.groupHom f₀)))) ''
              ((rationalPoints.map (CommGroupScheme.groupHom g)) ''
                CAstrict F B (restrictedSimpleCharacters i ν J g))}

/-- A strict point of any compatible actual representative gives a point of
the indexed quotient piece. -/
theorem mem_standardLeviStrictQuotientFace_of_representative
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν)
    (L : GroupScheme (Spec (CommRingCat.of F))) (j : L ⟶ G)
    (hjc : IsClosedSubgroup j) (hj : (standardLevi i ν J).IsRepresentedBy j)
    (B : CommGroupScheme (Spec (CommRingCat.of F))) (b : B.toGrp ⟶ L)
    (hb : IsSplitComponent b) (g : B ⟶ T)
    (hg : CommGroupScheme.groupHom g ≫ i = b ≫ j)
    (y : rationalPoints B.toGrp)
    (hy : y ∈ CAstrict F B (restrictedSimpleCharacters i ν J g)) :
    QuotientGroup.mk'
        ((CA F A₀).map (rationalPoints.map (CommGroupScheme.groupHom f₀)))
        (rationalPoints.map (CommGroupScheme.groupHom g) y) ∈
      standardLeviStrictQuotientFace F i ν A₀ f₀ J :=
  ⟨hJ, L, j, hjc, hj, B, b, hb, g, hg,
    _, ⟨y, hy, rfl⟩, rfl⟩

/-- An index outside the actual simple roots gives an empty piece. -/
theorem standardLeviStrictQuotientFace_eq_empty_of_not_subset
    (J : Set (characterLattice T)) (hJ : ¬ J ⊆ simpleRelativeRoots i ν) :
    standardLeviStrictQuotientFace F i ν A₀ f₀ J = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hJ hx.1

end Langlands.GroupScheme.CocharacterUniformizer
