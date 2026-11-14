import Langlands.Geometry.Building.StandardLeviStrictQuotientFaces

/-! # The partition of the nonnegative quotient by actual standard-Levi pieces -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterUniformizer

/-- The actual strict standard-Levi pieces lie in the nonnegative quotient
and give exactly one piece for every point of it. -/
def StandardLeviStrictQuotientPartitionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    ∀ (ν : cocharacterLattice T), IsGenericCocharacter i ν →
      ∀ (A₀ : CommGroupScheme (Spec (CommRingCat.of F))) (a₀ : A₀.toGrp ⟶ G),
        IsSplitComponent a₀ → ∀ (f₀ : A₀ ⟶ T),
          CommGroupScheme.groupHom f₀ ≫ i = a₀ →
          (∀ J : Set (characterLattice T),
            standardLeviStrictQuotientFace F i ν A₀ f₀ J ⊆
              CAplusQuotient F T (simpleRelativeRoots i ν) A₀ f₀) ∧
          (∀ x : CAplusQuotient F T (simpleRelativeRoots i ν) A₀ f₀,
            ∃! J : Set (characterLattice T),
              x.val ∈ standardLeviStrictQuotientFace F i ν A₀ f₀ J)

end Langlands.GroupScheme.CocharacterUniformizer
