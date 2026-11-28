import Langlands.Geometry.Building.CocharacterUniformizer
import Langlands.GroupScheme.Rational.ParabolicRootPresentation
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # The Levi uniformizer quotient and the ambient norm kernel -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterUniformizer

/-- Renard V.3.25 for the actual split components of a connected reductive
group and a Levi of a proper rational parabolic. The inclusion induces an
injection into the ambient quotient, and the strict uniformizer cone meets
the ambient common norm kernel. -/
def LeviUniformizerNormKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (P M : GroupScheme (Spec (CommRingCat.of F)))
    (A B : CommGroupScheme (Spec (CommRingCat.of F)))
    (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M) (b : B.toGrp ⟶ G),
    haveI := hG.isAffineHom
    IsParabolicSubgroup p → SubgroupFunctor.range p ≠ ⊤ → IsRationalLeviSubgroup l →
    IsSplitComponent a → ∀ hb : IsSplitComponent b,
    ∃ f : B ⟶ A, CommGroupScheme.groupHom f ≫ a ≫ l ≫ p = b ∧
      let i := rationalPoints.map (CommGroupScheme.groupHom f)
      let C := CA F A
      let D := (CA F B).map i
      let m := rationalPoints.map (a ≫ l ≫ p)
      let N := (rationalCommonNormKernel G).comap m
      let H := (rationalPoints.map b).range
      letI := H.normal_of_le_center hb.isCentralSplitTorus.range_le_center
      let Q := rationalCommonNormKernel G ⊔ H
      let K := D ⊔ (C ⊓ N)
      Function.Injective i ∧ ¬ Function.Surjective i ∧
        D ≤ C ∧ Disjoint D N ∧ C ⊓ Q.comap m = K ∧
        (∃ q : (C ⧸ K.subgroupOf C) →* (rationalPoints G ⧸ Q),
          Function.Injective q ∧ ∀ x : C,
            q (QuotientGroup.mk x) = QuotientGroup.mk (m x)) ∧
        Finite (C ⧸ K.subgroupOf C) ∧
        ∀ r : ParabolicRootPresentation p l a,
          ∃ x ∈ CAstrict F A (restrictedSimpleCharacters r.data.i r.data.ν r.data.J r.data.f),
            x ∈ N

end Langlands.GroupScheme.CocharacterUniformizer
