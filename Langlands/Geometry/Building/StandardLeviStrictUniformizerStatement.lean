import Langlands.Geometry.Building.CocharacterUniformizer
import Langlands.GroupScheme.Rational.RestrictedSimpleRootCones
import Langlands.GroupScheme.Rational.StandardLeviSplitComponentStatement

/-! # Strict uniformizer sections of actual standard Levi split components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.CocharacterUniformizer

/-- Along any compatible map into the maximal split torus, the strict
common-uniformizer section of an actual standard Levi split component is
exactly the section of the standard integral cocharacters for that face. -/
def StandardLeviStrictImageStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    ∀ (ν : cocharacterLattice T), IsGenericCocharacter i ν →
      ∀ (J : Set (characterLattice T)), J ⊆ simpleRelativeRoots i ν →
        ∀ (L : GroupScheme (Spec (CommRingCat.of F))) (j : L ⟶ G),
          IsClosedSubgroup j → (standardLevi i ν J).IsRepresentedBy j →
          ∀ (A : CommGroupScheme (Spec (CommRingCat.of F))) (a : A.toGrp ⟶ L),
            IsSplitComponent a → ∀ (f : A ⟶ T),
              CommGroupScheme.groupHom f ≫ i = a ≫ j →
              (rationalPoints.map (CommGroupScheme.groupHom f)) ''
                  CAstrict F A (restrictedSimpleCharacters i ν J f) =
                (fun ξ : cocharacterLattice T =>
                  latticeSection F T (Multiplicative.ofAdd ξ)) ''
                    {ξ | IsStandardCocharacter i ν J ξ}

end Langlands.GroupScheme.CocharacterUniformizer
