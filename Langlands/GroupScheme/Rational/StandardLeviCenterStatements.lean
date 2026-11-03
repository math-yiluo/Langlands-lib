import Langlands.GroupScheme.Rational.CenterSplitComponent
import Langlands.GroupScheme.Rational.StandardLeviPointComparison
import Langlands.Representation.Plancherel.LocalFieldUnits
import Mathlib.GroupTheory.Subgroup.Center

/-! # Actual center targets for the same represented standard Levi

The point map uses the existing all-test `standardLevi` representation. Compactness
concerns the full scheme-center point quotient. Its comparison with the abstract
center of `standardLeviPoints` is a separate proposition.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (J : Set (characterLattice T))
  {M : GroupScheme (Spec (CommRingCat.of F))} (j : M ⟶ G)
  (hj : (standardLevi i ν J).IsRepresentedBy j)

/-- Scheme-center points mapped into the abstract center of the same actual
standard Levi subgroup by the explicit point equivalence induced by `j`. -/
def standardLeviSchemeCenterToCenter :
    schemeCenterPoints M →* Subgroup.center (standardLeviPoints i ν J) :=
  (Subgroup.centerCongr
    (standardLeviRationalPointsEquiv i ν J j hj)).toMonoidHom.comp
      (schemeCenterPointsToCenter M)

@[simp] theorem standardLeviSchemeCenterToCenter_val (z : schemeCenterPoints M) :
    ((standardLeviSchemeCenterToCenter i ν J j hj z).val : rationalPoints G) =
      rationalPoints.map j z.val := rfl

/-- A central point map followed by the explicit comparison with the abstract
standard-Levi center. In particular this is the actual map on split-component points. -/
def standardLeviCentralRationalPointsMap
    {H : GroupScheme (Spec (CommRingCat.of F))} (a : H ⟶ M) (ha : IsCentral a) :
    rationalPoints H →* Subgroup.center (standardLeviPoints i ν J) :=
  (standardLeviSchemeCenterToCenter i ν J j hj).comp
    (centralRationalPointsMap a ha)

@[simp] theorem standardLeviCentralRationalPointsMap_val
    {H : GroupScheme (Spec (CommRingCat.of F))} (a : H ⟶ M) (ha : IsCentral a)
    (x : rationalPoints H) :
    ((standardLeviCentralRationalPointsMap i ν J j hj a ha x).val : rationalPoints G) =
      rationalPoints.map j (rationalPoints.map a x) := rfl

variable [TopologicalSpace F] [IsAffine G.X.left]

/-- The subgroup topology on the abstract center of `standardLeviPoints`, itself
given the subgroup topology inherited from the canonical topology of `G(F)`. -/
@[instance_reducible]
def standardLeviAbstractCenterTopology :
    TopologicalSpace (Subgroup.center (standardLeviPoints i ν J)) := by
  letI : TopologicalSpace (standardLeviPoints i ν J) := standardLeviPointTopology i ν J
  exact inferInstance

variable [IsAffine M.X.left]

/-- The explicit center map is a homeomorphism for the canonical scheme-center
point topology and the inherited abstract standard-Levi center topology. -/
def StandardLeviRationalCenterComparison : Prop :=
  letI : TopologicalSpace (schemeCenterPoints M) := schemeCenterPointTopology M
  letI : TopologicalSpace (Subgroup.center (standardLeviPoints i ν J)) :=
    standardLeviAbstractCenterTopology i ν J
  IsHomeomorph (standardLeviSchemeCenterToCenter i ν J j hj)

/-- Compactness of the full scheme-center point quotient for every split component
of the same closed represented standard Levi, over any nonarchimedean local field. -/
def StandardLeviCenterCompactnessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (_hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    IsGenericCocharacter i ν →
    ∀ (J : Set (characterLattice T)), J ⊆ simpleRelativeRoots i ν →
    ∀ (M : GroupScheme (Spec (CommRingCat.of F))) (hM : IsConnectedReductive M)
      (j : M ⟶ G), IsClosedSubgroup j →
    (standardLevi i ν J).IsRepresentedBy j →
    ∀ (A : CommGroupScheme (Spec (CommRingCat.of F))) (a : A.toGrp ⟶ M)
      (hA : IsSplitComponent a),
      haveI := hM.isAffineHom
      haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
      letI := centralPointQuotientTopology a hA.isCentralSplitTorus.isCentral
      CompactSpace (CentralPointQuotient a hA.isCentralSplitTorus.isCentral)

/-- Scheme-center versus abstract-center comparison for the same closed represented
standard Levi, with no center equality or topology comparison as a premise. -/
def StandardLeviRationalCenterComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (_hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    IsGenericCocharacter i ν →
    ∀ (J : Set (characterLattice T)), J ⊆ simpleRelativeRoots i ν →
    ∀ (M : GroupScheme (Spec (CommRingCat.of F))) (hM : IsConnectedReductive M)
      (j : M ⟶ G), IsClosedSubgroup j →
    ∀ hj : (standardLevi i ν J).IsRepresentedBy j,
      haveI := hM.isAffineHom
      haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
      StandardLeviRationalCenterComparison i ν J j hj

/-- The two independent actual standard-Levi center targets. -/
def StandardLeviCenterStatements : Prop :=
  StandardLeviCenterCompactnessStatement.{u} ∧
    StandardLeviRationalCenterComparisonStatement.{u}

end Langlands.GroupScheme
