import Langlands.GroupScheme.Rational.StandardLeviCenterStatements
import Langlands.GroupScheme.Rational.StandardRepresentability

/-! # Center targets for the canonical standard Levi representative

The representative and inclusion are the actual `Standard.leviScheme` and
`Standard.leviHom`. Connected reductivity and split-component data remain explicit
inputs; their structural existence target is separate.
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

/-- The full scheme-center point map for the canonical representative of the same
all-test standard Levi. -/
def canonicalStandardLeviSchemeCenterToCenter :
    schemeCenterPoints (Standard.leviScheme i ν J) →*
      Subgroup.center (standardLeviPoints i ν J) :=
  standardLeviSchemeCenterToCenter i ν J (Standard.leviHom i ν J)
    (Standard.isRepresentedBy_leviHom i ν J)

@[simp] theorem canonicalStandardLeviSchemeCenterToCenter_val
    (z : schemeCenterPoints (Standard.leviScheme i ν J)) :
    ((canonicalStandardLeviSchemeCenterToCenter i ν J z).val : rationalPoints G) =
      rationalPoints.map (Standard.leviHom i ν J) z.val := rfl

/-- The actual central point map followed by the canonical standard-Levi center map. -/
def canonicalStandardLeviCentralRationalPointsMap
    {H : GroupScheme (Spec (CommRingCat.of F))}
    (a : H ⟶ Standard.leviScheme i ν J) (ha : IsCentral a) :
    rationalPoints H →* Subgroup.center (standardLeviPoints i ν J) :=
  standardLeviCentralRationalPointsMap i ν J (Standard.leviHom i ν J)
    (Standard.isRepresentedBy_leviHom i ν J) a ha

@[simp] theorem canonicalStandardLeviCentralRationalPointsMap_val
    {H : GroupScheme (Spec (CommRingCat.of F))}
    (a : H ⟶ Standard.leviScheme i ν J) (ha : IsCentral a) (x : rationalPoints H) :
    ((canonicalStandardLeviCentralRationalPointsMap i ν J a ha x).val :
      rationalPoints G) =
        rationalPoints.map (Standard.leviHom i ν J) (rationalPoints.map a x) := rfl

/-- When supplied with the structural factorization through the same maximal
split torus, the ambient point map agrees with that factorization. -/
theorem canonicalStandardLeviCentralRationalPointsMap_val_of_factorization
    {H : GroupScheme (Spec (CommRingCat.of F))}
    (a : H ⟶ Standard.leviScheme i ν J) (ha : IsCentral a) (g : H ⟶ T.toGrp)
    (hcomp : g ≫ i = a ≫ Standard.leviHom i ν J) (x : rationalPoints H) :
    ((canonicalStandardLeviCentralRationalPointsMap i ν J a ha x).val :
      rationalPoints G) = rationalPoints.map i (rationalPoints.map g x) := by
  change (x ≫ a.hom.hom) ≫ (Standard.leviHom i ν J).hom.hom =
    (x ≫ g.hom.hom) ≫ i.hom.hom
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun f => x ≫ f)
    (congrArg (fun f : H ⟶ G => f.hom.hom) hcomp).symm

variable [TopologicalSpace F] [IsAffine G.X.left]
  [IsAffine (Standard.leviScheme i ν J).X.left]

/-- The canonical center map is a homeomorphism for the independently defined
scheme-center and ambient-subgroup topologies. -/
def CanonicalStandardLeviRationalCenterComparison : Prop :=
  StandardLeviRationalCenterComparison i ν J (Standard.leviHom i ν J)
    (Standard.isRepresentedBy_leviHom i ν J)

/-- Compactness of the full center point quotient of the named canonical standard
Levi, conditional on its actual connected reductivity and split-component input. -/
def CanonicalStandardLeviCenterCompactnessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (_hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    IsGenericCocharacter i ν →
    ∀ (J : Set (characterLattice T)), J ⊆ simpleRelativeRoots i ν →
    ∀ (hM : IsConnectedReductive (Standard.leviScheme i ν J))
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      (a : A.toGrp ⟶ Standard.leviScheme i ν J) (hA : IsSplitComponent a),
      haveI := hM.isAffineHom
      haveI : IsAffine (Standard.leviScheme i ν J).X.left :=
        isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
      letI := centralPointQuotientTopology a hA.isCentralSplitTorus.isCentral
      CompactSpace (CentralPointQuotient a hA.isCentralSplitTorus.isCentral)

/-- Full scheme-center versus abstract-center comparison for the named canonical
standard Levi, retaining actual connected reductivity as an input. -/
def CanonicalStandardLeviRationalCenterComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (_hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    IsGenericCocharacter i ν →
    ∀ (J : Set (characterLattice T)), J ⊆ simpleRelativeRoots i ν →
    ∀ (hM : IsConnectedReductive (Standard.leviScheme i ν J)),
      haveI := hM.isAffineHom
      haveI : IsAffine (Standard.leviScheme i ν J).X.left :=
        isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
      CanonicalStandardLeviRationalCenterComparison i ν J

/-- The two independent center targets for the canonical standard Levi family. -/
def CanonicalStandardLeviCenterStatements : Prop :=
  CanonicalStandardLeviCenterCompactnessStatement.{u} ∧
    CanonicalStandardLeviRationalCenterComparisonStatement.{u}

end Langlands.GroupScheme
