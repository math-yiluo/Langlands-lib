import Langlands.AbelianScheme.LieBaseChange
import Langlands.AbelianScheme.LieFunctor

/-! # Naturality of cotangent base change in actual group homomorphisms -/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

namespace Langlands.GroupScheme

/-- The actual cotangent base-change comparison is natural in all group-scheme
homomorphisms over the original base. -/
def CotangentBaseChangeNaturalityStatement (S : AlgebraicGeometry.Scheme.{u}) : Prop :=
  ∀ (T : AlgebraicGeometry.Scheme.{u}) (b : T ⟶ S)
      (G H : GroupScheme S) (f : G ⟶ H),
    (pullback b).map (cotangentMap f) ≫ cotangentBaseChangeMap b G =
      cotangentBaseChangeMap b H ≫ cotangentMap ((baseChange b).map f)

end Langlands.GroupScheme

namespace Langlands.AbelianScheme

/-- Cotangent naturality for actual abelian-scheme homomorphisms, using the
published forgetful maps to group schemes. -/
def CotangentBaseChangeNaturalityStatement (S : AlgebraicGeometry.Scheme.{u}) : Prop :=
  ∀ (T : AlgebraicGeometry.Scheme.{u}) (b : T ⟶ S)
      (A B : AbelianScheme S) (f : A ⟶ B),
    (pullback b).map (GroupScheme.cotangentMap (groupHom f)) ≫
        GroupScheme.cotangentBaseChangeMap b A.toGrp =
      GroupScheme.cotangentBaseChangeMap b B.toGrp ≫
        GroupScheme.cotangentMap (groupHom ((baseChange b).map f))

end Langlands.AbelianScheme

namespace Langlands

/-- The group-scheme cotangent naturality square and its actual abelian-scheme
specialization as a single proof target. -/
def CotangentBaseChangeNaturalityStatements (S : AlgebraicGeometry.Scheme.{u}) : Prop :=
  GroupScheme.CotangentBaseChangeNaturalityStatement S ∧
    AbelianScheme.CotangentBaseChangeNaturalityStatement S

end Langlands
