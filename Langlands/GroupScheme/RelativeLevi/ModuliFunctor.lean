import Langlands.GroupScheme.RelativeLevi.ModuliFieldReduction
import Langlands.GroupScheme.Reductive.SmoothRadicalFieldExtensionProof

/-! # The actual relative Levi moduli presheaf -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- Pullback of an actual relative Levi inclusion is again a relative Levi
inclusion along every base morphism. -/
theorem IsRelativeLeviSubgroup.baseChange {S T : Scheme.{u}} {P L : GroupScheme S}
    {l : L ⟶ P} (hl : IsRelativeLeviSubgroup l) (b : T ⟶ S) :
    IsRelativeLeviSubgroup ((baseChange b).map l) :=
  hl.baseChange_of_field_extension smoothAlgebraicallyClosedUnipotentRadicalExtension b

namespace RelativeLevi

variable {S : Scheme.{u}} {P U : GroupScheme S} {M T X : Over S}

/-- Actual Levi images are stable under restriction for every ambient group. -/
theorem restrictionStable (P : GroupScheme S) : RestrictionStable P :=
  restrictionStable_of_field_extension smoothAlgebraicallyClosedUnipotentRadicalExtension P

/-- The presheaf of actual Levi subgroup images of the pullbacks of `P`. -/
def moduliFunctor (P : GroupScheme S) : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  moduliFunctorOfFieldExtension smoothAlgebraicallyClosedUnipotentRadicalExtension P

/-- Restriction in the Levi presheaf is actual restriction of subgroup images. -/
theorem moduliFunctor_map_val (a : T ⟶ M)
    (F : LeviImage ((baseChange M.hom).obj P)) :
    ((moduliFunctor P).map a.op F : LeviImage ((baseChange T.hom).obj P)).val =
      restrictImage (P := P) a F.val :=
  LeviImage.restrict_val (restrictionStable P) a F

/-- The natural inclusion of Levi images into all subgroup functors. -/
def moduliInclusion (P : GroupScheme S) : moduliFunctor P ⟶ subgroupPresheaf P :=
  moduliInclusionOfStability (restrictionStable P)

/-- Restriction is equivariant for conjugation and restriction of group points. -/
theorem moduliFunctor_map_smul (r : U ⟶ P) (a : T ⟶ M) (g : M ⟶ U.X)
    (F : (moduliFunctor P).obj (op M)) :
    letI : MulAction (M ⟶ U.X) ((moduliFunctor P).obj (op M)) := leviConjugationAction r M
    letI : MulAction (T ⟶ U.X) ((moduliFunctor P).obj (op T)) := leviConjugationAction r T
    (moduliFunctor P).map a.op (g • F) = (a ≫ g) • (moduliFunctor P).map a.op F :=
  LeviImage.restrict_smul (restrictionStable P) r a g F

namespace ModuliRepresentation

/-- The correspondence in the Levi torsor statement represents the actual
presheaf, using the same point equivalences. -/
def representableBy (ρ : ModuliRepresentation P X) : (moduliFunctor P).RepresentableBy X where
  homEquiv {T} := ρ.pointsEquiv T
  homEquiv_comp {T M} a x := by
    change ρ.pointsEquiv T (a ≫ x) =
      (ρ.pointsEquiv M x).restrict (RelativeLevi.restrictionStable P) a
    apply LeviImage.ext
    exact ρ.naturality a x

/-- Equivariance of the torsor correspondence is equivariance for the
conjugation action on the actual presheaf. -/
theorem representableBy_equivariant (ρ : ModuliRepresentation P X)
    (r : U ⟶ P) [ModObj U.X X] (hρ : ρ.IsEquivariant r) (T : Over S)
    (g : T ⟶ U.X) (x : T ⟶ X) :
    letI : MulAction (T ⟶ U.X) ((moduliFunctor P).obj (op T)) := leviConjugationAction r T
    ρ.representableBy.homEquiv (g • x) = g • ρ.representableBy.homEquiv x :=
  hρ T g x

end ModuliRepresentation
end RelativeLevi
end Langlands.GroupScheme
