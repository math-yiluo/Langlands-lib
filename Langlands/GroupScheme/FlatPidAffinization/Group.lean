import Langlands.GroupScheme.FlatPidAffinization.Category
import Langlands.GroupScheme.FlatPidAffinization.Functor
import Langlands.AlgebraicGeometry.FlatPidAffinizationProducts

/-! # The actual group and canonical homomorphism on affinization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.Limits hiding prodComparison terminalComparison

namespace Langlands.GroupScheme.FlatPidAffinization

/-- Affinization restricted to the flat quasi-compact separated category. -/
abbrev restrictedAffinization (R : CommRingCat.{u}) :
    SchemeCategory (Spec R) ⥤ Over (Spec R) :=
  inclusion (Spec R) ⋙ affinizationFunctor R

instance {S : Scheme.{u}} (X : SchemeCategory S) : Flat X.obj.hom := X.property.1
instance {S : Scheme.{u}} (X : SchemeCategory S) : QuasiCompact X.obj.hom := X.property.2.1
instance {S : Scheme.{u}} (X : SchemeCategory S) : IsSeparated X.obj.hom := X.property.2.2

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

instance isIso_restrictedTerminalComparison :
    IsIso (terminalComparison (restrictedAffinization (CommRingCat.of R))) := by
  change IsIso (terminalComparison (affinizationFunctor (CommRingCat.of R)))
  infer_instance

instance isIso_restrictedProdComparison
    (X Y : SchemeCategory (Spec (CommRingCat.of R))) :
    IsIso (prodComparison (restrictedAffinization (CommRingCat.of R)) X Y) := by
  change IsIso (prodComparison (affinizationFunctor (CommRingCat.of R)) X.obj Y.obj)
  infer_instance

instance preservesFiniteProducts_restrictedAffinization :
    PreservesFiniteProducts (restrictedAffinization (CommRingCat.of R)) := by
  let F := restrictedAffinization (CommRingCat.of R)
  have := preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison F
  have := preservesLimit_empty_of_isIso_terminalComparison F
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) F :=
    preservesLimitsOfShape_pempty_of_preservesTerminal F
  exact PreservesFiniteProducts.of_preserves_binary_and_terminal F

local instance : (restrictedAffinization (CommRingCat.of R)).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

/-- The actual group object carried by the prescribed spectrum of global functions. -/
def affinizationGroup (G : GroupScheme (Spec (CommRingCat.of R)))
    [Flat G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom] :
    GroupScheme (Spec (CommRingCat.of R)) :=
  (restrictedAffinization (CommRingCat.of R)).mapGrp.obj (restrictedGroup G)

@[simp] theorem affinizationGroup_X (G : GroupScheme (Spec (CommRingCat.of R)))
    [Flat G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom] :
    (affinizationGroup G).X =
      Over.mk (Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.X.hom.appTop)) := rfl

/-- Canonical affinization, as a natural morphism from the full inclusion. -/
def restrictedToAffinization :
    inclusion (Spec (CommRingCat.of R)) ⟶ restrictedAffinization (CommRingCat.of R) :=
  Functor.whiskerLeft (inclusion _) (toAffinization _)

/-- The canonical map is a homomorphism of the actual group schemes. -/
def toAffinizationGroup (G : GroupScheme (Spec (CommRingCat.of R)))
    [Flat G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom] :
    G ⟶ affinizationGroup G :=
  (restrictedGroupIso G).inv ≫
    (Functor.mapGrpNatTrans (restrictedToAffinization (R := R))).app (restrictedGroup G)

@[simp] theorem toAffinizationGroup_left (G : GroupScheme (Spec (CommRingCat.of R)))
    [Flat G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom] :
    (toAffinizationGroup G).hom.hom.left = G.X.left.toSpecΓ := by
  change (𝟙 G.X.left) ≫ G.X.left.toSpecΓ = _
  simp

/-- The group structure directly on the prescribed `Over` object. -/
@[instance_reducible] def groupStructure (G : GroupScheme (Spec (CommRingCat.of R)))
    [Flat G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom] :
    GrpObj (Over.mk (Spec.map
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.X.hom.appTop))) :=
  (affinizationGroup G).grp

/-- The canonical over-base map is a monoid homomorphism for the constructed group law. -/
theorem toAffinization_isMonHom (G : GroupScheme (Spec (CommRingCat.of R)))
    [Flat G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom] :
    letI := groupStructure G
    IsMonHom (show G.X ⟶ Over.mk (Spec.map
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.X.hom.appTop)) from
      (toAffinization (CommRingCat.of R)).app G.X) := by
  let _ := groupStructure G
  have he : (toAffinizationGroup G).hom.hom =
      (toAffinization (CommRingCat.of R)).app G.X :=
    Over.OverMorphism.ext (toAffinizationGroup_left G)
  rw [← he]
  exact (toAffinizationGroup G).hom.isMonHom_hom

end Langlands.GroupScheme.FlatPidAffinization
