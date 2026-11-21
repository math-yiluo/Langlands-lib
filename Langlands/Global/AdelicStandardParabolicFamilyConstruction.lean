import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Geometry.Building.SpecialCompactLevi
import Langlands.Global.ReductiveInfiniteAdelicManifold
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof
import Langlands.GroupScheme.Rational.StandardLeviSplitComponentProof
import Langlands.Representation.LanglandsClassification.StandardParabolicRootPresentation

/-! # Construction of a compatible adelic standard parabolic family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Aubert.General.RepresentedParabolic

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (hG : IsConnectedReductive G) {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
  (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)

/-- The canonical represented standard parabolics, assembled with their
Levis, radicals, split components and the common ambient coroots. -/
def ofMaximalSplitTorus : StandardParabolicFamily F G := by
  let datum (J : StandardIndex F G i ν) :=
    ParabolicDatum.standard i ν hG hi hν J.val J.property
  let split (J : StandardIndex F G i ν) :=
    (standardLeviSplitComponentStatement F G hG T i hi ν hν J.val J.property).2
  let A (J : StandardIndex F G i ν) := (split J).choose
  let a (J : StandardIndex F G i ν) := (split J).choose_spec.choose
  let factor (J : StandardIndex F G i ν) := (split J).choose_spec.choose_spec.choose
  let hFactor (J : StandardIndex F G i ν) := (split J).choose_spec.choose_spec.choose_spec
  let hM (J : StandardIndex F G i ν) :=
    (standardLeviSplitComponentStatement F G hG T i hi ν hν J.val J.property).1
  refine
    { connectedReductive := hG
      T := T
      i := i
      ν := ν
      maximalSplit := hi
      generic := hν
      coroots := (relativeRootReflectionExistence F G hG T i hi).choose
      P := fun J => (datum J).P
      M := fun J => (datum J).M
      U := fun J => (datum J).U
      A := A
      p := fun J => (datum J).p
      iU := fun J => (datum J).r
      l := fun J => (datum J).l
      a := a
      f := fun J => Additive.ofMul (factor J)
      torus := fun J => Standard.leviTorusHom i ν J.val
      isCompatible := fun J => (ParabolicDatum.standardRootPresentation i ν hG hi hν J.val J.property
        (a J) (hFactor J).1 (factor J) (hFactor J).2).isCompatible
      isUnipotentRadical := fun J => (datum J).hr
      torus_comp := ?_
      leviDim := fun J => (hM J).smoothDimension
      leviSmooth := fun J => (hM J).smoothDimension_spec
      affineP := ?_
      finiteTypeP := fun J => (Standard.isClosedSubgroup_parabolicHom i ν J.val).locallyOfFiniteType
      affineM := fun J => (hM J).affineScheme
      finiteTypeM := fun J => (Standard.isClosedSubgroup_leviHom i ν J.val).locallyOfFiniteType
      affineU := ?_
      closedU := ?_ }
  · intro J
    change Standard.leviTorusHom i ν J.val ≫
      Standard.leviToParabolic i ν J.val ≫ Standard.parabolicHom i ν J.val = i
    rw [Standard.leviToParabolic_comp, Standard.leviTorusHom_comp]
  · intro J
    exact @isAffine_of_isAffineHom _ _ (Standard.parabolicScheme i ν J.val).X.hom
      (Standard.isClosedSubgroup_parabolicHom i ν J.val).isAffineHom inferInstance
  · intro J
    exact @isAffine_of_isAffineHom _ _ (Standard.unipotentScheme i ν J.val).X.hom
      (Standard.isClosedSubgroup_unipotentHom i ν J.val).isAffineHom inferInstance
  · intro J
    change IsClosedSubgroup (Standard.unipotentToParabolic i ν J.val ≫ Standard.parabolicHom i ν J.val)
    rw [Standard.unipotentToParabolic_comp]
    exact Standard.isClosedSubgroup_unipotentHom i ν J.val

end Langlands.Global.StandardParabolicFamily
