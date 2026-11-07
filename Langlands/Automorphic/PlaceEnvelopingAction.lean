import Langlands.Automorphic.PlaceLieAction
import Langlands.Global.ArchimedeanPlaceEnveloping

/-! # Genuine place enveloping actions on the original automorphic carrier -/

noncomputable section
universe u

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance : AddCommGroup S.Space := Submodule.addCommGroup _
local instance : AddCommGroup T.Space := Submodule.addCommGroup _

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual global differential restricts through the injective real-place enveloping map. -/
def realPlaceEnvelopingAction (v : RP) :
    RealPlaceEnvelopingAlgebra n →ₐ[ℂ] Module.End ℂ S.Space :=
  S.envelopingAction.comp (realPlaceEnvelopingInclusion F n v)

/-- At a complex place the full underlying real matrix Lie algebra acts before complexification. -/
def complexPlaceEnvelopingAction (v : CP) :
    ComplexPlaceEnvelopingAlgebra n →ₐ[ℂ] Module.End ℂ S.Space :=
  S.envelopingAction.comp (complexPlaceEnvelopingInclusion F n v)

theorem realPlaceEnvelopingAction_generator (v : RP) (X : ℂ ⊗[ℝ] RM) :
    S.realPlaceEnvelopingAction v (realPlaceEnvelopingGenerator n X) =
      S.realPlaceLieAction v X := by
  change S.envelopingAction
      (realPlaceEnvelopingInclusion F n v (realPlaceEnvelopingGenerator n X)) =
    S.envelopingAction (envelopingGenerator F n (realPlaceComplexLieInclusion F n v X))
  exact congrArg S.envelopingAction (realPlaceEnvelopingInclusion_generator F n v X)

theorem complexPlaceEnvelopingAction_generator (v : CP) (X : ℂ ⊗[ℝ] CM) :
    S.complexPlaceEnvelopingAction v (complexPlaceEnvelopingGenerator n X) =
      S.complexPlaceLieAction v X := by
  change S.envelopingAction
      (complexPlaceEnvelopingInclusion F n v (complexPlaceEnvelopingGenerator n X)) =
    S.envelopingAction (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v X))
  exact congrArg S.envelopingAction (complexPlaceEnvelopingInclusion_generator F n v X)

/-- The restriction is exactly the universal extension of the original place Lie action. -/
theorem realPlaceEnvelopingAction_eq_lift (v : RP) :
    S.realPlaceEnvelopingAction v =
      UniversalEnvelopingAlgebra.lift ℂ (S.realPlaceLieAction v) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change S.realPlaceEnvelopingAction v (realPlaceEnvelopingGenerator n X) =
    UniversalEnvelopingAlgebra.lift ℂ (S.realPlaceLieAction v)
      (UniversalEnvelopingAlgebra.ι ℂ X)
  exact (S.realPlaceEnvelopingAction_generator v X).trans
    (UniversalEnvelopingAlgebra.lift_ι_apply ℂ (S.realPlaceLieAction v) X).symm

theorem complexPlaceEnvelopingAction_eq_lift (v : CP) :
    S.complexPlaceEnvelopingAction v =
      UniversalEnvelopingAlgebra.lift ℂ (S.complexPlaceLieAction v) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change S.complexPlaceEnvelopingAction v (complexPlaceEnvelopingGenerator n X) =
    UniversalEnvelopingAlgebra.lift ℂ (S.complexPlaceLieAction v)
      (UniversalEnvelopingAlgebra.ι ℂ X)
  exact (S.complexPlaceEnvelopingAction_generator v X).trans
    (UniversalEnvelopingAlgebra.lift_ι_apply ℂ (S.complexPlaceLieAction v) X).symm

/-- Every local enveloping operator is the original differential on the embedded functions. -/
theorem inclusion_realPlaceEnvelopingAction (v : RP)
    (a : RealPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.inclusion (S.realPlaceEnvelopingAction v a f) =
      stableAutomorphicEnvelopingAction F n (realPlaceEnvelopingInclusion F n v a)
        (S.inclusion f) := rfl

theorem inclusion_complexPlaceEnvelopingAction (v : CP)
    (a : ComplexPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.inclusion (S.complexPlaceEnvelopingAction v a f) =
      stableAutomorphicEnvelopingAction F n (complexPlaceEnvelopingInclusion F n v a)
        (S.inclusion f) := rfl

theorem finiteRepresentation_realPlaceEnvelopingAction (d : FiniteAdelicGL F n)
    (v : RP) (a : RealPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.finiteRepresentation d (S.realPlaceEnvelopingAction v a f) =
      S.realPlaceEnvelopingAction v a (S.finiteRepresentation d f) :=
  S.finiteRepresentation_envelopingAction d (realPlaceEnvelopingInclusion F n v a) f

theorem finiteRepresentation_complexPlaceEnvelopingAction (d : FiniteAdelicGL F n)
    (v : CP) (a : ComplexPlaceEnvelopingAlgebra n) (f : S.Space) :
    S.finiteRepresentation d (S.complexPlaceEnvelopingAction v a f) =
      S.complexPlaceEnvelopingAction v a (S.finiteRepresentation d f) :=
  S.finiteRepresentation_envelopingAction d (complexPlaceEnvelopingInclusion F n v a) f

namespace Intertwiner

variable {S T}

theorem realPlaceEnvelopingAction (A : S.Intertwiner T) (v : RP)
    (a : RealPlaceEnvelopingAlgebra n) (f : S.Space) :
    A (S.realPlaceEnvelopingAction v a f) = T.realPlaceEnvelopingAction v a (A f) :=
  A.differential (realPlaceEnvelopingInclusion F n v a) f

theorem complexPlaceEnvelopingAction (A : S.Intertwiner T) (v : CP)
    (a : ComplexPlaceEnvelopingAlgebra n) (f : S.Space) :
    A (S.complexPlaceEnvelopingAction v a f) = T.complexPlaceEnvelopingAction v a (A f) :=
  A.differential (complexPlaceEnvelopingInclusion F n v a) f

/-- The same full linear map intertwines every element of the actual local enveloping algebra. -/
def realPlaceEnvelopingRestriction (A : S.Intertwiner T) (v : RP) :
    Representation.IntertwiningMap (S.realPlaceEnvelopingAction v).toMonoidHom
      (T.realPlaceEnvelopingAction v).toMonoidHom where
  toLinearMap := A.toLinearMap
  isIntertwining' a := LinearMap.ext (Intertwiner.realPlaceEnvelopingAction A v a)

def complexPlaceEnvelopingRestriction (A : S.Intertwiner T) (v : CP) :
    Representation.IntertwiningMap (S.complexPlaceEnvelopingAction v).toMonoidHom
      (T.complexPlaceEnvelopingAction v).toMonoidHom where
  toLinearMap := A.toLinearMap
  isIntertwining' a := LinearMap.ext (Intertwiner.complexPlaceEnvelopingAction A v a)

end Intertwiner

namespace Equivalence

variable {S T}

/-- Full automorphic equivalence retains the local enveloping action on the same vectors. -/
def realPlaceEnvelopingRestriction (e : S.Equivalence T) (v : RP) :
    Representation.Equiv (S.realPlaceEnvelopingAction v).toMonoidHom
      (T.realPlaceEnvelopingAction v).toMonoidHom :=
  Representation.Equiv.mk e.toLinearEquiv
    (fun a => LinearMap.ext (Intertwiner.realPlaceEnvelopingAction e.toIntertwiningMap v a))

def complexPlaceEnvelopingRestriction (e : S.Equivalence T) (v : CP) :
    Representation.Equiv (S.complexPlaceEnvelopingAction v).toMonoidHom
      (T.complexPlaceEnvelopingAction v).toMonoidHom :=
  Representation.Equiv.mk e.toLinearEquiv
    (fun a => LinearMap.ext (Intertwiner.complexPlaceEnvelopingAction e.toIntertwiningMap v a))

end Equivalence
end OperatorRealization
end Langlands.Automorphic
