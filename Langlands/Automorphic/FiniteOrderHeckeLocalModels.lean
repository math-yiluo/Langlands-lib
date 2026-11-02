import Langlands.Automorphic.FiniteOrderHeckeRealization
import Langlands.Automorphic.OperatorLocalRestriction
import Langlands.Automorphic.OperatorDeterminantTwistFiniteComparison
import Langlands.Automorphic.FiniteLocalDeterminantTwist
import Langlands.Representation.Filtration.ExactFunctorIrreducibility

/-! # Finite and local character models of actual automorphic Hecke lines -/

noncomputable section

universe uF

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.FiniteOrderHeckeRealization

open Langlands.Global ContinuousRationalFunctions

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

local instance heckeLocalModelGroup1 : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeLocalModelGroup2 : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeLocalModelGroup3 : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeLocalModelGroup4 : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance heckeLocalModelGroup5 : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance heckeLocalModelGroup6 : AddCommGroup (realization F n χ hχ).Space := Submodule.addCommGroup _

/-- The scalar representation of the actual finite adelic determinant character. -/
def finiteModel : Representation ℂ (FiniteAdelicGL F n) ℂ :=
  Langlands.characterRepresentation (χ.finiteAdelicDeterminant n).toMonoidHom

/-- The explicit scalar equivalence intertwines the original finite action. -/
def finiteModelEquiv :
    (finiteModel F n χ).Equiv (realization F n χ hχ).finiteRepresentation :=
  Representation.Equiv.mk (scalarEquiv F n χ hχ) (fun d => by
    apply LinearMap.ext
    intro c
    exact (finiteRepresentation_scalarEquiv F n χ hχ d c).symm)

@[simp]
theorem finiteModelEquiv_apply (c : ℂ) :
    finiteModelEquiv F n χ hχ c = scalarEquiv F n χ hχ c := rfl

/-- The same model is equivalent to the actual finite invariant image in forms. -/
def finiteFormEquiv :
    (finiteModel F n χ).Equiv (realization F n χ hχ).toFiniteRealization.representation :=
  (finiteModelEquiv F n χ hχ).trans (realization F n χ hχ).finiteEquiv

@[simp]
theorem finiteFormEquiv_inclusion (c : ℂ) :
    (realization F n χ hχ).toFiniteRealization.inclusion
        (finiteFormEquiv F n χ hχ c) = form F n χ hχ c := rfl

include hχ in
theorem finiteModel_isSmooth : Langlands.IsSmooth (finiteModel F n χ) :=
  Langlands.isSmooth_of_injective (finiteModelEquiv F n χ hχ).toIntertwiningMap
    (finiteModelEquiv F n χ hχ).injective
    (realization F n χ hχ).finiteRepresentation_isSmooth

/-- The finite action is irreducible on the actual embedded line. -/
theorem finiteRepresentation_isIrreducible :
    (realization F n χ hχ).finiteRepresentation.IsIrreducible :=
  Langlands.ExactFunctorIrreducibility.isIrreducible_of_finrank_eq_one
    (Langlands.SmoothRep.of _ (realization F n χ hχ).finiteRepresentation_isSmooth)
    (realization_finrank F n χ hχ)

/-- Admissibility follows from smoothness and the actual finite-dimensional carrier. -/
theorem finiteRepresentation_isAdmissible :
    Langlands.IsAdmissible (realization F n χ hχ).finiteRepresentation := by
  let : FiniteDimensional ℂ (realization F n χ hχ).Space :=
    FiniteDimensional.of_injective (scalarEquiv F n χ hχ).symm.toLinearMap
      (scalarEquiv F n χ hχ).symm.injective
  exact ⟨(realization F n χ hχ).finiteRepresentation_isSmooth, fun _ => inferInstance⟩

variable (v : FinitePlace F)

/-- The scalar representation of the actual determinant character at one finite place. -/
def localModel : Representation ℂ (FiniteLocalGL F n v) ℂ :=
  Langlands.characterRepresentation (χ.finiteLocalDeterminant n v).toMonoidHom

theorem localRepresentation_scalarEquiv (g : FiniteLocalGL F n v) (c : ℂ) :
    (realization F n χ hχ).localRepresentation v g (scalarEquiv F n χ hχ c) =
      scalarEquiv F n χ hχ ((χ.finiteLocalDeterminant n v g : ℂ) * c) :=
  finiteRepresentation_scalarEquiv F n χ hχ (FiniteAdelicGL.localInclusion F n v g) c

/-- This is the whole local restriction of the constructed actual line. -/
def localModelEquiv :
    (localModel F n χ v).Equiv ((realization F n χ hχ).localRepresentation v) :=
  Representation.Equiv.mk (scalarEquiv F n χ hχ) (fun g => by
    apply LinearMap.ext
    intro c
    exact (localRepresentation_scalarEquiv F n χ hχ v g c).symm)

@[simp]
theorem localModelEquiv_apply (c : ℂ) :
    localModelEquiv F n χ hχ v c = scalarEquiv F n χ hχ c := rfl

/-- An explicit equivalence with the existing embedded local form subspace. -/
def localFormEquiv :
    (localModel F n χ v).Equiv
      ((realization F n χ hχ).toFiniteRealization.toLocal F n v).representation :=
  (localModelEquiv F n χ hχ v).trans ((realization F n χ hχ).localFormEquiv v)

@[simp]
theorem localFormEquiv_inclusion (c : ℂ) :
    ((realization F n χ hχ).toFiniteRealization.toLocal F n v).inclusion
        (localFormEquiv F n χ hχ v c) = form F n χ hχ c := rfl

include hχ in
theorem localModel_isSmooth : Langlands.IsSmooth (localModel F n χ v) :=
  Langlands.isSmooth_of_injective (localModelEquiv F n χ hχ v).toIntertwiningMap
    (localModelEquiv F n χ hχ v).injective
    ((realization F n χ hχ).localRepresentation_isSmooth v)

/-- In this one-dimensional example the whole local restriction is irreducible. -/
theorem localRepresentation_isIrreducible :
    ((realization F n χ hχ).localRepresentation v).IsIrreducible :=
  Langlands.ExactFunctorIrreducibility.isIrreducible_of_finrank_eq_one
    ((realization F n χ hχ).localSmoothRepresentation v)
    (realization_finrank F n χ hχ)

theorem localRepresentation_isAdmissible :
    Langlands.IsAdmissible ((realization F n χ hχ).localRepresentation v) := by
  let : FiniteDimensional ℂ (realization F n χ hχ).Space :=
    FiniteDimensional.of_injective (scalarEquiv F n χ hχ).symm.toLinearMap
      (scalarEquiv F n χ hχ).symm.injective
  exact ⟨(realization F n χ hχ).localRepresentation_isSmooth v, fun _ => inferInstance⟩

end Langlands.Automorphic.FiniteOrderHeckeRealization
