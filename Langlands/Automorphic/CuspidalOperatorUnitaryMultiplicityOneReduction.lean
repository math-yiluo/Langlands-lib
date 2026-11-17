import Langlands.Automorphic.CuspidalOperatorMultiplicityOneStatement
import Langlands.Automorphic.CuspidalContragredientExistenceProof

/-! # Reduction of actual cuspidal multiplicity one to unitary central characters

Full operator equivalences preserve central characters and survive a common actual
Hecke determinant twist. The published unitarizing character therefore reduces the
unrestricted multiplicity-one target to its unitary-central-character case.
-/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global ContinuousRationalFunctions
open scoped NumberField

variable {F : Type u} [Field F] [NumberField F]

local instance unitaryReductionRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance unitaryReductionContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance unitaryReductionFiniteSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance unitaryReductionFormGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance unitaryReductionStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance unitaryReductionSpaceGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

private def equivalenceOfCommonConjugation
    {G V W V₁ W₁ : Type*} [Monoid G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup W₁] [Module ℂ W₁]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    (ρ₁ : Representation ℂ G V₁) (τ₁ : Representation ℂ G W₁)
    (σ : G → G) (E₁ : V ≃ₗ[ℂ] V₁) (E₂ : W ≃ₗ[ℂ] W₁)
    (h₁ : ∀ a v, ρ₁ a (E₁ v) = E₁ (ρ (σ a) v))
    (h₂ : ∀ a w, τ₁ a (E₂ w) = E₂ (τ (σ a) w))
    (e : ρ.Equiv τ) : ρ₁.Equiv τ₁ :=
  Representation.Equiv.mk (E₁.symm.trans (e.toLinearEquiv.trans E₂)) (fun a => by
    apply LinearMap.ext
    intro f
    obtain ⟨g, rfl⟩ := E₁.surjective f
    change E₂ (e (E₁.symm (ρ₁ a (E₁ g)))) =
      τ₁ a (E₂ (e (E₁.symm (E₁ g))))
    rw [h₁, E₁.symm_apply_apply, E₁.symm_apply_apply, h₂]
    exact congrArg E₂
      (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (σ a) g))

namespace OperatorRealization

variable {n : ℕ} {S T : OperatorRealization F n}

/-- A full operator equivalence preserves the central character on actual functions.
The finite local scalar actions determine the whole central character by idele density. -/
theorem Equivalence.hasCentralCharacter (e : S.Equivalence T) {ω : HeckeCharacter F}
    (hω : S.HasCentralCharacter ω) : T.HasCentralCharacter ω := by
  apply T.hasCentralCharacter_of_centralCharacterSubgroup_eq_top ω
  refine IdeleDensity.eq_top_of_isClosed (T.centralCharacterSubgroup ω) ∅
    (T.isClosed_centralCharacterSubgroup ω)
    (T.diagonalUnits_mem_centralCharacterSubgroup ω) ?_
  intro v _ a
  apply (T.finiteIdeleInclusion_mem_centralCharacterSubgroup_iff ω v a).mpr
  intro f
  obtain ⟨g, rfl⟩ := e.surjective f
  have hz : finiteIdeleInclusion F v a ∈ S.centralCharacterSubgroup ω :=
    (S.mem_centralCharacterSubgroup ω _).mpr fun h x =>
      S.centralCharacter_evaluate ω hω h _ x
  have hs := (S.finiteIdeleInclusion_mem_centralCharacterSubgroup_iff ω v a).mp hz g
  change S.finiteRepresentation
    (FiniteAdelicGL.localInclusion F n v (Matrix.GeneralLinearGroup.scalar (Fin n) a)) g =
      (ω.finiteComponent v a : ℂ) • g at hs
  change T.finiteRepresentation
    (FiniteAdelicGL.localInclusion F n v (Matrix.GeneralLinearGroup.scalar (Fin n) a)) (e g) =
      (ω.finiteComponent v a : ℂ) • e g
  exact (Intertwiner.finite e.toIntertwiningMap
    (FiniteAdelicGL.localInclusion F n v (Matrix.GeneralLinearGroup.scalar (Fin n) a))
    g).symm.trans ((congrArg e hs).trans
      (e.toLinearEquiv.map_smul (ω.finiteComponent v a : ℂ) g))

/-- Conjugate a full operator equivalence by the same actual determinant multiplier. -/
def Equivalence.heckeDeterminantTwist (e : S.Equivalence T) (χ : HeckeCharacter F) :
    (S.heckeDeterminantTwist χ).Equivalence (T.heckeDeterminantTwist χ) :=
  equivalenceOfCommonConjugation S.representation T.representation
    (S.heckeDeterminantTwist χ).representation (T.heckeDeterminantTwist χ).representation
    (heckeDeterminantOperatorConjugation n χ)
    (S.heckeDeterminantTwistEquiv χ).toLinearEquiv
    (T.heckeDeterminantTwistEquiv χ).toLinearEquiv
    (S.heckeDeterminantTwistEquiv_operatorAction χ)
    (T.heckeDeterminantTwistEquiv_operatorAction χ) e

/-- Equality of the multiplied actual subspaces reflects equality before twisting. -/
theorem heckeDeterminantTwist_injective (χ : HeckeCharacter F) :
    Function.Injective (fun S : OperatorRealization F n => S.heckeDeterminantTwist χ) := by
  intro S T h
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.map_injective_of_injective
    (StableAutomorphicFunctions.heckeDeterminantMultiplier n χ).injective
    (congrArg Subrepresentation.toSubmodule h)

end OperatorRealization

/-- The exact multiplicity-one conclusion restricted to actual cuspidal realizations
whose central characters are unitary. This proposition is retained as an open premise. -/
def CuspidalOperatorUnitaryMultiplicityOneStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T T' : CuspidalOperatorRealization F r),
    Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
    Langlands.ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T' →
    Nonempty (T.Equivalence T') → T.realization = T'.realization

/-- Reducing to the unitary-central-character case adds no hypothesis to the consequent. -/
def CuspidalOperatorUnitaryMultiplicityOneReductionStatement : Prop :=
  CuspidalOperatorUnitaryMultiplicityOneStatement.{u} →
    CuspidalOperatorMultiplicityOneStatement.{u}

/-- Use a common central character, a common unitarizing actual twist, and injectivity
of its ambient multiplier to reduce the exact target to the named unitary case. -/
theorem cuspidalOperatorUnitaryMultiplicityOneReduction :
    CuspidalOperatorUnitaryMultiplicityOneReductionStatement.{u} := by
  intro hunit F _ _ _ r T T' ⟨e⟩
  obtain ⟨ω, hω, -⟩ :=
    OperatorRealization.existsUnique_hasCentralCharacter T.realization T.irreducible
  have hω' : T'.HasCentralCharacter ω :=
    OperatorRealization.Equivalence.hasCentralCharacter e hω
  have ht := hunit F r
    (T.heckeDeterminantTwist (unitarizingCharacter r ω))
    (T'.heckeDeterminantTwist (unitarizingCharacter r ω))
    (hasUnitaryCentralCharacter_heckeDeterminantTwist_unitarizingCharacter T hω)
    (hasUnitaryCentralCharacter_heckeDeterminantTwist_unitarizingCharacter T' hω')
    ⟨OperatorRealization.Equivalence.heckeDeterminantTwist e (unitarizingCharacter r ω)⟩
  exact OperatorRealization.heckeDeterminantTwist_injective (unitarizingCharacter r ω) ht

end Langlands.Automorphic
