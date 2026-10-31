import Langlands.Automorphic.OperatorDeterminantTwist

/-! # Total determinant twisting on full automorphic isomorphism classes -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.HeckeCharacter

/-- The actual subgroup of finite-order continuous Hecke characters. -/
def finiteOrderSubgroup (F : Type u) [Field F] [NumberField F] :
    Subgroup (HeckeCharacter F) where
  carrier := {χ | χ.HasFiniteOrder}
  one_mem' := hasFiniteOrder_one
  mul_mem' := HasFiniteOrder.mul
  inv_mem' := HasFiniteOrder.inv

end Langlands.Global.HeckeCharacter

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance twistClassesRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance twistClassesContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance twistClassesFiniteSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance twistClassesFormGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance twistClassesStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance twistClassesSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

/-- Changing the original full realization by a full equivalence changes no twisted class. -/
theorem determinantTwist_congr
    {S T : OperatorRealization F n} (hST : Nonempty (S.Equivalence T))
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    Nonempty ((S.determinantTwist χ hχ).Equivalence (T.determinantTwist χ hχ)) := by
  have h : IsFiniteOrderDeterminantTwist χ T (S.determinantTwist χ hχ) :=
    (isFiniteOrderDeterminantTwist_congr hST
      ⟨Representation.Equiv.refl (S.determinantTwist χ hχ).representation⟩).mp
        (S.isFiniteOrderDeterminantTwist χ hχ)
  exact h.target_equivalent (T.isFiniteOrderDeterminantTwist χ hχ)

namespace IsoClass

/-- Descent of the actual image construction to the existing full-operator quotient. -/
def determinantTwist (c : IsoClass F n) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    IsoClass F n :=
  Quotient.lift (s := equivalenceSetoid F n)
    (fun S => (S.determinantTwist χ hχ).isoClass)
    (fun S T hST => ((S.determinantTwist χ hχ).isoClass_eq_iff
      (T.determinantTwist χ hχ)).mpr (determinantTwist_congr hST χ hχ)) c

@[simp]
theorem determinantTwist_isoClass (S : OperatorRealization F n)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantTwist S.isoClass χ hχ = (S.determinantTwist χ hχ).isoClass := rfl

@[simp]
theorem determinantTwist_one (c : IsoClass F n) :
    determinantTwist c 1 HeckeCharacter.hasFiniteOrder_one = c := by
  refine Quotient.inductionOn c ?_
  intro S
  obtain ⟨e⟩ := isFiniteOrderDeterminantTwist_one_iff.mp
    (S.isFiniteOrderDeterminantTwist 1 HeckeCharacter.hasFiniteOrder_one)
  exact ((S.determinantTwist 1 HeckeCharacter.hasFiniteOrder_one).isoClass_eq_iff S).mpr
    ⟨e.symm⟩

theorem determinantTwist_mul (c : IsoClass F n)
    (χ ψ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (hψ : ψ.HasFiniteOrder) :
    determinantTwist (determinantTwist c χ hχ) ψ hψ =
      determinantTwist c (χ * ψ) (hχ.mul hψ) := by
  refine Quotient.inductionOn c ?_
  intro S
  exact (((S.determinantTwist χ hχ).determinantTwist ψ hψ).isoClass_eq_iff
    (S.determinantTwist (χ * ψ) (hχ.mul hψ))).mpr
      (((S.isFiniteOrderDeterminantTwist χ hχ).trans
        ((S.determinantTwist χ hχ).isFiniteOrderDeterminantTwist ψ hψ)).target_equivalent
          (S.isFiniteOrderDeterminantTwist (χ * ψ) (hχ.mul hψ)))

@[simp]
theorem determinantTwist_inv (c : IsoClass F n)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantTwist (determinantTwist c χ hχ) χ⁻¹ hχ.inv = c := by
  simpa only [mul_inv_cancel, determinantTwist_one] using
    determinantTwist_mul c χ χ⁻¹ hχ hχ.inv

/-- The actual finite-order character group acts on the existing full classes. -/
instance finiteOrderCharacterMulAction :
    MulAction (HeckeCharacter.finiteOrderSubgroup F) (IsoClass F n) where
  smul χ c := determinantTwist c χ.val χ.property
  one_smul := determinantTwist_one
  mul_smul χ ψ c := by
    change determinantTwist c (χ.val * ψ.val) (χ.property.mul ψ.property) =
      determinantTwist (determinantTwist c ψ.val ψ.property) χ.val χ.property
    exact (congrArg (fun η : HeckeCharacter.finiteOrderSubgroup F =>
      determinantTwist c η.val η.property) (mul_comm χ ψ)).trans
        (determinantTwist_mul c ψ.val χ.val ψ.property χ.property).symm

end IsoClass
end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

namespace IsoClass

/-- Descent of actual irreducible cuspidal image twists with no chosen representative. -/
def determinantTwist (c : IsoClass F r) (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    IsoClass F r :=
  Quotient.lift (s := equivalenceSetoid F r)
    (fun S => (S.determinantTwist χ hχ).isoClass)
    (fun S T hST => ((S.determinantTwist χ hχ).isoClass_eq_iff
      (T.determinantTwist χ hχ)).mpr (OperatorRealization.determinantTwist_congr hST χ hχ)) c

@[simp]
theorem determinantTwist_isoClass (S : CuspidalOperatorRealization F r)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantTwist S.isoClass χ hχ = (S.determinantTwist χ hχ).isoClass := rfl

@[simp]
theorem toOperatorClass_determinantTwist (c : IsoClass F r)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (determinantTwist c χ hχ).toOperatorClass = c.toOperatorClass.determinantTwist χ hχ := by
  refine Quotient.inductionOn c ?_
  intro S
  rfl

/-- Every class now has the actual target whose relation was previously only specified. -/
theorem isFiniteOrderDeterminantTwist_determinantTwist (c : IsoClass F r)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    IsFiniteOrderDeterminantTwist χ c (determinantTwist c χ hχ) := by
  refine Quotient.inductionOn c ?_
  intro S
  exact S.determinantTwist_isFiniteOrderDeterminantTwist χ hχ

/-- The old relation is characterized by equality with the constructed total twist. -/
theorem isFiniteOrderDeterminantTwist_iff_eq (c d : IsoClass F r)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    IsFiniteOrderDeterminantTwist χ c d ↔ d = determinantTwist c χ hχ := by
  constructor
  · intro h
    exact h.target_unique (isFiniteOrderDeterminantTwist_determinantTwist c χ hχ)
  · rintro rfl
    exact isFiniteOrderDeterminantTwist_determinantTwist c χ hχ

@[simp]
theorem determinantTwist_one (c : IsoClass F r) :
    determinantTwist c 1 HeckeCharacter.hasFiniteOrder_one = c := by
  apply toOperatorClass_injective
  rw [toOperatorClass_determinantTwist, OperatorRealization.IsoClass.determinantTwist_one]

theorem determinantTwist_mul (c : IsoClass F r)
    (χ ψ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (hψ : ψ.HasFiniteOrder) :
    determinantTwist (determinantTwist c χ hχ) ψ hψ =
      determinantTwist c (χ * ψ) (hχ.mul hψ) := by
  apply toOperatorClass_injective
  simp only [toOperatorClass_determinantTwist,
    OperatorRealization.IsoClass.determinantTwist_mul]

@[simp]
theorem determinantTwist_inv (c : IsoClass F r)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantTwist (determinantTwist c χ hχ) χ⁻¹ hχ.inv = c := by
  simpa only [mul_inv_cancel, determinantTwist_one] using
    determinantTwist_mul c χ χ⁻¹ hχ hχ.inv

/-- Finite-order Hecke characters act on full positive-rank cuspidal classes. -/
instance finiteOrderCharacterMulAction :
    MulAction (HeckeCharacter.finiteOrderSubgroup F) (IsoClass F r) where
  smul χ c := determinantTwist c χ.val χ.property
  one_smul := determinantTwist_one
  mul_smul χ ψ c := by
    change determinantTwist c (χ.val * ψ.val) (χ.property.mul ψ.property) =
      determinantTwist (determinantTwist c ψ.val ψ.property) χ.val χ.property
    exact (congrArg (fun η : HeckeCharacter.finiteOrderSubgroup F =>
      determinantTwist c η.val η.property) (mul_comm χ ψ)).trans
        (determinantTwist_mul c ψ.val χ.val ψ.property χ.property).symm

end IsoClass
end CuspidalOperatorRealization

namespace PositiveRankCuspidalClass

variable [CompactSpace (AdeleQuotient F)]

/-- Mixed positive ranks retain their rank index under actual determinant twisting. -/
def determinantTwist (c : PositiveRankCuspidalClass F)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) : PositiveRankCuspidalClass F :=
  ⟨c.1, c.2.determinantTwist χ hχ⟩

@[simp]
theorem rankIndex_determinantTwist (c : PositiveRankCuspidalClass F)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (determinantTwist c χ hχ).rankIndex = c.rankIndex := rfl

@[simp]
theorem rank_determinantTwist (c : PositiveRankCuspidalClass F)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    (determinantTwist c χ hχ).rank = c.rank := rfl

@[simp]
theorem determinantTwist_ofFixedRank {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass F r)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) :
    determinantTwist (ofFixedRank c) χ hχ = ofFixedRank (c.determinantTwist χ hχ) := rfl

instance finiteOrderCharacterMulAction :
    MulAction (HeckeCharacter.finiteOrderSubgroup F) (PositiveRankCuspidalClass F) where
  smul χ c := determinantTwist c χ.val χ.property
  one_smul c := by
    obtain ⟨r, c⟩ := c
    change Sigma.mk r (c.determinantTwist 1 HeckeCharacter.hasFiniteOrder_one) = Sigma.mk r c
    rw [CuspidalOperatorRealization.IsoClass.determinantTwist_one]
  mul_smul χ ψ c := by
    obtain ⟨r, c⟩ := c
    change Sigma.mk r ((χ * ψ) • c) = Sigma.mk r (χ • (ψ • c))
    rw [mul_smul]

end PositiveRankCuspidalClass
end Langlands.Automorphic
