import Langlands.Weil.Representation.TwistProperties
import Langlands.Weil.Representation.Predicates
import Langlands.Weil.Representation.OperationClosureProof
import Langlands.Representation.Twist.AlgebraProof
import Langlands.Weil.Local.DegreeCharacters
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Topology.Algebra.Group.Units

/-! # Character-twist equivalences on genuine representation classes -/

noncomputable section

universe uK uG uV

namespace Langlands.FiniteRepresentation

section Algebraic

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

@[simp]
theorem twistClass_classOf (χ : G →* Kˣ)
    (A : FiniteRepresentation.{uK, uG, uV} K G) :
    twistClass χ (classOf A) = classOf (twist χ A) := rfl

@[simp]
theorem classRank_twistClass (χ : G →* Kˣ)
    (c : IsomorphismClasses.{uK, uG, uV} K G) :
    classRank (twistClass χ c) = classRank c := by
  refine Quotient.inductionOn c ?_
  intro A
  rfl

@[simp]
theorem twistClass_one (c : IsomorphismClasses.{uK, uG, uV} K G) :
    twistClass 1 c = c := by
  refine Quotient.inductionOn c ?_
  intro A
  exact Quotient.sound ⟨twistOneEquiv A⟩

theorem twistClass_twistClass (χ η : G →* Kˣ)
    (c : IsomorphismClasses.{uK, uG, uV} K G) :
    twistClass χ (twistClass η c) = twistClass (χ * η) c := by
  refine Quotient.inductionOn c ?_
  intro A
  exact Quotient.sound ⟨twistMulEquiv χ η A⟩

@[simp]
theorem twistClass_inv_twistClass (χ : G →* Kˣ)
    (c : IsomorphismClasses.{uK, uG, uV} K G) :
    twistClass χ⁻¹ (twistClass χ c) = c := by
  have hχ : χ⁻¹ * χ = 1 := by ext g; simp
  rw [twistClass_twistClass, hχ, twistClass_one]

@[simp]
theorem twistClass_twistClass_inv (χ : G →* Kˣ)
    (c : IsomorphismClasses.{uK, uG, uV} K G) :
    twistClass χ (twistClass χ⁻¹ c) = c := by
  have hχ : χ * χ⁻¹ = 1 := by ext g; simp
  rw [twistClass_twistClass, hχ, twistClass_one]

/-- Character twisting acts invertibly on the existing genuine class quotient. -/
def twistClassEquiv (χ : G →* Kˣ) :
    IsomorphismClasses.{uK, uG, uV} K G ≃ IsomorphismClasses.{uK, uG, uV} K G where
  toFun := twistClass χ
  invFun := twistClass χ⁻¹
  left_inv := twistClass_inv_twistClass χ
  right_inv := twistClass_twistClass_inv χ

@[simp]
theorem twistClassEquiv_apply (χ : G →* Kˣ)
    (c : IsomorphismClasses.{uK, uG, uV} K G) :
    twistClassEquiv χ c = twistClass χ c := rfl

@[simp]
theorem twistClassEquiv_classOf (χ : G →* Kˣ)
    (A : FiniteRepresentation.{uK, uG, uV} K G) :
    twistClassEquiv χ (classOf A) = classOf (twist χ A) := rfl

@[simp]
theorem classRank_twistClassEquiv (χ : G →* Kˣ)
    (c : IsomorphismClasses.{uK, uG, uV} K G) :
    classRank (twistClassEquiv χ c) = classRank c :=
  classRank_twistClass χ c

@[simp]
theorem twistClassEquiv_one :
    twistClassEquiv (1 : G →* Kˣ) =
      _root_.Equiv.refl (IsomorphismClasses.{uK, uG, uV} K G) := by
  apply _root_.Equiv.ext
  exact twistClass_one

theorem twistClassEquiv_mul (χ η : G →* Kˣ) :
    (twistClassEquiv.{uK, uG, uV} η).trans (twistClassEquiv χ) =
      twistClassEquiv (χ * η) := by
  apply _root_.Equiv.ext
  exact twistClass_twistClass χ η

@[simp]
theorem twistClassEquiv_symm (χ : G →* Kˣ) :
    (twistClassEquiv.{uK, uG, uV} χ).symm = twistClassEquiv χ⁻¹ := by
  apply _root_.Equiv.ext
  intro c
  rfl

/-- Forgetting a property is injective because the equivalence relation is unchanged. -/
theorem forgetPropertyClass_injective
    (P : FiniteRepresentation.{uK, uG, uV} K G → Prop) :
    Function.Injective (forgetPropertyClass P) := by
  intro c d
  refine Quotient.inductionOn₂ c d ?_
  intro A B h
  exact Quotient.sound ((classOf_eq_iff A.val B.val).mp h)

end Algebraic

section ContinuousIrreducible

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Twist an object carrying the actual continuity and irreducibility certificates. -/
def continuousIrreducibleTwist (χ : G →ₜ* ℂˣ)
    (A : {A : FiniteRepresentation.{0, uG, uV} ℂ G //
      A.IsContinuous ∧ A.IsIrreducible}) :
    {A : FiniteRepresentation.{0, uG, uV} ℂ G //
      A.IsContinuous ∧ A.IsIrreducible} :=
  ⟨twist χ.toMonoidHom A.val, isContinuous_twist χ A.property.1,
    (Weil.OperationClosure.irreducible_twist_iff χ.toMonoidHom
      A.val.representation).mpr A.property.2⟩

/-- Descend the certified object construction through the existing property quotient. -/
def continuousIrreducibleTwistClass (χ : G →ₜ* ℂˣ) :
    IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous ∧ A.IsIrreducible) →
    IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous ∧ A.IsIrreducible) :=
  Quotient.map (continuousIrreducibleTwist χ)
    (fun _ _ ⟨e⟩ => ⟨twistEquiv χ.toMonoidHom e⟩)

@[simp]
theorem forget_continuousIrreducibleTwistClass (χ : G →ₜ* ℂˣ)
    (c : IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous ∧ A.IsIrreducible)) :
    forgetPropertyClass _ (continuousIrreducibleTwistClass χ c) =
      twistClass χ.toMonoidHom (forgetPropertyClass _ c) := by
  refine Quotient.inductionOn c ?_
  intro A
  rfl

@[simp]
theorem continuousIrreducibleTwistClass_one
    (c : IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous ∧ A.IsIrreducible)) :
    continuousIrreducibleTwistClass 1 c = c := by
  apply forgetPropertyClass_injective _
  rw [forget_continuousIrreducibleTwistClass]
  exact twistClass_one _

theorem continuousIrreducibleTwistClass_mul (χ η : G →ₜ* ℂˣ)
    (c : IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous ∧ A.IsIrreducible)) :
    continuousIrreducibleTwistClass χ (continuousIrreducibleTwistClass η c) =
      continuousIrreducibleTwistClass (χ * η) c := by
  apply forgetPropertyClass_injective _
  simp only [forget_continuousIrreducibleTwistClass, twistClass_twistClass]
  rfl

@[simp]
theorem continuousIrreducibleTwistClass_inv (χ : G →ₜ* ℂˣ)
    (c : IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous ∧ A.IsIrreducible)) :
    continuousIrreducibleTwistClass χ⁻¹ (continuousIrreducibleTwistClass χ c) = c := by
  rw [continuousIrreducibleTwistClass_mul, inv_mul_cancel,
    continuousIrreducibleTwistClass_one]

@[simp]
theorem continuousIrreducibleTwistClass_inv' (χ : G →ₜ* ℂˣ)
    (c : IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uV} ℂ G =>
      A.IsContinuous ∧ A.IsIrreducible)) :
    continuousIrreducibleTwistClass χ (continuousIrreducibleTwistClass χ⁻¹ c) = c := by
  rw [continuousIrreducibleTwistClass_mul, mul_inv_cancel,
    continuousIrreducibleTwistClass_one]

/-- Rank-preserving twisting on the existing continuous irreducible classes. -/
def continuousIrreducibleTwistEquiv (χ : G →ₜ* ℂˣ) (n : ℕ) :
    ContinuousIrreducibleClasses.{uG, uV} G n ≃
      ContinuousIrreducibleClasses.{uG, uV} G n where
  toFun c := ⟨continuousIrreducibleTwistClass χ c.val, by
    simpa using c.property⟩
  invFun c := ⟨continuousIrreducibleTwistClass χ⁻¹ c.val, by
    simpa using c.property⟩
  left_inv c := Subtype.ext (continuousIrreducibleTwistClass_inv χ c.val)
  right_inv c := Subtype.ext (continuousIrreducibleTwistClass_inv' χ c.val)

/-- The rank-indexed action descends the certified twist of each representative. -/
theorem continuousIrreducibleTwistEquiv_mk (χ : G →ₜ* ℂˣ) (n : ℕ)
    (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (hA : A.IsContinuous ∧ A.IsIrreducible) (hn : A.rank = n) :
    continuousIrreducibleTwistEquiv χ n ⟨Quotient.mk _ ⟨A, hA⟩, hn⟩ =
      ⟨Quotient.mk _ (continuousIrreducibleTwist χ ⟨A, hA⟩), hn⟩ := rfl

@[simp]
theorem forget_continuousIrreducibleTwistEquiv (χ : G →ₜ* ℂˣ) (n : ℕ)
    (c : ContinuousIrreducibleClasses.{uG, uV} G n) :
    forgetPropertyClass _ (continuousIrreducibleTwistEquiv χ n c).val =
      twistClass χ.toMonoidHom (forgetPropertyClass _ c.val) :=
  forget_continuousIrreducibleTwistClass χ c.val

@[simp]
theorem continuousIrreducibleTwistEquiv_one (n : ℕ) :
    continuousIrreducibleTwistEquiv (1 : G →ₜ* ℂˣ) n =
      _root_.Equiv.refl (ContinuousIrreducibleClasses.{uG, uV} G n) := by
  apply _root_.Equiv.ext
  intro c
  exact Subtype.ext (continuousIrreducibleTwistClass_one c.val)

theorem continuousIrreducibleTwistEquiv_mul (χ η : G →ₜ* ℂˣ) (n : ℕ) :
    (continuousIrreducibleTwistEquiv.{uG, uV} η n).trans
      (continuousIrreducibleTwistEquiv χ n) =
      continuousIrreducibleTwistEquiv (χ * η) n := by
  apply _root_.Equiv.ext
  intro c
  exact Subtype.ext (continuousIrreducibleTwistClass_mul χ η c.val)

@[simp]
theorem continuousIrreducibleTwistEquiv_symm (χ : G →ₜ* ℂˣ) (n : ℕ) :
    (continuousIrreducibleTwistEquiv.{uG, uV} χ n).symm =
      continuousIrreducibleTwistEquiv χ⁻¹ n := by
  apply _root_.Equiv.ext
  intro c
  rfl

@[simp]
theorem continuousIrreducibleTwistEquiv_inv_apply (χ : G →ₜ* ℂˣ) (n : ℕ)
    (c : ContinuousIrreducibleClasses.{uG, uV} G n) :
    continuousIrreducibleTwistEquiv χ⁻¹ n (continuousIrreducibleTwistEquiv χ n c) = c :=
  (continuousIrreducibleTwistEquiv χ n).symm_apply_apply c

@[simp]
theorem continuousIrreducibleTwistEquiv_apply_inv (χ : G →ₜ* ℂˣ) (n : ℕ)
    (c : ContinuousIrreducibleClasses.{uG, uV} G n) :
    continuousIrreducibleTwistEquiv χ n (continuousIrreducibleTwistEquiv χ⁻¹ n c) = c :=
  (continuousIrreducibleTwistEquiv χ n).apply_symm_apply c

/-- Specialize to any complex value at degree one, without a unitarity restriction. -/
def continuousIrreducibleUnramifiedTwistEquiv (d : G →ₜ* Weil.Degree)
    (z : ℂˣ) (n : ℕ) :
    ContinuousIrreducibleClasses.{uG, uV} G n ≃
      ContinuousIrreducibleClasses.{uG, uV} G n :=
  continuousIrreducibleTwistEquiv (Weil.Local.unramifiedCharacter d z) n

@[simp]
theorem forget_continuousIrreducibleUnramifiedTwistEquiv
    (d : G →ₜ* Weil.Degree) (z : ℂˣ) (n : ℕ)
    (c : ContinuousIrreducibleClasses.{uG, uV} G n) :
    forgetPropertyClass _ (continuousIrreducibleUnramifiedTwistEquiv d z n c).val =
      twistClass (Weil.Local.unramifiedCharacter d z).toMonoidHom
        (forgetPropertyClass _ c.val) :=
  forget_continuousIrreducibleTwistEquiv _ n c

@[simp]
theorem continuousIrreducibleUnramifiedTwistEquiv_one
    (d : G →ₜ* Weil.Degree) (n : ℕ) :
    continuousIrreducibleUnramifiedTwistEquiv.{uG, uV} d 1 n =
      _root_.Equiv.refl (ContinuousIrreducibleClasses.{uG, uV} G n) := by
  change continuousIrreducibleTwistEquiv (Weil.Local.unramifiedCharacterHom d 1) n = _
  rw [map_one, continuousIrreducibleTwistEquiv_one]

theorem continuousIrreducibleUnramifiedTwistEquiv_mul
    (d : G →ₜ* Weil.Degree) (z w : ℂˣ) (n : ℕ) :
    (continuousIrreducibleUnramifiedTwistEquiv.{uG, uV} d w n).trans
      (continuousIrreducibleUnramifiedTwistEquiv d z n) =
      continuousIrreducibleUnramifiedTwistEquiv d (z * w) n := by
  change (continuousIrreducibleTwistEquiv (Weil.Local.unramifiedCharacterHom d w) n).trans
    (continuousIrreducibleTwistEquiv (Weil.Local.unramifiedCharacterHom d z) n) =
    continuousIrreducibleTwistEquiv (Weil.Local.unramifiedCharacterHom d (z * w)) n
  rw [map_mul, continuousIrreducibleTwistEquiv_mul]

@[simp]
theorem continuousIrreducibleUnramifiedTwistEquiv_symm
    (d : G →ₜ* Weil.Degree) (z : ℂˣ) (n : ℕ) :
    (continuousIrreducibleUnramifiedTwistEquiv.{uG, uV} d z n).symm =
      continuousIrreducibleUnramifiedTwistEquiv d z⁻¹ n := by
  change (continuousIrreducibleTwistEquiv (Weil.Local.unramifiedCharacterHom d z) n).symm =
    continuousIrreducibleTwistEquiv (Weil.Local.unramifiedCharacterHom d z⁻¹) n
  rw [map_inv, continuousIrreducibleTwistEquiv_symm]

@[simp]
theorem continuousIrreducibleUnramifiedTwistEquiv_inv_apply
    (d : G →ₜ* Weil.Degree) (z : ℂˣ) (n : ℕ)
    (c : ContinuousIrreducibleClasses.{uG, uV} G n) :
    continuousIrreducibleUnramifiedTwistEquiv d z⁻¹ n
      (continuousIrreducibleUnramifiedTwistEquiv d z n c) = c := by
  rw [← continuousIrreducibleUnramifiedTwistEquiv_symm]
  exact (continuousIrreducibleUnramifiedTwistEquiv d z n).symm_apply_apply c

@[simp]
theorem continuousIrreducibleUnramifiedTwistEquiv_apply_inv
    (d : G →ₜ* Weil.Degree) (z : ℂˣ) (n : ℕ)
    (c : ContinuousIrreducibleClasses.{uG, uV} G n) :
    continuousIrreducibleUnramifiedTwistEquiv d z n
      (continuousIrreducibleUnramifiedTwistEquiv d z⁻¹ n c) = c := by
  rw [← continuousIrreducibleUnramifiedTwistEquiv_symm]
  exact (continuousIrreducibleUnramifiedTwistEquiv d z n).apply_symm_apply c

end ContinuousIrreducible

end Langlands.FiniteRepresentation
