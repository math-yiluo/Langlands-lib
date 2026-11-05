import Langlands.Representation.Plancherel.UnramifiedUniversalTwist
import Langlands.Representation.Aubert.General.Parabolic

/-! Normalized full induction and actual Jacquet quotients over the concrete
unramified regular algebra. No finiteness or base-change isomorphism is asserted. -/

noncomputable section

open CategoryTheory
open scoped NNReal TensorProduct

namespace Langlands.Plancherel.UnramifiedNormalized

universe uL uI uG uV

variable {L : Type uL} [Group L] [TopologicalSpace L]
  {I : Type uI} (ν : I → (L →* ℝ≥0ˣ))

/-- Specialization of the concrete regular algebra at an actual parameter. -/
def evaluation (χ : unramifiedCharacters ν) : unramifiedRegularFunctions ν →+* ℂ where
  toFun b := b.val χ
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem evaluation_apply (χ : unramifiedCharacters ν)
    (b : unramifiedRegularFunctions ν) : evaluation ν χ b = b.val χ := rfl

@[simp] theorem evaluation_algebraMap (χ : unramifiedCharacters ν) (c : ℂ) :
    evaluation ν χ (algebraMap ℂ (unramifiedRegularFunctions ν) c) = c := rfl

/-- The constant image of a complex unit-valued character. -/
def constantCharacter {H : Type*} [Group H] (η : H →* ℂˣ) :
    H →* (unramifiedRegularFunctions ν)ˣ :=
  (Units.map (algebraMap ℂ (unramifiedRegularFunctions ν)).toMonoidHom).comp η

@[simp] theorem constantCharacter_val {H : Type*} [Group H]
    (η : H →* ℂˣ) (g : H) :
    (constantCharacter ν η g : unramifiedRegularFunctions ν) =
      algebraMap ℂ (unramifiedRegularFunctions ν) (η g : ℂ) := rfl

@[simp] theorem evaluation_constantCharacter {H : Type*} [Group H]
    (η : H →* ℂˣ) (g : H) (χ : unramifiedCharacters ν) :
    evaluation ν χ (constantCharacter ν η g : unramifiedRegularFunctions ν) =
      (η g : ℂ) := rfl

/-- The constant map preserves the exact kernel, not just its openness. -/
theorem constantCharacter_ker {H : Type*} [Group H] (η : H →* ℂˣ) :
    (constantCharacter ν η).ker = η.ker := by
  ext g
  constructor
  · intro hg
    apply Units.ext
    have hv := congrArg (fun z : (unramifiedRegularFunctions ν)ˣ =>
      evaluation ν (1 : unramifiedCharacters ν) (z : unramifiedRegularFunctions ν)) hg
    exact hv
  · intro hg
    change constantCharacter ν η g = 1
    change η g = 1 at hg
    simp [constantCharacter, hg]

/-- Constant extension of an open-kernel character remains smooth. -/
def constantSmoothCharacter {H : Type*} [Group H] [TopologicalSpace H]
    (η : H →* ℂˣ) (hη : IsOpen (η.ker : Set H)) :
    Induction.SmoothCharacter (unramifiedRegularFunctions ν) H where
  toMonoidHom := constantCharacter ν η
  isOpen_ker := by rw [constantCharacter_ker]; exact hη

section Parabolic

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}

/-- Positive half-modulus on the full parabolic, with constant B coefficients. -/
def inductionCharacter (U P : Subgroup G) (hU : IsClosed (U : Set G))
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) :
    Induction.SmoothCharacter (unramifiedRegularFunctions ν) P :=
  constantSmoothCharacter ν (HaarModulus.closedHalfCharacter U hU P hPU)
    (HaarModulus.isOpen_ker_closedHalfCharacter U hU P hPU)

/-- Inverse Levi half-modulus, with constant B coefficients. -/
def jacquetCharacter (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) :
    Induction.SmoothCharacter (unramifiedRegularFunctions ν) M :=
  constantSmoothCharacter ν (HaarModulus.closedInverseHalfCharacter U hU M hMU)
    (HaarModulus.isOpen_ker_closedInverseHalfCharacter U hU M hMU)

/-- Actual inflation and full-parabolic positive normalization over B. -/
abbrev inducingRepresentation (h : Aubert.General.IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) {V : Type uV} [AddCommGroup V]
    [Module (unramifiedRegularFunctions ν) V]
    (σ : Representation (unramifiedRegularFunctions ν) M V) :=
  Langlands.twist (inductionCharacter ν U P hU h.le_normalizer).toMonoidHom
    (σ.comp h.projection)

/-- Full smooth normalized induction, on actual functions with a uniform right stabilizer. -/
abbrev Induced (h : Aubert.General.IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) {V : Type uV} [AddCommGroup V]
    [Module (unramifiedRegularFunctions ν) V]
    (σ : Representation (unramifiedRegularFunctions ν) M V) :=
  Induction.SmoothFunctions P (inducingRepresentation ν h hU σ)

/-- Right translation on the full normalized induced model. -/
def inducedRepresentation (h : Aubert.General.IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) {V : Type uV} [AddCommGroup V]
    [Module (unramifiedRegularFunctions ν) V]
    (σ : Representation (unramifiedRegularFunctions ν) M V) :
    Representation (unramifiedRegularFunctions ν) G (Induced ν h hU σ) :=
  Induction.smoothInduced P (inducingRepresentation ν h hU σ)

/-- B-normalized induction as a functor, using the actual Levi projection. -/
def normalizedInductionFunctor (h : Aubert.General.IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) :
    SmoothRep.{_, uG, uV} (unramifiedRegularFunctions ν) M ⥤
      SmoothRep.{_, uG, max uG uV} (unramifiedRegularFunctions ν) G :=
  SmoothRep.toRep ⋙ Rep.resFunctor h.projection ⋙
    Induction.normalizedSmoothInductionFunctor P
      (inductionCharacter ν U P hU h.le_normalizer)

/-- The exact character-relation quotient with character one. -/
abbrev Jacquet {V : Type uV} [AddCommGroup V] [Module (unramifiedRegularFunctions ν) V]
    (ρ : Representation (unramifiedRegularFunctions ν) G V) (U : Subgroup G) :=
  Langlands.Jacquet.Localization.Coinvariants ρ U 1

/-- Inverse-half normalized action on the actual relation quotient. -/
def jacquetRepresentation {V : Type uV} [AddCommGroup V]
    [Module (unramifiedRegularFunctions ν) V]
    (ρ : Representation (unramifiedRegularFunctions ν) G V)
    (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) :
    Representation (unramifiedRegularFunctions ν) M (Jacquet ν ρ U) :=
  Langlands.twist (jacquetCharacter ν U M hU hMU).toMonoidHom
    (Langlands.Jacquet.Localization.action ρ U 1 M hMU
      (Langlands.Jacquet.Localization.isInvariant_one U M hMU))

/-- Normalized Jacquet on B-smooth representations, with its intrinsic functor laws. -/
def normalizedJacquetFunctor (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) :
    SmoothRep.{_, uG, uV} (unramifiedRegularFunctions ν) G ⥤
      SmoothRep.{_, uG, uV} (unramifiedRegularFunctions ν) M :=
  Langlands.Jacquet.Localization.smoothFunctor U 1 M hMU
      (Langlands.Jacquet.Localization.isInvariant_one U M hMU) ⋙
    SmoothRep.twistFunctor (jacquetCharacter ν U M hU hMU).toMonoidHom
      (jacquetCharacter ν U M hU hMU).isOpen_ker

section Laws

variable (h : Aubert.General.IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) {V : Type uV} [AddCommGroup V]
  [Module (unramifiedRegularFunctions ν) V]

/-- The full P covariance on the actual underlying function. -/
theorem induced_covariant (σ : Representation (unramifiedRegularFunctions ν) M V)
    (f : Induced ν h hU σ) (p : P) (g : G) :
    Induction.eval P (inducingRepresentation ν h hU σ) f ((p : G) * g) =
      (inductionCharacter ν U P hU h.le_normalizer).toMonoidHom p •
        σ (h.projection p) (Induction.eval P (inducingRepresentation ν h hU σ) f g) :=
  f.1.2 p g

@[simp] theorem induced_action (σ : Representation (unramifiedRegularFunctions ν) M V)
    (f : Induced ν h hU σ) (g x : G) :
    Induction.eval P (inducingRepresentation ν h hU σ)
      (inducedRepresentation ν h hU σ g f) x =
        Induction.eval P (inducingRepresentation ν h hU σ) f (x * g) := rfl

theorem isSmooth_inducedRepresentation
    (σ : Representation (unramifiedRegularFunctions ν) M V) :
    IsSmooth (inducedRepresentation ν h hU σ) :=
  Induction.smoothInduced_smooth _ _

@[simp] theorem jacquet_action_mk (ρ : Representation (unramifiedRegularFunctions ν) G V)
    (m : M) (v : V) :
    jacquetRepresentation ν ρ U M hU h.levi_le_normalizer m
      (Langlands.Jacquet.Localization.mk ρ U 1 v) =
        (jacquetCharacter ν U M hU h.levi_le_normalizer).toMonoidHom m •
          Langlands.Jacquet.Localization.mk ρ U 1 (ρ m v) := rfl

theorem isSmooth_jacquetRepresentation
    (ρ : Representation (unramifiedRegularFunctions ν) G V) (hρ : IsSmooth ρ) :
    IsSmooth (jacquetRepresentation ν ρ U M hU h.levi_le_normalizer) :=
  (isSmooth_twist_iff _ _ (jacquetCharacter ν U M hU h.levi_le_normalizer).isOpen_ker).mpr
    (Langlands.Jacquet.Localization.isSmooth_action ρ U 1 M h.levi_le_normalizer
      (Langlands.Jacquet.Localization.isInvariant_one U M h.levi_le_normalizer) hρ)

end Laws
end Parabolic
end Langlands.Plancherel.UnramifiedNormalized
