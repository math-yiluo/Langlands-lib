import Langlands.Automorphic.Contragredient
import Langlands.Global.ArchimedeanTransposeCompact

/-! # The full-operator transpose contragredient pairing condition -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open NumberField IsDedekindDomain Langlands.Global Langlands.GeneralLinear

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance transposePairingRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance transposePairingContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance transposePairingSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance transposePairingFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance transposePairingStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

local instance transposePairingSpaceAddCommGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- A linear equivalence realizes the transpose twist of all three kinds of operators. -/
def IsTransposeIntertwining (S T : OperatorRealization F n)
    (e : S.Space ≃ₗ[ℂ] T.Space) : Prop :=
  (∀ (d : FiniteAdelicGL F n) (x : S.Space),
      e (S.finiteRepresentation
        (inverseTranspose n (FiniteAdeleRing (𝓞 F) F) d) x) =
        T.finiteRepresentation d (e x)) ∧
    (∀ (k : standardInfiniteCompact F n) (x : S.Space),
      e (S.compactRepresentation (ArchimedeanGL.compactTranspose F n k) x) =
        T.compactRepresentation k (e x)) ∧
    ∀ (X : ArchimedeanGL.RealLieAlgebra F n) (x : S.Space),
      e (S.lieAction (ArchimedeanGL.realLieIota F n X) x) =
        T.lieAction X (e x)

/-- A bilinear form invariant when its second variable has the transpose-twisted action. -/
def IsTransposeInvariantPairing (S : OperatorRealization F n)
    (B : S.Space →ₗ[ℂ] S.Space →ₗ[ℂ] ℂ) : Prop :=
  (∀ (d : FiniteAdelicGL F n) (y x : S.Space),
      B (S.finiteRepresentation d y)
        (S.finiteRepresentation
          (inverseTranspose n (FiniteAdeleRing (𝓞 F) F) d) x) =
        B y x) ∧
    (∀ (k : standardInfiniteCompact F n) (y x : S.Space),
      B (S.compactRepresentation k y)
        (S.compactRepresentation (ArchimedeanGL.compactTranspose F n k) x) = B y x) ∧
    ∀ (X : ArchimedeanGL.RealLieAlgebra F n) (y x : S.Space),
      B (S.lieAction X y) x +
        B y (S.lieAction (ArchimedeanGL.realLieIota F n X) x) = 0

/-- The transpose-invariant form identifies the original space with all of its smooth,
compact-finite contragredient functionals. -/
def IsTransposeContragredientPairing (S : OperatorRealization F n)
    (B : S.Space →ₗ[ℂ] S.Space →ₗ[ℂ] ℂ) : Prop :=
  S.IsTransposeInvariantPairing B ∧
    (∀ x : S.Space, S.IsContragredientFunctional (B.flip x)) ∧
    Function.Injective B.flip ∧
    ∀ l : Module.Dual ℂ S.Space, S.IsContragredientFunctional l → ∃ x, B.flip x = l

/-- The intrinsic full-operator Gelfand--Kazhdan pairing condition for a realization. -/
def HasTransposeContragredientPairing (S : OperatorRealization F n) : Prop :=
  ∃ B : S.Space →ₗ[ℂ] S.Space →ₗ[ℂ] ℂ, S.IsTransposeContragredientPairing B

variable {S T : OperatorRealization F n}

private theorem symm_covariance {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) {A : V → V} {A' : W → W}
    (h : ∀ x, e (A x) = A' (e x)) (x : W) :
    e.symm (A' x) = A (e.symm x) := by
  apply e.injective
  exact (e.apply_symm_apply (A' x)).trans
    ((congrArg A' (e.apply_symm_apply x)).symm.trans (h (e.symm x)).symm)

/-- A transpose-twisted realization is a contragredient whenever the intrinsic pairing
condition holds on the original realization. -/
theorem IsTransposeIntertwining.isContragredientOf
    {e : S.Space ≃ₗ[ℂ] T.Space} (he : S.IsTransposeIntertwining T e)
    (hS : S.HasTransposeContragredientPairing) : T.IsContragredientOf S := by
  obtain ⟨B, ⟨hd, hk, hX⟩, hB, hinj, hsurj⟩ := hS
  refine ⟨B.compl₂ e.symm.toLinearMap, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro d y x
    change B (S.finiteRepresentation d y) (e.symm (T.finiteRepresentation d x)) =
      B y (e.symm x)
    exact (congrArg (B (S.finiteRepresentation d y))
      (symm_covariance e (he.1 d) x)).trans (hd d y (e.symm x))
  · intro k y x
    change B (S.compactRepresentation k y) (e.symm (T.compactRepresentation k x)) =
      B y (e.symm x)
    exact (congrArg (B (S.compactRepresentation k y))
      (symm_covariance e (he.2.1 k) x)).trans (hk k y (e.symm x))
  · intro X y x
    change B (S.lieAction X y) (e.symm x) +
      B y (e.symm (T.lieAction X x)) = 0
    exact (congrArg (fun z => B (S.lieAction X y) (e.symm x) + B y z)
      (symm_covariance e (he.2.2 X) x)).trans (hX X y (e.symm x))
  · intro x
    exact hB (e.symm x)
  · intro x₁ x₂ h
    have h' : B.flip (e.symm x₁) = B.flip (e.symm x₂) := h
    exact e.symm.injective (hinj h')
  · intro l hl
    obtain ⟨x, hx⟩ := hsurj l hl
    refine ⟨e x, ?_⟩
    change B.flip (e.symm (e x)) = l
    exact (congrArg B.flip (e.symm_apply_apply x)).trans hx

/-- A contragredient pairing on a transpose-twisted realization gives the intrinsic
transpose pairing condition on the original realization. -/
theorem IsTransposeIntertwining.hasTransposeContragredientPairing
    {e : S.Space ≃ₗ[ℂ] T.Space} (he : S.IsTransposeIntertwining T e)
    (hT : T.IsContragredientOf S) : S.HasTransposeContragredientPairing := by
  obtain ⟨B, ⟨hd, hk, hX⟩, hB, hinj, hsurj⟩ := hT
  refine ⟨B.compl₂ e.toLinearMap, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro d y x
    change B (S.finiteRepresentation d y)
      (e (S.finiteRepresentation
        (inverseTranspose n (FiniteAdeleRing (𝓞 F) F) d) x)) =
      B y (e x)
    exact (congrArg (B (S.finiteRepresentation d y)) (he.1 d x)).trans (hd d y (e x))
  · intro k y x
    change B (S.compactRepresentation k y)
      (e (S.compactRepresentation (ArchimedeanGL.compactTranspose F n k) x)) = B y (e x)
    exact (congrArg (B (S.compactRepresentation k y)) (he.2.1 k x)).trans (hk k y (e x))
  · intro X y x
    change B (S.lieAction X y) (e x) +
      B y (e (S.lieAction (ArchimedeanGL.realLieIota F n X) x)) = 0
    exact (congrArg (fun z => B (S.lieAction X y) (e x) + B y z)
      (he.2.2 X x)).trans (hX X y (e x))
  · intro x
    exact hB (e x)
  · intro x₁ x₂ h
    have h' : B.flip (e x₁) = B.flip (e x₂) := h
    exact e.injective (hinj h')
  · intro l hl
    obtain ⟨x, hx⟩ := hsurj l hl
    refine ⟨e.symm x, ?_⟩
    change B.flip (e (e.symm x)) = l
    exact (congrArg B.flip (e.apply_symm_apply x)).trans hx

/-- For any actual realization of the transpose twist, B2 is exactly the intrinsic
pairing condition. This theorem does not assert that the condition holds. -/
theorem IsTransposeIntertwining.isContragredientOf_iff
    {e : S.Space ≃ₗ[ℂ] T.Space} (he : S.IsTransposeIntertwining T e) :
    T.IsContragredientOf S ↔ S.HasTransposeContragredientPairing :=
  ⟨he.hasTransposeContragredientPairing, he.isContragredientOf⟩

end OperatorRealization
end Langlands.Automorphic
