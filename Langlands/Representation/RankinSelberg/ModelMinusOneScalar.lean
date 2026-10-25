import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Representation.Whittaker.CoefficientCentralCharacterProof

/-! The actual minus-one scalar shared by all coefficient images. -/

noncomputable section

namespace Langlands.RankinSelberg

open Whittaker GeneralLinear

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {θ : upperUnipotent (n + 1) F →* ℂˣ}

/-- The actual negative identity matrix, regarded as a central element. -/
def minusOneCentral (n : ℕ) (F : Type uF) [Field F] :
    Subgroup.center (Langlands.GeneralLinear (n + 1) F) :=
  ⟨-1, Subgroup.mem_center_iff.mpr fun g => by
    apply Units.ext
    simp⟩

/-- Evaluate the common coefficient central character at the actual `-I`.
The choice is made before specifying any equivariant functional. -/
def modelMinusOneScalar
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsOfWhittakerType n θ σ) : ℂˣ :=
  (Classical.choose (coefficientCentralCharacter
    (Langlands.GeneralLinear (n + 1) F) (upperUnipotent (n + 1) F) θ V σ
      hσ.1.1 hσ.2.2)) (minusOneCentral n F)

/-- The chosen scalar acts on every coefficient image, including that of the
zero functional. -/
theorem hasModelMinusOneScalar_modelMinusOneScalar
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsOfWhittakerType n θ σ)
    (ℓ : functionals (upperUnipotent (n + 1) F) θ σ) :
    HasModelMinusOneScalar σ ℓ (modelMinusOneScalar σ hσ) := by
  intro f g
  exact (Classical.choose_spec (coefficientCentralCharacter
    (Langlands.GeneralLinear (n + 1) F) (upperUnipotent (n + 1) F) θ V σ
      hσ.1.1 hσ.2.2)).1.2 ℓ f (minusOneCentral n F) g

/-- One minus-one scalar works simultaneously for all equivariant functionals
of a representation of Whittaker type. -/
theorem exists_modelMinusOneScalar
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsOfWhittakerType n θ σ) :
    ∃ ζ : ℂˣ, ∀ ℓ : functionals (upperUnipotent (n + 1) F) θ σ,
      HasModelMinusOneScalar σ ℓ ζ :=
  ⟨modelMinusOneScalar σ hσ, hasModelMinusOneScalar_modelMinusOneScalar σ hσ⟩

/-- For a nonzero functional, the shared scalar is the unique scalar satisfying
the published model-action predicate. -/
theorem modelMinusOneScalar_eq
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsOfWhittakerType n θ σ)
    (ℓ : functionals (upperUnipotent (n + 1) F) θ σ) (hℓ : ℓ.val ≠ 0)
    {ζ : ℂˣ} (hζ : HasModelMinusOneScalar σ ℓ ζ) :
    modelMinusOneScalar σ hσ = ζ :=
  (hasModelMinusOneScalar_modelMinusOneScalar σ hσ ℓ).unique hℓ hζ

end Langlands.RankinSelberg
