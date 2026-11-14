import Langlands.Representation.Whittaker.CoefficientRightStabilizer
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
/-!
# Common right stabilizers for actual coefficient functions

Smoothness gives a common compact open right stabilizer in every prescribed
identity neighborhood. The p-adic specialization uses the supplied topology
and puts that stabilizer in the normalized determinant kernel.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding exists_compactOpen_glCoefficientRightStabilizer
open Langlands.AllField.Whittaker

open _root_.Topology
open scoped NNReal

universe uR uG uV uW uF

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable {W : Type uW} [AddCommGroup W] [Module R W]
variable {N N' : Subgroup G} {θ : N →* Rˣ} {θ' : N' →* Rˣ}

section Padic

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- For every supplied local-field topology, two actual Whittaker coefficient
vectors have a common compact open right stabilizer on which the supplied
normalized determinant absolute value is one. Rank one is included. -/
theorem exists_compactOpen_glCoefficientRightStabilizer (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
      IsSmooth π → IsSmooth σ →
      ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
        (f : (coefficientModel π ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule),
      ∃ J : OpenSubgroup (Langlands.GeneralLinear (n + 1) F),
        IsCompact (J : Set (Langlands.GeneralLinear (n + 1) F)) ∧
        IsCommonCoefficientRightStabilizer f f' J.toSubgroup ∧
        ∀ j : J, T.normalizedAbs (Matrix.det j.val.val) = 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ W _ _ π σ hπ hσ ℓ ℓ' f f'
  let := T.generalLinearNonarchimedean (n + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1)
  let K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F) :=
    ⟨(T.determinantNorm (n + 1)).ker, T.isOpen_ker_determinantNorm (n + 1)⟩
  obtain ⟨J, hJ, hJK, hfix⟩ := exists_compactOpen_coefficientRightStabilizer
    π σ hπ hσ ℓ ℓ' f f' (K : Set _) K.mem_nhds_one
  refine ⟨J, hJ, hfix, ?_⟩
  intro j
  have hj : T.determinantNorm (n + 1) j.val = 1 := hJK j.property
  have heq := congrArg (fun a : ℝ≥0ˣ => ((a : ℝ≥0) : ℝ)) hj
  exact heq

end Padic

end Langlands.AllField.Whittaker
