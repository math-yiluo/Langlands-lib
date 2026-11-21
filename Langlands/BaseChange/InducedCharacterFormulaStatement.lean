import Langlands.BaseChange.LeviClassSystem
import Langlands.BaseChange.RelativeParabolicDiscriminant
import Langlands.BaseChange.SigmaInducedIntertwiner
import Langlands.Group.GL.LocalFieldTopology
import Langlands.JacquetLanglands.LocalCharacter
import Langlands.LocalField.ResidueNormalization

/-! # The induced character formula at regular semisimple points

This module states the ordinary case of Henniart–Lemaire (2011), II.4.5, formula (3). It
supplies no proof.
-/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear JacquetLanglands

universe u uV

/-- The weight `|D_{G/M}(m)|_F^{-1/2}` of Henniart–Lemaire II.4.5 (3), for the relative
discriminant `det_F(1 - Ad(m)⁻¹; g/m)` and the normalized absolute value of `F`. -/
def relativeDiscriminantWeight {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n : ℕ} (B : BlockShape n) (m : B.Levi F) : ℂ :=
  ((Real.sqrt (LocalField.residueNormalizedAbsoluteValue F
    (relativeParabolicDiscriminant B F m)))⁻¹ : ℝ)

/-- Ordinary Henniart–Lemaire II.4.5 (3): at a regular semisimple `γ`, the character of the
normalized product induction of irreducible admissible block representations is the sum,
over a Levi class system `m` for `γ`, of `|D_{G/M}(m_j)|_F^{-1/2}` times the character value
of the Levi tensor representation at `m_j`. An empty system gives the value zero. -/
def InducedCharacterFormulaStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n → ∀ (B : BlockShape n)
    (V : Fin B.length → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    (hπ : ∀ i, IsAdmissible (π i)), (∀ i, (π i).IsIrreducible) →
    ∀ (γ : GeneralLinear n F), IsRegularSemisimple γ →
    ∀ (k : ℕ) (m : Fin k → B.Levi F), IsLeviClassSystem B γ m →
    ∀ (a : Fin k → ℂ),
      (∀ j,
        haveI : ∀ i, T2Space (GeneralLinear (B.size i) F) := fun i =>
          LocalFieldTopology.generalLinear_t2Space F (B.size i)
        haveI : ∀ i, LocallyCompactSpace (GeneralLinear (B.size i) F) := fun i =>
          LocalFieldTopology.generalLinear_locallyCompactSpace F (B.size i)
        haveI : ∀ i, TotallyDisconnectedSpace (GeneralLinear (B.size i) F) := fun i =>
          LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (B.size i)
        HasCharacterValue (B.blockTensor π) (FiniteTensor.isAdmissible_external π hπ)
          (m j) (a j)) →
      haveI := LocalFieldTopology.generalLinear_t2Space F n
      haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
      haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
      HasCharacterValue ((LocalFieldData.ofInstances F).normalizedProductInduced B π)
        (isAdmissible_normalizedProductInduced B π hπ) γ
        (∑ j, relativeDiscriminantWeight B (m j) * a j)

end Langlands.BaseChange
