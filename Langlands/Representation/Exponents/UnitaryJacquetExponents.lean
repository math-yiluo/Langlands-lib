import Langlands.Representation.Exponents.ArbitraryParabolicUnitaryJacquetPart

/-! # The unitary normalized Jacquet exponent set and vanishing -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance unitaryExponentsAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

/-- The actual normalized Jacquet exponents whose normalized real part vanishes. -/
def unitaryJacquetExponents : Set (rationalPoints A.toGrp →* ℂˣ) :=
  {χ | IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ ∧
    Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0}

@[simp]
theorem mem_unitaryJacquetExponents (χ : rationalPoints A.toGrp →* ℂˣ) :
    χ ∈ unitaryJacquetExponents p l r hp hl hr hmul ha π ↔
      IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ ∧
        Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ = 0 :=
  Iff.rfl

/-- The unitary exponent set is a subset of the normalized Jacquet exponent set. -/
theorem unitaryJacquetExponents_subset_normalizedJacquetExponents :
    unitaryJacquetExponents p l r hp hl hr hmul ha π ⊆
      normalizedJacquetExponents p l r hp hl hr hmul ha π :=
  fun _ hχ => hχ.1

/-- The unitary part is exactly the sum over the unitary exponent set. -/
theorem unitaryJacquetPart_eq_iSup_unitaryJacquetExponents :
    unitaryJacquetPart p l r hp hl hr hmul ha π =
      ⨆ χ : unitaryJacquetExponents p l r hp hl hr hmul ha π,
        normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ := by
  rw [iSup_subtype]
  simp only [unitaryJacquetExponents, Set.mem_ofPred_eq, iSup_and]
  rfl

/-- Vanishing means that every actual exponent has nonzero normalized real part. -/
theorem unitaryJacquetPart_eq_bot_iff :
    unitaryJacquetPart p l r hp hl hr hmul ha π = ⊥ ↔
      ∀ χ : rationalPoints A.toGrp →* ℂˣ,
        IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ →
          Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ≠ 0 := by
  constructor
  · intro h χ hχ h0
    have hle := normalizedJacquetWeightSpace_le_unitaryJacquetPart
      p l r hp hl hr hmul ha π hχ h0
    rw [h] at hle
    exact ((isNormalizedJacquetExponent_iff_isOpen_ker_and
      p l r hp hl hr hmul ha π χ).mp hχ).2 (le_bot_iff.mp hle)
  · intro h
    apply bot_unique
    exact iSup_le fun χ => iSup_le fun hχ => iSup_le fun h0 => (h χ hχ h0).elim

/-- The unitary exponent set is empty exactly when the unitary part vanishes. -/
theorem unitaryJacquetExponents_eq_empty_iff :
    unitaryJacquetExponents p l r hp hl hr hmul ha π = ∅ ↔
      unitaryJacquetPart p l r hp hl hr hmul ha π = ⊥ := by
  rw [unitaryJacquetPart_eq_bot_iff]
  simp only [Set.eq_empty_iff_forall_notMem, mem_unitaryJacquetExponents, not_and]

/-- A nonzero unitary part is witnessed by an actual exponent with zero real part. -/
theorem unitaryJacquetExponents_nonempty_iff :
    (unitaryJacquetExponents p l r hp hl hr hmul ha π).Nonempty ↔
      unitaryJacquetPart p l r hp hl hr hmul ha π ≠ ⊥ := by
  rw [Set.nonempty_iff_ne_empty]
  exact not_congr (unitaryJacquetExponents_eq_empty_iff p l r hp hl hr hmul ha π)

end Langlands.Aubert.General.RepresentedParabolic
