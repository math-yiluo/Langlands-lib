import Langlands.Group.GL.CartanQuotientDefinitions

/-!
# Intrinsic algebraic laws for the concrete Cartan quotient cells

This closed proposition concerns only the published concrete constructions.
It states algebraic obligations; it neither assumes them as data nor proves them.
-/

namespace Langlands.GeneralLinear.CartanQuotient

open scoped NNReal

universe uF

/-- Membership, scalar shifts, radial weights, diagonal entries, the actual upper
Borel modulus, and normalization for the concrete quotient cells. -/
def CartanQuotientLawsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    -- 1. The existing membership formulas and subgroup monotonicity.
    ((∀ (n : ℕ) (lam : Fin n → ℤ) (x : centralQuotient F n),
        x ∈ cell T lam ↔
          ∃ k₁ ∈ maximalCompact T n, ∃ k₂ ∈ maximalCompact T n,
            x = quotientMap F n (k₁ * representative T lam * k₂)) ∧
      (∀ (n : ℕ) (H : Subgroup (GeneralLinear n F.Carrier))
          (lam : Fin n → ℤ) (x : centralQuotient F n),
        x ∈ subgroupCell T H lam ↔
          ∃ h₁ ∈ H, ∃ h₂ ∈ H,
            x = quotientMap F n (h₁ * representative T lam * h₂)) ∧
      (∀ (n : ℕ) (H J : Subgroup (GeneralLinear n F.Carrier))
          (lam : Fin n → ℤ),
        H ≤ J → subgroupCell T H lam ⊆ subgroupCell T J lam)) ∧
    -- 2. Scalars vanish in the actual quotient, and shifts preserve its cells.
    ((∀ (n : ℕ) (a : F.Carrierˣ),
        quotientMap F n (GeneralLinear.scalar a) = 1) ∧
      (∀ (n : ℕ) (a : F.Carrierˣ) (g : GeneralLinear n F.Carrier),
        quotientMap F n (GeneralLinear.scalar a * g) = quotientMap F n g) ∧
      (∀ (n : ℕ) (a : F.Carrierˣ) (g : GeneralLinear n F.Carrier),
        quotientMap F n (g * GeneralLinear.scalar a) = quotientMap F n g) ∧
      (∀ (n : ℕ) (lam : Fin n → ℤ) (c : ℤ),
        representative T (shift lam c) =
          GeneralLinear.scalar (LocalFactor.PadicAbelian.uniformizerUnit T ^ c) *
            representative T lam) ∧
      (∀ (n : ℕ) (lam : Fin n → ℤ) (c : ℤ),
        quotientMap F n (representative T (shift lam c)) =
          quotientMap F n (representative T lam)) ∧
      (∀ (n : ℕ) (H : Subgroup (GeneralLinear n F.Carrier))
          (lam : Fin n → ℤ) (c : ℤ),
        subgroupCell T H (shift lam c) = subgroupCell T H lam) ∧
      (∀ (n : ℕ) (lam : Fin n → ℤ) (c : ℤ),
        cell T (shift lam c) = cell T lam)) ∧
    -- 3. Shift invariance and positivity of the radial weights.
    ((∀ (n : ℕ) (lam : Fin n → ℤ) (c : ℤ),
        degree (shift lam c) = degree lam) ∧
      (∀ (n : ℕ) (lam : Fin n → ℤ) (c : ℤ),
        delta T (shift lam c) = delta T lam) ∧
      (∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → 0 ≤ degree lam) ∧
      (∀ (n : ℕ) (lam : Fin n → ℤ), 0 < delta T lam) ∧
      (∀ (n : ℕ) (lam : Fin n → ℤ), 0 < height lam)) ∧
    -- 4. The diagonal entries and their order in the positive chamber.
    ((∀ (n : ℕ) (lam : Fin n → ℤ) (i : Fin n),
        T.normalizedAbs (representative T lam i i) =
          (T.residueCardinality : ℝ) ^ (-lam i)) ∧
      (∀ (n : ℕ) (lam : Fin n → ℤ) (i j : Fin n),
        i ≠ j → representative T lam i j = 0) ∧
      (∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam →
        Monotone (fun i => T.normalizedAbs (representative T lam i i)))) ∧
    -- 5. The same matrices in the singleton Levi and upper Borel, with its modulus.
    ((∀ (n : ℕ) (lam : Fin n → ℤ),
        ((BlockShape.singletons n).leviEmbedding F.Carrier
          (representativeLevi T lam)).val = (representative T lam).val) ∧
      (∀ (n : ℕ) (lam : Fin n → ℤ),
        ((representativeBorel T lam : GeneralLinear n F.Carrier)).val =
          (representative T lam).val) ∧
      (∀ (n : ℕ) (lam : Fin n → ℤ),
        delta T lam =
          ((T.leviModulus (BlockShape.singletons n) (representativeLevi T lam) :
            ℝ≥0) : ℝ)) ∧
      (∀ (n : ℕ) (lam : Fin n → ℤ),
        delta T lam =
          ((T.parabolicModulus (BlockShape.singletons n) (representativeBorel T lam) :
            ℝ≥0) : ℝ))) ∧
    -- 6. Last-coordinate normalization in positive rank, and inherited countability.
    ((∀ (m : ℕ) (lam : Fin (m + 1) → ℤ),
        Normalized lam ↔ Antitone lam ∧ lam (Fin.last m) = 0) ∧
      (∀ (lam : Fin 1 → ℤ), Normalized lam ↔ lam = 0) ∧
      (∀ (n : ℕ), Countable (NormalizedTuple n)))

end Langlands.GeneralLinear.CartanQuotient
