import Langlands.LocalFactor.Ramification.Herbrand.QuotientProof
import Langlands.LocalFactor.Ramification.HasseArf.Abelian

/-!
# The Hasse–Arf theorem for actual finite p-adic Galois extensions

The ported Anthropic FLT theorem
`Langlands.Ramification.hasseArfChain_lowerGroup_of_isMulCommutative` (a finite
commutative group acting faithfully on a discrete valuation ring with perfect residue field and
separable residue extension: at every lower break `i`, `|G_0|` divides `Σ_{j=1}^{i} |G_j|`) is
applied to the supplied integer ring of a finite extension of p-adic fields and its full
automorphism group. With the floor formula for the Library's Herbrand function this proves the
Library proposition `HasseArfIntegrality K L T` for every prime, every pair of p-adic fields in
independent universes and every supplied topological data `T`.
-/

noncomputable section

namespace Langlands.Ramification.Padic

open IsLocalRing

universe uK uL

section Divisibility

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]

/-- **Hasse–Arf divisibility for the Library's lower groups.** If the automorphism group of
`F` over `K` is commutative, then at every lower break `i` the order of the inertia group
`G_0` divides `Σ_{j=1}^{i} |G_j|`. -/
theorem lowerGroupOrder_zero_dvd_sum_of_break
    [IsMulCommutative (F.Carrier ≃ₐ[K] F.Carrier)] (i : ℕ)
    (hi : lowerRamificationGroup T K i ≠ lowerRamificationGroup T K (i + 1)) :
    lowerGroupOrder T K 0 ∣ ∑ j ∈ Finset.Icc 1 i, lowerGroupOrder T K j := by
  let := integerAction T K
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have _ : IsDiscreteValuationRing T.Integers := inferInstance
  have _ : FiniteDimensional K F.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier
  have := HerbrandBridge.integerAction_faithful T K
  have _ : Finite T.ResidueField := inferInstance
  have _ : Finite (T.Integers ⧸ maximalIdeal T.Integers) :=
    inferInstanceAs (Finite T.ResidueField)
  have _ : (maximalIdeal T.Integers).LiesOver
      (maximalIdeal (FixedPoints.subring T.Integers (F.Carrier ≃ₐ[K] F.Carrier))) :=
    ⟨maximalIdeal_fixedSubring_eq_comap⟩
  let _ : Field (T.Integers ⧸ maximalIdeal T.Integers) := Ideal.Quotient.field _
  let _ : Field (FixedPoints.subring T.Integers (F.Carrier ≃ₐ[K] F.Carrier) ⧸
      maximalIdeal (FixedPoints.subring T.Integers (F.Carrier ≃ₐ[K] F.Carrier))) :=
    Ideal.Quotient.field _
  have _ : Finite (FixedPoints.subring T.Integers (F.Carrier ≃ₐ[K] F.Carrier) ⧸
      maximalIdeal (FixedPoints.subring T.Integers (F.Carrier ≃ₐ[K] F.Carrier))) :=
    Finite.of_injective (algebraMap _ (T.Integers ⧸ maximalIdeal T.Integers))
      (algebraMap
        (FixedPoints.subring T.Integers (F.Carrier ≃ₐ[K] F.Carrier) ⧸
          maximalIdeal (FixedPoints.subring T.Integers (F.Carrier ≃ₐ[K] F.Carrier)))
        (T.Integers ⧸ maximalIdeal T.Integers)).injective
  exact hasseArfChain_lowerGroup_of_isMulCommutative i hi

/-- At a natural number the Library Herbrand function is the partial sum of the orders of the
positive lower groups divided by the inertia order. -/
theorem herbrandPhi_natCast_eq_sum_div (i : ℕ) :
    herbrandPhi T K i =
      ((∑ j ∈ Finset.Icc 1 i, lowerGroupOrder T K j : ℕ) : ℝ) / (lowerGroupOrder T K 0 : ℝ) := by
  rw [herbrandPhi_floor T K (Nat.cast_nonneg i), Nat.floor_natCast, sub_self, zero_mul,
    add_zero, Nat.cast_sum, HerbrandBridge.sum_Icc_one_eq_sum_range]

end Divisibility

/-- **The Hasse–Arf theorem** for an actual finite Galois extension `L/K` of p-adic fields:
if `Gal(L/K)` is commutative, the Library Herbrand function takes an integer value at every
lower break. This proves `HasseArfIntegrality K L T` for every supplied `T`. -/
theorem hasseArfIntegrality {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) (L : PadicField.{uL} p)
    [Algebra K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier L.Carrier]
    [IsGalois K.Carrier L.Carrier] (T : L.TopologicalData) : HasseArfIntegrality K L T := by
  intro hcomm i hi
  obtain ⟨n, hn⟩ := lowerGroupOrder_zero_dvd_sum_of_break T K.Carrier i hi
  refine ⟨(n : ℤ), ?_⟩
  have h0 : (lowerGroupOrder T K.Carrier 0 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (lowerGroupOrder_pos T K.Carrier 0).ne'
  rw [herbrandPhi_natCast_eq_sum_div, hn, Nat.cast_mul, Int.cast_natCast,
    mul_div_cancel_left₀ (n : ℝ) h0]

end Langlands.Ramification.Padic
