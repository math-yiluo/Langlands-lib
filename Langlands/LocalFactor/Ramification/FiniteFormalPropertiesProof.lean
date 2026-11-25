import Langlands.LocalFactor.Ramification.FiniteExactSequenceProof
import Langlands.LocalFactor.Ramification.FiniteIntegralityProof
import Langlands.LocalFactor.Ramification.ConductorFunctional
import Langlands.Representation.Twist.AdmissibilityProof
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Intertwining

/-!
# The formal properties of the finite-Galois Artin and Swan conductors

For a finite group `G` acting faithfully on a Noetherian local ring `R`, every summand
`|G_i|/|G_0| · codim V^{G_i}` of the Artin and Swan expressions is

* additive on a product `V × W` (from the short exact sequence `0 → V → V × W → W → 0`),
* unchanged under the dual (`dim (V^*)^H = dim V^H` by the averaging formula and
  `χ_{V^*}(h) = χ_V(h⁻¹)`),
* unchanged under the twist by a character trivial on `G_0` (the twist does not change the
  vectors fixed by any `G_i ⊆ G_0`),
* zero exactly when `G_i` acts trivially (the weight `|G_i|/|G_0|` is positive).

Hence the Artin expression vanishes exactly when `G_0` acts trivially, the Swan expression
exactly when `G_1` does, and when `G_1` acts trivially the Artin expression is the codimension
of the `G_0`-invariants. For the integer-ring action of the automorphism group of a finite
extension of p-adic fields these are the five sister statements of `FiniteStatement.lean`
(direct sum, dual, unramified twist, vanishing, tame), and with integrality
(`finiteGaloisConductorIntegrality`) and additivity in short exact sequences
(`finiteGaloisConductorExactSequence`) they prove the conjunction
`FiniteGaloisConductorStatement` (`finiteGaloisConductor`). None of the arguments uses the
Galois hypothesis; the p-adic lemmas are stated without it.
-/

noncomputable section

namespace Langlands.Ramification

open Module

universe uK uL uU uR uG uk uV uW

section FixedCodimension

variable (G : Type uG) [Group G] {k : Type uk} [Field k]
  {V : Type uV} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The fixed codimension of a subgroup vanishes exactly when the subgroup acts trivially. -/
theorem fixedCodimension_eq_zero_iff (ρ : Representation k G V) (H : Subgroup G) :
    fixedCodimension G ρ H = 0 ↔ ∀ g ∈ H, ∀ v : V, ρ g v = v := by
  rw [fixedCodimension, Nat.sub_eq_zero_iff_le]
  constructor
  · intro h g hg v
    have htop : fixedVectors ρ H = ⊤ :=
      Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) h)
    have hv : v ∈ fixedVectors ρ H := htop ▸ Submodule.mem_top
    exact (Representation.mem_invariants _ v).mp hv ⟨g, hg⟩
  · intro h
    have htop : fixedVectors ρ H = ⊤ := by
      refine Submodule.eq_top_iff'.mpr fun v => ?_
      exact (Representation.mem_invariants _ v).mpr fun g => h g g.2 v
    rw [htop, finrank_top]

end FixedCodimension

section Dual

variable (G : Type uG) [Group G] [Finite G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- **The dual has the same fixed codimensions**: `dim (V^*)^H = dim V^H` for every subgroup of a
finite group, by the averaging formula and `χ_{V^*}(h) = χ_V(h⁻¹)`. -/
theorem fixedCodimension_dual (ρ : Representation ℂ G V) (H : Subgroup G) :
    fixedCodimension G ρ.dual H = fixedCodimension G ρ H := by
  classical
  let := Fintype.ofFinite G
  have hdual := LocalFactor.SpectralConductor.finrank_fixedVectors ρ.dual H
  have hρ := LocalFactor.SpectralConductor.finrank_fixedVectors ρ H
  have hsum : (∑ g : G, if g ∈ H then LinearMap.trace ℂ (Dual ℂ V) (ρ.dual g) else 0) =
      ∑ g : G, if g ∈ H then LinearMap.trace ℂ V (ρ g) else 0 := by
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
    have hc : LinearMap.trace ℂ (Dual ℂ V) (ρ.dual g) = LinearMap.trace ℂ V (ρ g⁻¹) :=
      Representation.char_dual ρ g
    simp only [Equiv.inv_apply, inv_mem_iff, hc]
  have hfin : finrank ℂ (fixedVectors ρ.dual H) = finrank ℂ (fixedVectors ρ H) := by
    have h : (finrank ℂ (fixedVectors ρ.dual H) : ℂ) = finrank ℂ (fixedVectors ρ H) := by
      rw [hdual, hρ, hsum]
    exact_mod_cast h
  rw [fixedCodimension, fixedCodimension, Subspace.dual_finrank_eq, hfin]

end Dual

section Conductor

variable (R : Type uR) (G : Type uG) [CommRing R] [IsLocalRing R] [Group G]
  [MulSemiringAction G R]

section Term

variable {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- A twist by a character trivial on `G_0` does not change the conductor summands. -/
theorem conductorTerm_twist (ρ : Representation k G V) (χ : G →* kˣ)
    (hχ : ∀ g ∈ lowerGroup R G 0, χ g = 1) (i : ℕ) :
    conductorTerm R G (Langlands.twist χ ρ) i = conductorTerm R G ρ i := by
  have hle : lowerGroup R G i ≤ χ.ker := fun g hg =>
    hχ g (lowerGroup_antitone R G (Nat.zero_le i) hg)
  have hfix : fixedCodimension G (Langlands.twist χ ρ) (lowerGroup R G i) =
      fixedCodimension G ρ (lowerGroup R G i) := by
    unfold fixedCodimension
    rw [fixedVectors_twist_eq_of_le_ker χ ρ _ hle]
  simp only [conductorTerm, hfix]

/-- A conductor summand vanishes exactly when `G_i` acts trivially. -/
theorem conductorTerm_eq_zero_iff [Finite G] (ρ : Representation k G V) (i : ℕ) :
    conductorTerm R G ρ i = 0 ↔ ∀ g ∈ lowerGroup R G i, ∀ v : V, ρ g v = v := by
  have hi : (0 : ℚ) < Nat.card (lowerGroup R G i) := by exact_mod_cast Nat.card_pos
  have h0 : (0 : ℚ) < Nat.card (lowerGroup R G 0) := by exact_mod_cast Nat.card_pos
  rw [conductorTerm, mul_eq_zero, or_iff_right (div_pos hi h0).ne', Nat.cast_eq_zero,
    fixedCodimension_eq_zero_iff]

end Term

section Dual

variable [Finite G] {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem conductorTerm_dual (ρ : Representation ℂ G V) (i : ℕ) :
    conductorTerm R G ρ.dual i = conductorTerm R G ρ i := by
  simp only [conductorTerm, fixedCodimension_dual G]

variable [IsNoetherianRing R] [FaithfulSMul G R]

/-- **The Artin expression of the dual** is that of the representation. -/
theorem artinConductor_dual (ρ : Representation ℂ G V) :
    artinConductor R G ρ.dual = artinConductor R G ρ := by
  simp only [artinConductor_eq_finsum, conductorTerm_dual]

/-- **The Swan expression of the dual** is that of the representation. -/
theorem swanConductor_dual (ρ : Representation ℂ G V) :
    swanConductor R G ρ.dual = swanConductor R G ρ := by
  simp only [swanConductor_eq_finsum, conductorTerm_dual]

end Dual

variable [IsNoetherianRing R] [FaithfulSMul G R] [Finite G]

section Prod

variable {k : Type uk} [Field k] [CharZero k]
  {V : Type uV} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {W : Type uW} [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- **The Artin expression is additive on direct sums.** -/
theorem artinConductor_prod (ρ : Representation k G V) (σ : Representation k G W) :
    artinConductor R G (ρ.prod σ) = artinConductor R G ρ + artinConductor R G σ :=
  artinConductor_eq_add R G (Representation.IntertwiningMap.inl k ρ σ)
    (Representation.IntertwiningMap.snd k ρ σ) LinearMap.inl_injective
    (LinearMap.range_inl k V W) LinearMap.snd_surjective

/-- **The Swan expression is additive on direct sums.** -/
theorem swanConductor_prod (ρ : Representation k G V) (σ : Representation k G W) :
    swanConductor R G (ρ.prod σ) = swanConductor R G ρ + swanConductor R G σ :=
  swanConductor_eq_add R G (Representation.IntertwiningMap.inl k ρ σ)
    (Representation.IntertwiningMap.snd k ρ σ) LinearMap.inl_injective
    (LinearMap.range_inl k V W) LinearMap.snd_surjective

end Prod

variable {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- **Unramified twist**: a twist by a character trivial on `G_0` does not change the Artin
expression. -/
theorem artinConductor_twist (ρ : Representation k G V) (χ : G →* kˣ)
    (hχ : ∀ g ∈ lowerGroup R G 0, χ g = 1) :
    artinConductor R G (Langlands.twist χ ρ) = artinConductor R G ρ := by
  simp only [artinConductor_eq_finsum, conductorTerm_twist R G ρ χ hχ]

/-- A twist by a character trivial on `G_0` does not change the Swan expression. -/
theorem swanConductor_twist (ρ : Representation k G V) (χ : G →* kˣ)
    (hχ : ∀ g ∈ lowerGroup R G 0, χ g = 1) :
    swanConductor R G (Langlands.twist χ ρ) = swanConductor R G ρ := by
  simp only [swanConductor_eq_finsum, conductorTerm_twist R G ρ χ hχ]

/-- **The Artin expression vanishes exactly when `G_0` acts trivially.** -/
theorem artinConductor_eq_zero_iff (ρ : Representation k G V) :
    artinConductor R G ρ = 0 ↔ ∀ g ∈ lowerGroup R G 0, ∀ v : V, ρ g v = v := by
  rw [← fixedCodimension_eq_zero_iff G ρ]
  constructor
  · intro h
    have htame := artinConductor_eq_tame_add_swan R G ρ
    have hswan := swanConductor_nonneg R G ρ
    have hc : (0 : ℚ) ≤ fixedCodimension G ρ (lowerGroup R G 0) := Nat.cast_nonneg _
    have : (fixedCodimension G ρ (lowerGroup R G 0) : ℚ) = 0 := by linarith
    exact_mod_cast this
  · intro h
    have hterm (i : ℕ) : conductorTerm R G ρ i = 0 :=
      (conductorTerm_eq_zero_iff R G ρ i).mpr fun g hg v =>
        (fixedCodimension_eq_zero_iff G ρ _).mp h g
          (lowerGroup_antitone R G (Nat.zero_le i) hg) v
    simp [artinConductor_eq_finsum, hterm]

/-- **The Swan expression vanishes exactly when `G_1` acts trivially.** -/
theorem swanConductor_eq_zero_iff (ρ : Representation k G V) :
    swanConductor R G ρ = 0 ↔ ∀ g ∈ lowerGroup R G 1, ∀ v : V, ρ g v = v := by
  rw [← conductorTerm_eq_zero_iff R G ρ 1]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := exists_lowerGroup_eq_bot R G
    rw [swanConductor_eq_sum_range R G ρ (b + 1) fun i hi => hb i (by omega)] at h
    exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => conductorTerm_nonneg R G ρ (i + 1)).mp
      h 0 (by simp)
  · intro h
    have hterm (i : ℕ) : conductorTerm R G ρ (i + 1) = 0 :=
      (conductorTerm_eq_zero_iff R G ρ (i + 1)).mpr fun g hg v =>
        (conductorTerm_eq_zero_iff R G ρ 1).mp h g
          (lowerGroup_antitone R G (by omega : 1 ≤ i + 1) hg) v
    simp [swanConductor_eq_finsum, hterm]

/-- **Tame representations**: when `G_1` acts trivially, the Artin expression is the
codimension of the `G_0`-invariants. -/
theorem artinConductor_eq_fixedCodimension_of_lowerGroup_one (ρ : Representation k G V)
    (h : ∀ g ∈ lowerGroup R G 1, ∀ v : V, ρ g v = v) :
    artinConductor R G ρ = fixedCodimension G ρ (lowerGroup R G 0) := by
  rw [artinConductor_eq_tame_add_swan R G ρ, (swanConductor_eq_zero_iff R G ρ).mpr h, add_zero]

end Conductor

namespace Padic


variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]

section Lemmas

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- The p-adic Artin expression is additive on direct sums. -/
theorem artinConductor_prod (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V)
    (σ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) W) :
    artinConductor T K (ρ.prod σ) = artinConductor T K ρ + artinConductor T K σ := by
  let := integerAction T K
  have := HerbrandBridge.integerAction_faithful T K
  have := LocalFactor.SpectralConductor.integerRing_noetherian' T
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  exact Ramification.artinConductor_prod T.Integers _ ρ σ

/-- The p-adic Swan expression is additive on direct sums. -/
theorem swanConductor_prod (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V)
    (σ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) W) :
    swanConductor T K (ρ.prod σ) = swanConductor T K ρ + swanConductor T K σ := by
  let := integerAction T K
  have := HerbrandBridge.integerAction_faithful T K
  have := LocalFactor.SpectralConductor.integerRing_noetherian' T
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  exact Ramification.swanConductor_prod T.Integers _ ρ σ

/-- The p-adic Artin expression of the dual is that of the representation. -/
theorem artinConductor_dual (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    artinConductor T K ρ.dual = artinConductor T K ρ := by
  let := integerAction T K
  have := HerbrandBridge.integerAction_faithful T K
  have := LocalFactor.SpectralConductor.integerRing_noetherian' T
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  exact Ramification.artinConductor_dual T.Integers _ ρ

/-- The p-adic Swan expression of the dual is that of the representation. -/
theorem swanConductor_dual (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    swanConductor T K ρ.dual = swanConductor T K ρ := by
  let := integerAction T K
  have := HerbrandBridge.integerAction_faithful T K
  have := LocalFactor.SpectralConductor.integerRing_noetherian' T
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  exact Ramification.swanConductor_dual T.Integers _ ρ

/-- A twist by a character trivial on inertia does not change the p-adic Artin expression. -/
theorem artinConductor_twist (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V)
    (χ : (F.Carrier ≃ₐ[K] F.Carrier) →* ℂˣ) (hχ : ∀ g ∈ inertia T K, χ g = 1) :
    artinConductor T K (Langlands.twist χ ρ) = artinConductor T K ρ := by
  let := integerAction T K
  have := HerbrandBridge.integerAction_faithful T K
  have := LocalFactor.SpectralConductor.integerRing_noetherian' T
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  have h0 : lowerGroup T.Integers (F.Carrier ≃ₐ[K] F.Carrier) 0 = inertia T K :=
    lowerRamificationGroup_zero T K
  exact Ramification.artinConductor_twist T.Integers _ ρ χ (h0 ▸ hχ)

/-- A twist by a character trivial on inertia does not change the p-adic Swan expression. -/
theorem swanConductor_twist (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V)
    (χ : (F.Carrier ≃ₐ[K] F.Carrier) →* ℂˣ) (hχ : ∀ g ∈ inertia T K, χ g = 1) :
    swanConductor T K (Langlands.twist χ ρ) = swanConductor T K ρ := by
  let := integerAction T K
  have := HerbrandBridge.integerAction_faithful T K
  have := LocalFactor.SpectralConductor.integerRing_noetherian' T
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  have h0 : lowerGroup T.Integers (F.Carrier ≃ₐ[K] F.Carrier) 0 = inertia T K :=
    lowerRamificationGroup_zero T K
  exact Ramification.swanConductor_twist T.Integers _ ρ χ (h0 ▸ hχ)

/-- The p-adic Artin expression vanishes exactly when inertia acts trivially. -/
theorem artinConductor_eq_zero_iff (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    artinConductor T K ρ = 0 ↔ ∀ g ∈ inertia T K, ∀ v : V, ρ g v = v := by
  let := integerAction T K
  have := HerbrandBridge.integerAction_faithful T K
  have := LocalFactor.SpectralConductor.integerRing_noetherian' T
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  have h0 : lowerGroup T.Integers (F.Carrier ≃ₐ[K] F.Carrier) 0 = inertia T K :=
    lowerRamificationGroup_zero T K
  rw [← h0]
  exact Ramification.artinConductor_eq_zero_iff T.Integers _ ρ

/-- The p-adic Swan expression vanishes exactly when the first lower group acts trivially. -/
theorem swanConductor_eq_zero_iff (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    swanConductor T K ρ = 0 ↔ ∀ g ∈ lowerRamificationGroup T K 1, ∀ v : V, ρ g v = v := by
  let := integerAction T K
  have := HerbrandBridge.integerAction_faithful T K
  have := LocalFactor.SpectralConductor.integerRing_noetherian' T
  have := LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  exact Ramification.swanConductor_eq_zero_iff T.Integers _ ρ

/-- When the first lower group acts trivially, the p-adic Artin expression is the codimension
of the inertia invariants. -/
theorem artinConductor_eq_fixedCodimension_of_lowerRamificationGroup_one
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V)
    (h : ∀ g ∈ lowerRamificationGroup T K 1, ∀ v : V, ρ g v = v) :
    artinConductor T K ρ =
      (fixedCodimension (F.Carrier ≃ₐ[K] F.Carrier) ρ (inertia T K) : ℚ) := by
  rw [Langlands.Ramification.Padic.artinConductor_eq_tame_add_swan T K ρ,
    (swanConductor_eq_zero_iff T K ρ).mpr h, add_zero]

end Lemmas

/-- **Direct sums.** The Artin and Swan conductors of `ρ ⊕ σ` are the sums. -/
theorem finiteGaloisConductorDirectSum {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
    (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] :
    FiniteGaloisConductorDirectSumStatement T K (V := V) (W := W) :=
  fun ρ σ => ⟨artinConductor_prod T K ρ σ, swanConductor_prod T K ρ σ⟩

/-- **Duals.** The Artin and Swan conductors of the dual are those of the representation. -/
theorem finiteGaloisConductorDual {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
    (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    FiniteGaloisConductorDualStatement T K (V := V) :=
  fun ρ => ⟨artinConductor_dual T K ρ, swanConductor_dual T K ρ⟩

/-- **Unramified twists.** Twisting by a character trivial on inertia changes neither
conductor. -/
theorem finiteGaloisConductorUnramifiedTwist {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
    (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    FiniteGaloisConductorUnramifiedTwistStatement T K (V := V) :=
  fun ρ χ hχ => ⟨artinConductor_twist T K ρ χ hχ, swanConductor_twist T K ρ χ hχ⟩

/-- **Vanishing.** The Artin conductor vanishes exactly on representations trivial on inertia,
the Swan conductor exactly on those trivial on the first lower group. -/
theorem finiteGaloisConductorVanishing {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
    (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    FiniteGaloisConductorVanishingStatement T K (V := V) :=
  fun ρ => ⟨artinConductor_eq_zero_iff T K ρ, swanConductor_eq_zero_iff T K ρ⟩

/-- **Tame representations.** When the first lower group acts trivially, the Artin conductor is
the codimension of the inertia invariants. -/
theorem finiteGaloisTameArtin {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
    (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    FiniteGaloisTameArtinStatement T K (V := V) :=
  fun ρ h => artinConductor_eq_fixedCodimension_of_lowerRamificationGroup_one T K ρ h

/-- **The complete family** of finite-Galois conductor statements: integrality, additivity in
short exact sequences, direct sums, duals, unramified twists, vanishing and the tame formula. -/
theorem finiteGaloisConductor : FiniteGaloisConductorStatement.{uK, uL, uU, uV, uW} :=
  fun _ _ _ T K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    ⟨finiteGaloisConductorIntegrality T K, finiteGaloisConductorExactSequence T K,
      finiteGaloisConductorDirectSum T K, finiteGaloisConductorDual T K,
      finiteGaloisConductorUnramifiedTwist T K, finiteGaloisConductorVanishing T K,
      finiteGaloisTameArtin T K⟩

end Padic

end Langlands.Ramification
