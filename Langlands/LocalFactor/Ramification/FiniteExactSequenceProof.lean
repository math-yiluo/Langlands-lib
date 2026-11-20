import Langlands.LocalFactor.SpectralConductorFunctional
import Langlands.LocalFactor.Ramification.Herbrand.QuotientProof
import Langlands.LocalFactor.Ramification.FiniteStatement
import Mathlib.RepresentationTheory.Invariants

/-!
# Additivity of finite-Galois conductors in short exact sequences

For a short exact sequence `0 → U → V → W → 0` of representations of a finite
group over a field of characteristic zero, the fixed vectors of every subgroup
form a short exact sequence again (surjectivity by averaging). Hence every
fixed-space codimension, every conductor summand, and the generic Artin and
Swan sums are additive. Specializing to the actual integer-ring action of a
finite p-adic Galois group proves
`Langlands.Ramification.Padic.FiniteGaloisConductorExactSequenceStatement`.
-/

noncomputable section

namespace Langlands.Ramification

open Module

section Linear

universe uk uA uB uC

variable {k : Type uk} [Field k]
  {A : Type uA} [AddCommGroup A] [Module k A]
  {B : Type uB} [AddCommGroup B] [Module k B]
  {C : Type uC} [AddCommGroup C] [Module k C]

/-- Dimension is additive along a short exact sequence of vector spaces. -/
theorem finrank_eq_add_of_shortExact [FiniteDimensional k B]
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (hf : Function.Injective f)
    (hfg : LinearMap.range f = LinearMap.ker g) (hg : Function.Surjective g) :
    finrank k B = finrank k A + finrank k C := by
  rw [← LinearMap.finrank_range_add_finrank_ker g, LinearMap.range_eq_top.mpr hg,
    finrank_top, ← hfg, LinearMap.finrank_range_of_inj hf, add_comm]

end Linear

section FixedVectors

universe uk uG uH uU uV uW

variable {k : Type uk} [Field k] {G : Type uG} [Group G]
  {U : Type uU} [AddCommGroup U] [Module k U]
  {V : Type uV} [AddCommGroup V] [Module k V]
  {W : Type uW} [AddCommGroup W] [Module k W]
  {ρ : Representation k G U} {σ : Representation k G V} {τ : Representation k G W}

/-- Mathlib's averaging projection, written as the normalized sum. -/
theorem averageMap_eq_smul_sum {H : Type uH} [Group H] [Fintype H]
    [Invertible (Fintype.card H : k)] (π : Representation k H V) (v : V) :
    π.averageMap v = ⅟(Fintype.card H : k) • ∑ h : H, π h v := by
  simp [GroupAlgebra.average, map_sum]

/-- An intertwiner commutes with averaging over a finite subgroup. -/
theorem intertwiningMap_averageMap (q : σ.IntertwiningMap τ) (N : Subgroup G)
    [Fintype N] [Invertible (Fintype.card N : k)] (v : V) :
    q (Representation.averageMap (σ.comp N.subtype) v) =
      Representation.averageMap (τ.comp N.subtype) (q v) := by
  rw [averageMap_eq_smul_sum, averageMap_eq_smul_sum, map_smul, map_sum]
  simp only [MonoidHom.coe_comp, Function.comp_apply, q.isIntertwining]

/-- Averaging lifts fixed vectors along a surjective intertwiner. -/
theorem fixedVectorsMap_surjective (q : σ.IntertwiningMap τ)
    (hq : Function.Surjective q) (N : Subgroup G) [Fintype N]
    [Invertible (Fintype.card N : k)] :
    Function.Surjective (fixedVectorsMap q N) := by
  rintro ⟨w, hw⟩
  obtain ⟨v, rfl⟩ := hq w
  refine ⟨⟨Representation.averageMap (σ.comp N.subtype) v,
    Representation.averageMap_invariant (σ.comp N.subtype) v⟩, ?_⟩
  apply Subtype.ext
  change q (Representation.averageMap (σ.comp N.subtype) v) = q v
  rw [intertwiningMap_averageMap]
  exact Representation.averageMap_id (τ.comp N.subtype) (q v) hw

/-- Exactness in the middle is inherited by fixed vectors. -/
theorem range_fixedVectorsMap_eq_ker (i : ρ.IntertwiningMap σ)
    (q : σ.IntertwiningMap τ) (hi : Function.Injective i)
    (hiq : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    (N : Subgroup G) :
    LinearMap.range (fixedVectorsMap i N) = LinearMap.ker (fixedVectorsMap q N) := by
  ext ⟨v, hv⟩
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨u, hu⟩, h⟩
    have huv : i u = v := congrArg Subtype.val h
    apply Subtype.ext
    change q v = 0
    have hmem : v ∈ LinearMap.range i.toLinearMap := ⟨u, huv⟩
    rw [hiq, LinearMap.mem_ker] at hmem
    exact hmem
  · intro h
    have hq0 : q v = 0 := congrArg Subtype.val h
    have hmem : v ∈ LinearMap.ker q.toLinearMap := hq0
    rw [← hiq] at hmem
    obtain ⟨u, hu⟩ := hmem
    have hu' : i u = v := hu
    refine ⟨⟨u, ?_⟩, Subtype.ext hu'⟩
    intro g
    apply hi
    change i (ρ (g : G) u) = i u
    rw [i.isIntertwining, hu']
    exact hv g

/-- Dimensions of fixed vectors are additive along a short exact sequence. -/
theorem finrank_fixedVectors_eq_add [FiniteDimensional k V]
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ) (hi : Function.Injective i)
    (hiq : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    (hq : Function.Surjective q) (N : Subgroup G) [Fintype N]
    [Invertible (Fintype.card N : k)] :
    finrank k (fixedVectors σ N) =
      finrank k (fixedVectors ρ N) + finrank k (fixedVectors τ N) := by
  refine finrank_eq_add_of_shortExact (fixedVectorsMap i N) (fixedVectorsMap q N)
    ?_ (range_fixedVectorsMap_eq_ker i q hi hiq N) (fixedVectorsMap_surjective q hq N)
  intro u u' h
  exact Subtype.ext (hi (congrArg Subtype.val h))

variable (G) in
/-- Fixed-space codimensions are additive along a short exact sequence. -/
theorem fixedCodimension_eq_add [FiniteDimensional k U] [FiniteDimensional k V]
    [FiniteDimensional k W]
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ) (hi : Function.Injective i)
    (hiq : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    (hq : Function.Surjective q) (N : Subgroup G) [Fintype N]
    [Invertible (Fintype.card N : k)] :
    fixedCodimension G σ N = fixedCodimension G ρ N + fixedCodimension G τ N := by
  have hV := finrank_eq_add_of_shortExact i.toLinearMap q.toLinearMap hi hiq hq
  have hN := finrank_fixedVectors_eq_add i q hi hiq hq N
  have hU := Submodule.finrank_le (fixedVectors ρ N)
  have hW := Submodule.finrank_le (fixedVectors τ N)
  unfold fixedCodimension
  omega

end FixedVectors

section Conductor

universe uR uG uk uU uV uW

variable (R : Type uR) (G : Type uG) [CommRing R] [IsLocalRing R]
  [Group G] [MulSemiringAction G R]
  {k : Type uk} [Field k] [CharZero k]
  {U : Type uU} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
  {V : Type uV} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {W : Type uW} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  {ρ : Representation k G U} {σ : Representation k G V} {τ : Representation k G W}

/-- Each conductor summand is additive along a short exact sequence. -/
theorem conductorTerm_eq_add [Finite G]
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ) (hi : Function.Injective i)
    (hiq : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    (hq : Function.Surjective q) (n : ℕ) :
    conductorTerm R G σ n = conductorTerm R G ρ n + conductorTerm R G τ n := by
  let : Fintype (lowerGroup R G n) := Fintype.ofFinite _
  let : Invertible (Fintype.card (lowerGroup R G n) : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  simp only [conductorTerm, fixedCodimension_eq_add G i q hi hiq hq, Nat.cast_add, mul_add]

variable [IsNoetherianRing R] [FaithfulSMul G R] [Finite G]

/-- The generic Artin expression is additive along a short exact sequence. -/
theorem artinConductor_eq_add
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ) (hi : Function.Injective i)
    (hiq : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    (hq : Function.Surjective q) :
    artinConductor R G σ = artinConductor R G ρ + artinConductor R G τ := by
  obtain ⟨b, hb⟩ := exists_lowerGroup_eq_bot R G
  rw [artinConductor_eq_sum_range R G σ b hb, artinConductor_eq_sum_range R G ρ b hb,
    artinConductor_eq_sum_range R G τ b hb, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => conductorTerm_eq_add R G i q hi hiq hq n

/-- The generic Swan expression is additive along a short exact sequence. -/
theorem swanConductor_eq_add
    (i : ρ.IntertwiningMap σ) (q : σ.IntertwiningMap τ) (hi : Function.Injective i)
    (hiq : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap)
    (hq : Function.Surjective q) :
    swanConductor R G σ = swanConductor R G ρ + swanConductor R G τ := by
  obtain ⟨b, hb⟩ := exists_lowerGroup_eq_bot R G
  rw [swanConductor_eq_sum_range R G σ b hb, swanConductor_eq_sum_range R G ρ b hb,
    swanConductor_eq_sum_range R G τ b hb, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => conductorTerm_eq_add R G i q hi hiq hq (n + 1)

end Conductor

namespace Padic

universe uK uL uU uV uW

section Instances

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]

end Instances

/-- Additivity of the actual finite-Galois Artin and Swan conductors along short
exact sequences of finite-dimensional complex representations. -/
theorem finiteGaloisConductorExactSequence
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p} (T : F.TopologicalData)
    (K : Type uK) [Field K] [Algebra (Padic p) K] [Algebra K F.Carrier]
    [IsScalarTower (Padic p) K F.Carrier]
    {U : Type uU} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] :
    FiniteGaloisConductorExactSequenceStatement T K (U := U) (V := V) (W := W) := by
  intro _ ρ σ τ i q hi hiq hq
  let := integerAction T K
  have := Langlands.Ramification.HerbrandBridge.integerAction_faithful T K
  have := Langlands.LocalFactor.SpectralConductor.integerRing_noetherian' T
  have := Langlands.LocalFactor.SpectralConductor.automorphismGroup_finite' (E := F) K
  exact ⟨Ramification.artinConductor_eq_add T.Integers (F.Carrier ≃ₐ[K] F.Carrier)
      i q hi hiq hq,
    Ramification.swanConductor_eq_add T.Integers (F.Carrier ≃ₐ[K] F.Carrier)
      i q hi hiq hq⟩

end Padic

end Langlands.Ramification
