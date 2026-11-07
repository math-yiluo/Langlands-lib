import Langlands.LocalFactor.RankOneStabilityStatement
import Langlands.LocalFactor.Abelian.LocalAnalysisHelpers
import Langlands.LocalFactor.Abelian.GaussDual
import Langlands.HarmonicAnalysis.PadicAdditiveCharacterSelfDuality
import Langlands.HarmonicAnalysis.PadicPrincipalUnitCharacterExtensionProof
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

noncomputable section

open MeasureTheory
open scoped Topology WithZero

namespace Langlands.LocalFactor.RankOneStability

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology

open PadicAbelian HarmonicAnalysis.AdditiveSelfDuality

/-- The low-conductor range preserves the ramified conductor and the two L factors. -/
theorem conductor_and_L (χ : Character) (ha : 2 ≤ T.multiplicativeConductor χ)
    (η : Character) (hη : 2 * T.multiplicativeConductor η ≤ T.multiplicativeConductor χ) :
    T.multiplicativeConductor (χ * η) = T.multiplicativeConductor χ ∧
    rationalLFactor T χ = 1 ∧ rationalLFactor T (χ * η) = 1 ∧
    ∀ s : ℂ, lFactor T χ s = 1 ∧ lFactor T (χ * η) s = 1 := by
  have hlt : T.multiplicativeConductor η < T.multiplicativeConductor χ := by omega
  have hc : ConductorAt T (χ * η) (T.multiplicativeConductor χ) := by
    simpa only [max_eq_left hlt.le] using conductorAt_mul_of_ne T χ η
      (T.multiplicativeConductor χ) (T.multiplicativeConductor η)
      ((conductorAt_iff T χ _).mpr rfl) ((conductorAt_iff T η _).mpr rfl) (by omega)
  have he := (conductorAt_iff T (χ * η) _).mp hc
  have hn : T.multiplicativeConductor χ ≠ 0 := by omega
  refine ⟨he.symm, ?_, ?_, ?_⟩
  · simp [rationalLFactor, lPolynomial, hn]
  · simp [rationalLFactor, lPolynomial, ← he, hn]
  · intro s
    simp [lFactor, lFactorAt, ← he, hn]

end Langlands.LocalFactor.RankOneStability

namespace Langlands.PadicField.TopologicalData

open HarmonicAnalysis HarmonicAnalysis.AdditiveSelfDuality

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology

/-- Finite-level self-duality for a character defined only on the lattice. -/
theorem exists_parameter_lattice_character (ψ : AdditiveCharacter)
    (k M : ℤ) (χ : AddChar (T.additiveLattice M) ℂ)
    (hχ : ∀ x : T.additiveLattice M, (x : F.Carrier) ∈ T.additiveLattice k → χ x = 1) :
    letI := T.topology
    ∃ a : F.Carrier, ∀ (x : F.Carrier) (hx : x ∈ T.additiveLattice M), χ ⟨x, hx⟩ = ψ.complex (a * x) := by
  let _ := T.topology
  have : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    have := T.localField
    infer_instance
  set n := T.additiveConductor ψ with hn
  -- The finite groups `B = L_M / L_k` and `A = L_(n-k) / L_(n-M)`.
  let G := T.additiveLattice M
  let K := (T.additiveLattice k).addSubgroupOf G
  let G' := T.additiveLattice (n - k)
  let K' := (T.additiveLattice (n - M)).addSubgroupOf G'
  have hopen : ∀ (i j : ℤ), IsOpen (((T.additiveLattice i).addSubgroupOf
      (T.additiveLattice j)) : Set (T.additiveLattice j)) := by
    intro i j
    rw [AddSubgroup.coe_addSubgroupOf]
    exact (T.isOpen_additiveLattice i).preimage continuous_subtype_val
  have hcompact : ∀ j : ℤ, CompactSpace (T.additiveLattice j) :=
    fun j => isCompact_iff_compactSpace.mp (T.isCompact_additiveLattice j)
  let _ : Fintype (G ⧸ K) := @Fintype.ofFinite _ (by
    have := hcompact M
    exact AddSubgroup.quotient_finite_of_isOpen K (hopen k M))
  let _ : Fintype (G' ⧸ K') := @Fintype.ofFinite _ (by
    have := hcompact (n - k)
    exact AddSubgroup.quotient_finite_of_isOpen K' (hopen (n - M) (n - k)))
  -- The characters `x ↦ ψ(a x)` of `L_M` for `a ∈ L_(n-k)` descend to `B`.
  let φ : G' → AddChar G ℂ := fun a => (ψ.complex.mulShift a.val).compAddMonoidHom G.subtype
  have hφ : ∀ (a : G') (x : G), φ a x = ψ.complex (a.val * x.val) := fun a x => rfl
  have hφK : ∀ (a : G') (x : G), x ∈ K → φ a x = 1 := by
    intro a x hx
    rw [hφ]
    apply T.complex_eq_one_of_mem_conductor ψ
    have h := T.mul_mem_additiveLattice_add a.property (AddSubgroup.mem_addSubgroupOf.mp hx)
    rwa [sub_add_cancel] at h
  let Φ₀ : G' → AddChar (G ⧸ K) ℂ := fun a => quotientAddChar K (φ a) (hφK a)
  have hΦ₀ : ∀ (a : G') (x : G), Φ₀ a (x : G ⧸ K) = ψ.complex (a.val * x.val) :=
    fun a x => rfl
  have hΦ₀K : ∀ a b : G', -a + b ∈ K' → Φ₀ a = Φ₀ b := by
    intro a b hab
    ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [hΦ₀, hΦ₀]
    have hd : (b.val - a.val) * x.val ∈ T.additiveLattice n := by
      have hm : b.val - a.val ∈ T.additiveLattice (n - M) := by
        have := AddSubgroup.mem_addSubgroupOf.mp hab
        simpa [sub_eq_neg_add] using this
      have h := T.mul_mem_additiveLattice_add hm x.property
      rwa [sub_add_cancel] at h
    have hb : b.val * x.val = a.val * x.val + (b.val - a.val) * x.val := by ring
    rw [hb, AddChar.map_add_eq_mul, T.complex_eq_one_of_mem_conductor ψ hd, mul_one]
  let Φ : G' ⧸ K' → AddChar (G ⧸ K) ℂ := fun q =>
    Quotient.liftOn' q Φ₀ (fun a b h => hΦ₀K a b (QuotientAddGroup.leftRel_apply.mp h))
  have hΦ : ∀ a : G', Φ (a : G' ⧸ K') = Φ₀ a := fun a => rfl
  have hinj : Function.Injective Φ := by
    intro q q' hqq'
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective q'
    rw [hΦ, hΦ] at hqq'
    apply (QuotientAddGroup.eq).mpr
    rw [AddSubgroup.mem_addSubgroupOf]
    have hann : ∀ x ∈ T.additiveLattice M, ψ.complex ((b.val - a.val) * x) = 1 := by
      intro x hx
      have h := congrArg (fun c : AddChar (G ⧸ K) ℂ => c ((⟨x, hx⟩ : G) : G ⧸ K)) hqq'
      simp only [hΦ₀] at h
      have hb : b.val * x = a.val * x + (b.val - a.val) * x := by ring
      have h2 := congrArg (fun z => ψ.complex (-(a.val * x)) * z) h
      rw [hb, AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul,
        neg_add_cancel, AddChar.map_zero_eq_one, one_mul] at h2
      exact h2.symm
    have hmem := T.mem_additiveLattice_of_forall_complex_mul_eq_one ψ M _ hann
    simpa [sub_eq_neg_add] using hmem
  -- Both quotients have the same cardinality.
  have hcard : Nat.card (G' ⧸ K') = Nat.card (G ⧸ K) := by
    have hπ : T.uniformizer ^ (M + k - n) ≠ 0 := by
      apply zpow_ne_zero
      apply T.discreteValuation.ne_zero_iff.mp
      rw [T.discreteValuation_uniformizer]
      exact WithZero.exp_ne_zero
    have hord : T.ord (T.uniformizer ^ (M + k - n)) = M + k - n := by
      rw [T.ord_zpow, T.ord_uniformizer, mul_one]
    have hinjm : Function.Injective (AddMonoidHom.mulLeft (T.uniformizer ^ (M + k - n))) :=
      mul_right_injective₀ hπ
    have h := AddSubgroup.relIndex_map_map_of_injective (T.additiveLattice k)
      (T.additiveLattice M) hinjm
    rw [T.map_mulLeft_additiveLattice hπ, T.map_mulLeft_additiveLattice hπ, hord] at h
    have h1 : k - (M + k - n) = n - M := by ring
    have h2 : M - (M + k - n) = n - k := by ring
    rw [h1, h2] at h
    exact h
  have hbij : Function.Bijective Φ := by
    rw [Fintype.bijective_iff_injective_and_card, AddChar.card_eq]
    refine ⟨hinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard
  -- `χ` restricted to `L_M` descends to `B` and lies in the image.
  let χB : AddChar (G ⧸ K) ℂ := quotientAddChar K χ
    (fun x hx => hχ x (AddSubgroup.mem_addSubgroupOf.mp hx))
  obtain ⟨q, hq⟩ := hbij.2 χB
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
  refine ⟨a.val, fun x hx => ?_⟩
  have h := congrArg (fun c : AddChar (G ⧸ K) ℂ => c ((⟨x, hx⟩ : G) : G ⧸ K)) hq
  exact h.symm

end Langlands.PadicField.TopologicalData
