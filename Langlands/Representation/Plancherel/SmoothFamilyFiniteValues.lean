import Langlands.Representation.Plancherel.SmoothFamilyPrescribedValues

/-! # Finite parameter isolation in the existing smooth product-induced sections -/

noncomputable section

open scoped NNReal
open Langlands.HarishChandraSchwartz

namespace Langlands.Plancherel

universe uG uI uV uJ uS

section Torus

variable {J : Type*} [Fintype J]
  {S : Type*} [Group S] [Finite S]
  (τ : S →* (J → Circle)) (hτ : Function.Injective τ)

include hτ in
/-- A smooth stabilizer-invariant scalar which is one at a specified parameter
and zero at finitely many parameters in different stabilizer orbits. -/
theorem exists_smoothFiniteTorusFunction_invariant_finiteValues
    (Z : Set (J → Circle)) (hZ : Z.Finite) (z₀ : J → Circle)
    (hsep : ∀ z ∈ Z, ∀ s : S, z * τ s ≠ z₀) :
    ∃ φ : (J → Circle) → ℂ, IsSmoothFiniteTorusFunction φ ∧
      (∀ s z, φ (z * τ s) = φ z) ∧ φ z₀ = 1 ∧ ∀ z ∈ Z, φ z = 0 := by
  classical
  let _ : Fintype S := Fintype.ofFinite S
  let _ : Finite Z := hZ.to_subtype
  let bad : Set (J → Circle) := Set.range (fun x : Z × S => x.1.val * τ x.2)
  let W := bad ∪ Set.range (fun s : S => z₀ * τ s)
  have hW : W.Finite := (Set.finite_range _).union (Set.finite_range _)
  obtain ⟨p, hp, hp1, hp0⟩ := exists_isSmoothFiniteTorusFunction_lagrange W hW z₀
  refine ⟨fun z => ∑ s : S, p (z * τ s), ?_, ?_, ?_, ?_⟩
  · exact isSmoothFiniteTorusFunction_sum_mul_const Finset.univ τ hp
  · intro t z
    refine Fintype.sum_equiv (Equiv.mulLeft t) _ _ fun s => ?_
    change p (z * τ t * τ s) = p (z * τ (t * s))
    rw [map_mul, mul_assoc]
  · change (∑ s : S, p (z₀ * τ s)) = 1
    rw [Fintype.sum_eq_single (1 : S)]
    · simpa only [map_one, mul_one] using hp1
    · intro s hs
      apply hp0
      · exact Or.inr ⟨s, rfl⟩
      · intro he
        apply hs
        apply hτ
        rw [map_one]
        exact mul_left_cancel (he.trans (mul_one z₀).symm)
  · intro z hz
    apply Finset.sum_eq_zero
    intro s _
    exact hp0 _ (Or.inl ⟨(⟨z, hz⟩, s), rfl⟩) (hsep z hz s)

end Torus

/-- Finite smooth interpolation on distinct orbits of an injective finite
translation group. The following theorem proves this proposition. -/
def SmoothInvariantFiniteInterpolationStatement : Prop :=
  ∀ (J : Type uJ) [Fintype J] (S : Type uS) [Group S] [Finite S]
    (τ : S →* (J → Circle)), Function.Injective τ →
    ∀ (Z : Set (J → Circle)), Z.Finite → ∀ z₀ : J → Circle,
      (∀ z ∈ Z, ∀ s : S, z * τ s ≠ z₀) →
      ∃ φ : (J → Circle) → ℂ, IsSmoothFiniteTorusFunction φ ∧
        (∀ s z, φ (z * τ s) = φ z) ∧ φ z₀ = 1 ∧ ∀ z ∈ Z, φ z = 0

theorem smoothInvariantFiniteInterpolation :
    SmoothInvariantFiniteInterpolationStatement.{uJ, uS} :=
  fun _ _ _ _ _ τ hτ Z hZ z₀ hsep =>
    exists_smoothFiniteTorusFunction_invariant_finiteValues τ hτ Z hZ z₀ hsep

section Sections

open Langlands.Aubert.General Langlands.Induction

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  {J : Type uJ} (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  [LocallyCompactSpace G] {P U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G))
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  [Fintype J] [Finite (unitaryClassTwistStabilizer ν (Quotient.mk _ π))]

/-- Prescribe one actual product-induced fiber value and zero values at
finitely many parameter fibers in different stabilizer orbits, on the
existing coherent smooth orbit-section space and its own torus coordinates. -/
theorem exists_mem_productInducedSmoothOrbitSections_finiteValues
    (Z : Set (J → Circle)) (hZ : Z.Finite) (z₀ : J → Circle)
    (hsep : ∀ z ∈ Z, ∀ s : unitaryClassTwistStabilizer ν (Quotient.mk _ π),
      z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s ≠ z₀)
    (w : productInducedCoefficientObject h hU
      (π.obj.twist (unitaryTorusParameter ν e z₀).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z₀)))) :
    ∃ q ∈ productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK,
      q (unitaryOrbitParameterRepresentative ν π e z₀) = w ∧
        ∀ z ∈ Z, q (unitaryOrbitParameterRepresentative ν π e z) = 0 := by
  obtain ⟨q, hq, hq0⟩ :=
    exists_mem_productInducedSmoothOrbitSections_eval_eq ν π e h hU K hP hK hν hr hPK z₀ w
  obtain ⟨φ, hφ, hinv, hφ0, hφZ⟩ := exists_smoothFiniteTorusFunction_invariant_finiteValues
    (unitaryStabilizerTorusHom ν e (Quotient.mk _ π))
    (unitaryStabilizerTorusHom_injective ν e _) Z hZ z₀ hsep
  obtain ⟨q', hq', heq⟩ :=
    exists_mem_productInducedSmoothOrbitSections_smul ν π e h hU K hP hK hν hr hPK hφ hinv hq
  refine ⟨q', hq', ?_, ?_⟩
  · rw [heq, hφ0, one_smul, hq0]
  · intro z hz
    rw [heq, hφZ z hz, zero_smul]

end Sections

end Langlands.Plancherel
