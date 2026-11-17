import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitFiberIsolation
import Langlands.Representation.Plancherel.ProductInducedOrbitSections

/-! # Prescribed values and scalar multiplication for smooth equivariant families

Finite smooth equivariant families on the circle torus, and the coherent smooth orbit
sections of the actual normalized product induction built from them, can take any
prescribed value at a parameter point. They are stable under multiplication by smooth
scalar functions invariant under the stabilizer translations.
-/

noncomputable section

open scoped TensorProduct NNReal

namespace Langlands.Plancherel

universe uG uI uV uJ uS

section Families

variable {J : Type*} [Fintype J] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Multiplying a finite smooth family by a smooth scalar function gives a finite smooth
family. -/
theorem smul_mem_finiteSmoothFamilies {φ : (J → Circle) → ℂ}
    (hφ : IsSmoothFiniteTorusFunction φ) {F : (J → Circle) → V}
    (hF : F ∈ finiteSmoothFamilies J V) :
    (fun z => φ z • F z) ∈ finiteSmoothFamilies J V := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨f, v, rfl⟩ := hF
    refine Submodule.subset_span
      ⟨⟨φ * f.val, (smoothFiniteTorusFunctions J).mul_mem
        (show φ ∈ smoothFiniteTorusFunctions J from hφ) f.property⟩, v, ?_⟩
    funext z
    change φ z • (f.val z • v) = (φ z * f.val z) • v
    rw [mul_smul]
  | zero =>
    have h0 : (fun z => φ z • (0 : (J → Circle) → V) z) = 0 := by
      funext z
      simp
    rw [h0]
    exact (finiteSmoothFamilies J V).zero_mem
  | add F H _ _ hF hH =>
    have h1 : (fun z => φ z • (F + H) z) = (fun z => φ z • F z) + (fun z => φ z • H z) := by
      funext z
      simp [smul_add]
    rw [h1]
    exact (finiteSmoothFamilies J V).add_mem hF hH
  | smul c F _ hF =>
    have h1 : (fun z => φ z • (c • F) z) = c • (fun z => φ z • F z) := by
      funext z
      simp only [Pi.smul_apply]
      exact smul_comm _ _ _
    rw [h1]
    exact (finiteSmoothFamilies J V).smul_mem c hF

variable {S : Type*} [Group S] (τ : S →* (J → Circle)) (ρ : Representation ℂ S V)

/-- Multiplying an equivariant family by a smooth scalar function invariant under the
stabilizer translations gives an equivariant family. -/
theorem smul_mem_finiteSmoothEquivariantFamilies {φ : (J → Circle) → ℂ}
    (hφ : IsSmoothFiniteTorusFunction φ) (hinv : ∀ s z, φ (z * τ s) = φ z)
    {F : (J → Circle) → V} (hF : F ∈ finiteSmoothEquivariantFamilies J V τ ρ) :
    (fun z => φ z • F z) ∈ finiteSmoothEquivariantFamilies J V τ ρ := by
  refine ⟨smul_mem_finiteSmoothFamilies hφ hF.1, fun s z => ?_⟩
  change φ (z * τ s) • F (z * τ s) = ρ s (φ z • F z)
  rw [hinv, hF.2 s z, map_smul]

/-- **Prescribed values.** For a finite group acting through injective torus translations,
every vector is the value at a given parameter of some finite smooth equivariant family.
The family is `z ↦ ∑ₛ φ(z τ(s)⁻¹) • ρ(s) v` for a smooth Lagrange function `φ` equal to
`1` at the parameter and `0` at its other stabilizer translates. -/
theorem exists_mem_finiteSmoothEquivariantFamilies_eval_eq [Finite S]
    (hτ : Function.Injective τ) (z₀ : J → Circle) (v : V) :
    ∃ F ∈ finiteSmoothEquivariantFamilies J V τ ρ, F z₀ = v := by
  classical
  let _ : Fintype S := Fintype.ofFinite S
  obtain ⟨φ, hφ, hφ1, hφ0⟩ :=
    Langlands.HarishChandraSchwartz.exists_isSmoothFiniteTorusFunction_lagrange
      (Set.range fun s : S => z₀ * (τ s)⁻¹) (Set.finite_range _) z₀
  refine ⟨fun z => ∑ s : S, φ (z * (τ s)⁻¹) • ρ s v, ⟨?_, ?_⟩, ?_⟩
  · have hsum : (fun z => ∑ s : S, φ (z * (τ s)⁻¹) • ρ s v) =
        ∑ s : S, (fun z => φ (z * (τ s)⁻¹) • ρ s v) := by
      funext z
      simp [Finset.sum_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun s _ => Submodule.subset_span
      ⟨⟨fun z => φ (z * (τ s)⁻¹), (isSmoothFiniteTorusFunction_mul_const_iff φ _).mpr hφ⟩,
        ρ s v, rfl⟩
  · intro t z
    change ∑ s : S, φ (z * τ t * (τ s)⁻¹) • ρ s v =
      ρ t (∑ s : S, φ (z * (τ s)⁻¹) • ρ s v)
    rw [map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft t⁻¹) _ _ fun s => ?_
    change φ (z * τ t * (τ s)⁻¹) • ρ s v =
      ρ t (φ (z * (τ (t⁻¹ * s))⁻¹) • ρ (t⁻¹ * s) v)
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left, map_mul τ,
      map_inv, mul_inv_rev, inv_inv, mul_comm (τ s)⁻¹, ← mul_assoc]
  · change ∑ s : S, φ (z₀ * (τ s)⁻¹) • ρ s v = v
    rw [Fintype.sum_eq_single 1]
    · simp [hφ1]
    · intro s hs
      rw [hφ0 _ ⟨s, rfl⟩ ?_, zero_smul]
      intro h
      apply hs
      apply hτ
      have h' : (τ s)⁻¹ = 1 := by simpa using h
      rw [inv_eq_one.mp h', map_one]

/-- The prescribed-value property of finite smooth equivariant families, recorded as a
proposition. It is proved below by `exists_mem_finiteSmoothEquivariantFamilies_eval_eq`. -/
def SmoothEquivariantFamilyPrescribedValueStatement : Prop :=
  ∀ (J : Type uJ) [Fintype J] (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (S : Type uS) [Group S] [Finite S] (τ : S →* (J → Circle)) (ρ : Representation ℂ S V),
    Function.Injective τ → ∀ (z₀ : J → Circle) (v : V),
      ∃ F ∈ finiteSmoothEquivariantFamilies J V τ ρ, F z₀ = v

theorem smoothEquivariantFamilyPrescribedValue :
    SmoothEquivariantFamilyPrescribedValueStatement.{uV, uJ, uS} :=
  fun _ _ _ _ _ _ _ _ τ ρ hτ z₀ v => exists_mem_finiteSmoothEquivariantFamilies_eval_eq τ ρ hτ z₀ v

end Families

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
  [Fintype J]

omit [LocallyCompactSpace G] [Fintype J] in
/-- The stabilizer parameter homomorphism is injective. -/
theorem unitaryStabilizerTorusHom_injective
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) :
    Function.Injective (unitaryStabilizerTorusHom ν e ω) :=
  e.injective.comp Subtype.val_injective

/-- Every value in the actual induced fiber at a parameter is taken by a smooth family. -/
theorem exists_mem_productInducedSmoothFamilies_eval_eq
    [Finite (unitaryClassTwistStabilizer ν (Quotient.mk _ π))] (z₀ : J → Circle)
    (w : productInducedCoefficientObject h hU
      (π.obj.twist (unitaryTorusParameter ν e z₀).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z₀)))) :
    ∃ F ∈ productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π, F z₀ = w := by
  let R := productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
  let C := (productInducedCompactEquiv ν h K hP hK hν hr hU hPK
    (unitaryTorusParameter ν e z₀) π.obj).toLinearEquiv
  obtain ⟨F', hF', hF'z⟩ := exists_mem_finiteSmoothEquivariantFamilies_eval_eq
    (unitaryStabilizerTorusHom ν e (Quotient.mk _ π))
    (unitaryStabilizerCompactRepresentation ν h K hP hK hν hr π)
    (unitaryStabilizerTorusHom_injective ν e _) z₀ (C w)
  refine ⟨R.symm F', ?_, ?_⟩
  · change R (R.symm F') ∈ finiteSmoothEquivariantFamilies J _ _ _
    rw [R.apply_symm_apply]
    exact hF'
  · apply C.injective
    change R (R.symm F') z₀ = C w
    rw [R.apply_symm_apply, hF'z]

/-- Every value in the actual induced fiber of a parameter representative is taken by a
coherent smooth orbit section. -/
theorem exists_mem_productInducedSmoothOrbitSections_eval_eq
    [Finite (unitaryClassTwistStabilizer ν (Quotient.mk _ π))] (z₀ : J → Circle)
    (w : productInducedCoefficientObject h hU
      (π.obj.twist (unitaryTorusParameter ν e z₀).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z₀)))) :
    ∃ q ∈ productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK,
      q (unitaryOrbitParameterRepresentative ν π e z₀) = w := by
  obtain ⟨F, hF, hFz⟩ :=
    exists_mem_productInducedSmoothFamilies_eval_eq ν π e h hU K hP hK hν hr hPK z₀ w
  let E := productInducedSmoothOrbitFamilyEquiv ν π e h hU K hP hK hν hr hPK
  refine ⟨(E.symm ⟨F, hF⟩).val, (E.symm ⟨F, hF⟩).property, ?_⟩
  have hE := congrArg (fun H => H.val z₀) (E.apply_symm_apply ⟨F, hF⟩)
  exact hE.trans hFz

/-- Multiplying a coherent smooth orbit section, on parameter representatives, by a smooth
scalar function invariant under the stabilizer translations gives a coherent smooth orbit
section. -/
theorem exists_mem_productInducedSmoothOrbitSections_smul
    {φ : (J → Circle) → ℂ} (hφ : IsSmoothFiniteTorusFunction φ)
    (hinv : ∀ s z, φ (z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s) = φ z)
    {q : ProductInducedOrbitSections ν π h hU}
    (hq : q ∈ productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    ∃ q' ∈ productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK,
      ∀ z, q' (unitaryOrbitParameterRepresentative ν π e z) =
        φ z • q (unitaryOrbitParameterRepresentative ν π e z) := by
  let E := productInducedSmoothOrbitFamilyEquiv ν π e h hU K hP hK hν hr hPK
  let R := productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
  let F : productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π := E ⟨q, hq⟩
  have hF : F.val = fun z => q (unitaryOrbitParameterRepresentative ν π e z) := rfl
  let F' : ProductInducedTorusFamilies ν e h hU π.obj := fun z => φ z • F.val z
  have hF' : F' ∈ productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π := by
    change R F' ∈ finiteSmoothEquivariantFamilies J _ _ _
    have hRF' : R F' = fun z => φ z • R F.val z := by
      funext z
      exact map_smul (productInducedCompactEquiv ν h K hP hK hν hr hU hPK
        (unitaryTorusParameter ν e z) π.obj).toLinearEquiv (φ z) (F.val z)
    rw [hRF']
    exact smul_mem_finiteSmoothEquivariantFamilies _ _ hφ hinv F.property
  refine ⟨(E.symm ⟨F', hF'⟩).val, (E.symm ⟨F', hF'⟩).property, fun z => ?_⟩
  have hE := congrArg (fun H => H.val z) (E.apply_symm_apply ⟨F', hF'⟩)
  exact hE

end Sections

end Langlands.Plancherel
