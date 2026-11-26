import Langlands.BaseChange.TwistedCharacter.AdjointFixedSpace

/-! # Algebraic multiplicity of one at a σ-regular element -/

noncomputable section

namespace Langlands.BaseChange

open JacquetLanglands Matrix Module

universe u v

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) E
local notation "G" => GeneralLinear n E

private theorem exists_mul_idempotent_ne_zero {R : Type*} [CommRing R]
    [IsArtinianRing R] [IsReduced R] {a : R} (ha : a ≠ 0) :
    ∃ b, IsIdempotentElem (a * b) ∧ a * b ≠ 0 := by
  let S (i : MaximalSpectrum R) := R ⧸ i.asIdeal
  let (i : MaximalSpectrum R) : Field (S i) := IsArtinianRing.fieldOfSubtypeIsMaximal R i
  let e : R ≃+* ∀ i, S i := IsArtinianRing.equivPi R
  let b := e.symm fun i => (e a i)⁻¹
  have hb (i : MaximalSpectrum R) : e b i = (e a i)⁻¹ :=
    congrFun (e.apply_symm_apply _) i
  refine ⟨b, ?_, ?_⟩
  · apply e.injective
    funext i
    simp only [map_mul, Pi.mul_apply, hb]
    by_cases h : e a i = 0 <;> simp [h]
  · intro hab
    apply ha
    have h : a * (a * b) = a := by
      apply e.injective
      funext i
      simp only [map_mul, Pi.mul_apply, hb]
      by_cases hi : e a i = 0 <;> simp [hi]
    simpa only [hab, mul_zero] using h.symm

variable [CharZero F]

private theorem tracePairing_separatesFixed_of_norm (σ : E ≃ₐ[F] E) {l : ℕ}
    (hE : IsCyclicAlgebra σ l) (δ : G) (γ : GeneralLinear n F) (hγ : IsRegularSemisimple γ)
    (hnorm : cyclicNorm σ l δ = baseChange F E n γ) (X : twistedAdjointFixed σ δ)
    (hX : ∀ Y : twistedAdjointFixed σ δ, adjointTracePairing F E n X.val Y.val = 0) :
    X = 0 := by
  let _ : Module.Finite F E := hE.1
  let A := AdjoinRoot γ.val.charpoly
  let _ : Module.Finite F A := (AdjoinRoot.powerBasis' γ.val.charpoly_monic).finite
  let _ : IsArtinianRing A := IsArtinianRing.of_finite F A
  let _ : IsReduced A :=
    (Ideal.isRadical_iff_quotient_reduced _).1
      (isRadical_iff_span_singleton.1 hγ.squarefree.isRadical)
  let e := twistedAdjointFixedEquivRootOfNorm σ hE δ γ hγ hnorm
  obtain ⟨a, rfl⟩ := e.surjective X
  by_contra hne
  have ha : a ≠ 0 := fun h => hne (by rw [h, map_zero])
  obtain ⟨b, habIdem, hab⟩ := exists_mul_idempotent_ne_zero ha
  let ev := charpolyRootEvaluation γ.val
  obtain ⟨w, hw⟩ := regularCyclicBasis F n γ.val hγ
  have hev := charpolyRootEvaluation_injective γ.val w hw
  let T := Matrix.toLinAlgEquiv' (ev (a * b))
  have hT : IsIdempotentElem T := (habIdem.map ev).map Matrix.toLinAlgEquiv'
  have htr : Matrix.trace (ev (a * b)) ≠ 0 := by
    intro hz
    have hT₀ : T = 0 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff hT).1 (by
      change LinearMap.trace F (Fin n → F) (ev (a * b)).toLin' = 0
      rw [Matrix.trace_toLin'_eq]
      exact hz)
    have hM : ev (a * b) = 0 := by
      apply Matrix.toLinAlgEquiv'.injective
      simpa only [T, map_zero] using hT₀
    exact hab (hev (hM.trans (map_zero ev).symm))
  have hz := hX (e b)
  simp only [adjointTracePairing_apply, e, twistedAdjointFixedEquivRootOfNorm_apply] at hz
  have hmul : (ev a).map (algebraMap F E) * (ev b).map (algebraMap F E) =
      (ev (a * b)).map (algebraMap F E) := by
    change ((algebraMap F E).mapMatrix (ev a)) * ((algebraMap F E).mapMatrix (ev b)) =
      (algebraMap F E).mapMatrix (ev (a * b))
    rw [map_mul, map_mul]
  change Algebra.trace F E
    (Matrix.trace ((ev a).map (algebraMap F E) * (ev b).map (algebraMap F E))) = 0 at hz
  rw [hmul, ← AddMonoidHom.map_trace (algebraMap F E), Algebra.trace_algebraMap,
    nsmul_eq_mul] at hz
  have hn : (Module.finrank F E : F) ≠ 0 := Nat.cast_ne_zero.mpr (hE.2.1.symm ▸ hE.pos).ne'
  exact mul_ne_zero hn htr hz

private theorem tracePairing_separatesFixed (σ : E ≃ₐ[F] E) {l : ℕ}
    (hE : IsCyclicAlgebra σ l) (δ : G) (hδ : IsSigmaRegular σ l δ)
    (X : twistedAdjointFixed σ δ)
    (hX : ∀ Y : twistedAdjointFixed σ δ, adjointTracePairing F E n X.val Y.val = 0) :
    X = 0 := by
  obtain ⟨γ, ⟨x, hx⟩, hγ⟩ := hδ
  let d := x⁻¹ * δ * entrywiseAut σ n x
  let e := twistedAdjointFixedConjEquiv σ x δ
  have hd : cyclicNorm σ l d = baseChange F E n γ := by
    dsimp [d]
    rw [cyclicNorm_twistedConj, hE.pow_eq_one, entrywiseAut_one_apply, hx]
  have he : e X = 0 := tracePairing_separatesFixed_of_norm σ hE d γ hγ hd (e X) (by
    intro Z
    obtain ⟨Y, rfl⟩ := e.surjective Z
    let C := twistedMatrixConj (1 : E ≃ₐ[F] E) x⁻¹
    change adjointTracePairing F E n (C X.val) (C Y.val) = 0
    exact (adjointTracePairing_preserved _ _ _ _).trans (hX Y))
  exact e.injective (he.trans (map_zero e).symm)

/-- At a σ-regular point the algebraic multiplicity of the adjoint eigenvalue `1` is `n`. -/
theorem rootMultiplicity_twistedMatrixConj_of_sigmaRegular (σ : E ≃ₐ[F] E) {l : ℕ}
    (hE : IsCyclicAlgebra σ l) (δ : G) (hδ : IsSigmaRegular σ l δ) :
    haveI : Module.Finite F E := hE.1
    (LinearMap.charpoly (twistedMatrixConj σ δ).toLinearMap).rootMultiplicity 1 = n := by
  have : Module.Finite F E := hE.1
  let T : End F Mat := (twistedMatrixConj σ δ).toLinearMap
  let D : End F Mat := T - 1
  let B := adjointTracePairing F E n
  have hfix (Z : Mat) : D Z = 0 ↔ Z ∈ twistedAdjointFixed σ δ := by
    rw [mem_twistedAdjointFixed]
    exact sub_eq_zero
  have horth (Z : Mat) (Y : twistedAdjointFixed σ δ) : B (D Z) Y.val = 0 := by
    have h := adjointTracePairing_preserved σ δ Z Y.val
    rw [(mem_twistedAdjointFixed σ).1 Y.property] at h
    change B (T Z - Z) Y.val = 0
    rw [LinearMap.BilinForm.sub_left, show B (T Z) Y.val = B Z Y.val from h, sub_self]
  have hstep (Z : Mat) (hZ : D (D Z) = 0) : D Z = 0 := by
    have hx := tracePairing_separatesFixed σ hE δ hδ ⟨D Z, (hfix _).1 hZ⟩ (horth Z)
    exact congrArg Subtype.val hx
  have hpow (k : ℕ) (Z : Mat) (hZ : (D ^ k) Z = 0) : D Z = 0 := by
    induction k generalizing Z with
    | zero =>
      change Z = 0 at hZ
      rw [hZ, map_zero]
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply] at hZ
      exact hstep Z (ih (D Z) hZ)
  have hmax : T.maxGenEigenspace (1 : F) = twistedAdjointFixed σ δ := by
    apply le_antisymm
    · intro Z hZ
      obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace T 1 Z).1 hZ
      exact (hfix Z).1 (hpow k Z (by simpa only [one_smul, D] using hk))
    · exact T.genEigenspace_le_maximal 1 1
  change T.charpoly.rootMultiplicity 1 = n
  rw [← LinearMap.finrank_maxGenEigenspace_eq, hmax]
  exact finrank_twistedAdjointFixed_of_sigmaRegular σ hE δ hδ

end Langlands.BaseChange
