import Langlands.Geometry.Analytic.QuasiEtaleActionLift.SpectralRoot
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.FiniteBanachBounds
import Langlands.Geometry.Analytic.GeneralizedAffinoid.SpectrumIdealCriterionProof
import Mathlib.RingTheory.Etale.StandardEtale

/-! # Nearby lifts through a standard étale presentation -/

noncomputable section

universe u v w z t

namespace Langlands.Analytic.BoundedAlgHom

open BanachSpectrum Polynomial

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem exists_unit_of_spectral_sub_bound (B : PresentedAffinoidAlgebra K)
    (e : Bˣ) (b : B) {M η : ℝ} (hη : 0 ≤ η) (hsmall : η * M < 1)
    (he : SpectralBound (↑e⁻¹ : B) M) (hb : SpectralBound (b - ↑e) η) :
    ∃ w : Bˣ, (w : B) = b ∧ SpectralBound ((↑w⁻¹ : B) - ↑e⁻¹) (M * M * η) := by
  have hmul (p : BanachSpectrum B) : p (e : B) * p (↑e⁻¹ : B) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have he0 (p : BanachSpectrum B) : p (e : B) ≠ 0 :=
    (B.isUnit_iff_forall_spectrum_ne_zero _).mp e.isUnit p
  have hbval (p : BanachSpectrum B) : p b = p (e : B) := by
    have hlt : p (b - (e : B)) < p (e : B) := by
      apply lt_of_mul_lt_mul_right (a := p (↑e⁻¹ : B)) _ (apply_nonneg p.toMulRingSeminorm _)
      rw [hmul p]
      exact (mul_le_mul (hb p) (he p) (apply_nonneg p.toMulRingSeminorm _) hη).trans_lt hsmall
    simpa only [sub_add_cancel] using
      (p.isNonarchimedean (K := K)).add_eq_right_of_lt
        (map_neg_eq_map p.toMulRingSeminorm) hlt
  obtain ⟨w, hw⟩ := (B.isUnit_iff_forall_spectrum_ne_zero b).mpr
    (fun p => (hbval p).symm ▸ he0 p)
  have hwinv (p : BanachSpectrum B) : p (↑w⁻¹ : B) = p (↑e⁻¹ : B) := by
    apply mul_left_cancel₀ (he0 p)
    rw [← hbval p, ← hw, ← map_mul, Units.mul_inv, map_one, hw, hbval p, hmul p]
  have hwprod : (↑w⁻¹ : B) * b = 1 := by rw [← hw, Units.inv_mul]
  have hdiff : (↑w⁻¹ : B) - ↑e⁻¹ = ↑w⁻¹ * ↑e⁻¹ * ((e : B) - b) := by
    rw [mul_sub]
    congr 1
    · rw [mul_assoc, Units.inv_mul, mul_one]
    · rw [mul_right_comm, hwprod, one_mul]
  have hback : SpectralBound ((e : B) - b) η := by
    rw [← neg_sub]
    exact hb.neg
  refine ⟨w, hw, fun p => ?_⟩
  rw [hdiff, map_mul, map_mul, hwinv p]
  have hpinv := apply_nonneg p.toMulRingSeminorm (↑e⁻¹ : B)
  exact mul_le_mul
    (mul_le_mul (he p) (he p) hpinv (hpinv.trans (he p)))
    (hback p) (apply_nonneg p.toMulRingSeminorm _) (mul_self_nonneg M)

private theorem eq_mul_inv_pow_of_mul_pow_eq {C : Type*} [CommRing C] (e : Cˣ)
    (n : ℕ) {x y : C} (h : x * (e : C) ^ n = y) :
    x = y * (↑e⁻¹ : C) ^ n := by
  rw [← h, mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]

variable {R : Type v} {S : Type w} {A : Type z} {T : Type t}
  [NormedCommRing R] [NormedAlgebra K R] [NormedCommRing S] [NormedAlgebra K S]
  [NormedCommRing A] [NormedAlgebra K A] [CommRing T] [Algebra R T]

/-- A bounded map out of a finite Banach algebra that factors through a standard
étale presentation can be lifted along any spectrally close base map, with
arbitrary prescribed spectral control on finitely many elements. The coefficient
tests work uniformly after bounded specialization of the reference algebra. -/
theorem exists_spectralLift_of_standardEtalePresentation
    (f : BoundedAlgHom K R S) (hf : f.IsFiniteBanach)
    (P : StandardEtalePresentation R T) (i : S →+* T)
    (hi : ∀ r, i (f r) = algebraMap R T r)
    (j : BoundedAlgHom K S A) (k : T →+* A) (hk : ∀ s, k (i s) = j s)
    (E : Finset S) {ε : ℝ} (hε : 0 < ε) :
    ∃ (D : Finset R) (δ : ℝ), 0 < δ ∧
      ∀ (B : PresentedAffinoidAlgebra K) (l : BoundedAlgHom K A B) (b : BoundedAlgHom K R B),
        (∀ r ∈ D, SpectralBound (b r - l (j (f r))) δ) →
        ∃ b' : BoundedAlgHom K S B, b'.comp f = b ∧
          ∀ s ∈ E, SpectralBound (b' s - l (j s)) ε := by
  classical
  let a := j.comp f
  let x := k P.x
  have hka : k.comp (algebraMap R T) = a.toAlgHom.toRingHom := by
    ext r
    change k (algebraMap R T r) = j (f r)
    rw [← hi, hk]
  have hEval (p : Polynomial R) : k (p.aeval P.x) = p.eval₂ a.toAlgHom.toRingHom x := by
    rw [aeval_def, hom_eval₂, hka]
  have hx : P.f.eval₂ a.toAlgHom.toRingHom x = 0 := by
    rw [← hEval, P.hasMap.1, map_zero]
  let dT : Tˣ := P.hasMap.isUnit_derivative_f.unit
  have hdT : (dT : T) = P.f.derivative.aeval P.x := P.hasMap.isUnit_derivative_f.unit_spec
  let d := k (↑dT⁻¹ : T)
  have hd : d * P.f.derivative.eval₂ a.toAlgHom.toRingHom x = 1 := by
    rw [← hEval]
    change k (↑dT⁻¹ : T) * k (P.f.derivative.aeval P.x) = 1
    rw [← map_mul, ← hdT, Units.inv_mul, map_one]
  let e : Aˣ := Units.map k.toMonoidHom P.hasMap.2.unit
  have he : (e : A) = P.g.eval₂ a.toAlgHom.toRingHom x := by
    change k (↑P.hasMap.2.unit : T) = P.g.eval₂ a.toAlgHom.toRingHom x
    rw [IsUnit.unit_spec, hEval]
  choose num n hn using fun s : S => P.exists_mul_aeval_x_g_pow_eq_aeval_x (i s)
  have hj (s : S) : j s =
      (num s).eval₂ a.toAlgHom.toRingHom x * (↑e⁻¹ : A) ^ n s := by
    apply eq_mul_inv_pow_of_mul_pow_eq e
    simpa only [map_mul, map_pow, hk, hEval, he] using congrArg k (hn s)
  let X₀ : Bool → A := fun i => if i then ↑e⁻¹ else x
  let evalRep (s : S) (B : PresentedAffinoidAlgebra K) (_ : BoundedAlgHom K A B)
      (b : BoundedAlgHom K R B) (y : Bool → B) :=
    (num s).eval₂ b.toAlgHom.toRingHom (y false) * (y true) ^ n s
  have hRep (s : S) : HasSpectralControlAt a X₀ (j s) (evalRep s) := by
    rw [hj s]
    exact (HasSpectralControlAt.eval₂ (num s) (HasSpectralControlAt.argument false)).mul
      ((HasSpectralControlAt.argument true).pow (n s))
  obtain ⟨Drep, δrep, hδrep, hrep⟩ :=
    HasSpectralControlAt.finite E (fun _ => ε) (fun s => j s) evalRep
      (fun _ _ => hε) (fun s _ => hRep s)
  let M := max 1 ‖(↑e⁻¹ : A)‖
  have hM : 0 < M := zero_lt_one.trans_le (le_max_left _ _)
  let η := min ((1 / 2) / M) (δrep / (M * M))
  have hη : 0 < η := lt_min (div_pos (by norm_num) hM) (div_pos hδrep (mul_pos hM hM))
  have hsmall : η * M < 1 :=
    ((le_div_iff₀ hM).mp (min_le_left _ _)).trans_lt (by norm_num)
  have hηrep : M * M * η ≤ δrep := by
    rw [mul_comm, ← le_div_iff₀ (mul_pos hM hM)]
    exact min_le_right _ _
  have hg : HasSpectralControlAt a X₀ (e : A)
      (fun _ _ b y => P.g.eval₂ b.toAlgHom.toRingHom (y false)) :=
    he ▸ HasSpectralControlAt.eval₂ P.g (HasSpectralControlAt.argument false)
  obtain ⟨Dg, δg, hδg, hg'⟩ := hg η hη
  obtain ⟨Droot, δroot, hδroot, hroot⟩ :=
    PresentedAffinoidAlgebra.exists_spectralRootNear a P.f x d hx hd (lt_min hδrep hδg)
  refine ⟨Droot ∪ (Dg ∪ Drep), min δroot (min δg δrep), lt_min hδroot (lt_min hδg hδrep),
    fun B l b hb => ?_⟩
  have hbroot (r : R) (hr : r ∈ Droot) : SpectralBound (b r - l (a r)) δroot :=
    (hb r (Finset.mem_union_left _ hr)).mono (min_le_left _ _)
  have hbg (r : R) (hr : r ∈ Dg) : SpectralBound (b r - l (a r)) δg :=
    (hb r (Finset.mem_union_right _ (Finset.mem_union_left _ hr))).mono
      ((min_le_right _ _).trans (min_le_left _ _))
  have hbrep (r : R) (hr : r ∈ Drep) : SpectralBound (b r - l (a r)) δrep :=
    (hb r (Finset.mem_union_right _ (Finset.mem_union_right _ hr))).mono
      ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨y, hy, hyclose⟩ := hroot B l b hbroot
  let eB : Bˣ := Units.map l.toAlgHom.toMonoidHom e
  have heB : (eB : B) = l e := rfl
  have heBinv : (↑eB⁻¹ : B) = l (↑e⁻¹ : A) := rfl
  let y₀ : Bool → B := fun i => if i then ↑eB⁻¹ else y
  have hy₀ (i : Bool) : SpectralBound (y₀ i - l (X₀ i)) δg := by
    cases i
    · exact hyclose.mono (min_le_right _ _)
    · change SpectralBound ((↑eB⁻¹ : B) - l (↑e⁻¹ : A)) δg
      rw [heBinv, sub_self]
      exact spectralBound_zero hδg.le
  let v := P.g.eval₂ b.toAlgHom.toRingHom y
  have hv : SpectralBound (v - (eB : B)) η := by
    rw [heB]
    exact hg' B l b y₀ hbg hy₀
  have hMbound : SpectralBound (↑eB⁻¹ : B) M := by
    rw [heBinv]
    exact fun p => ((BanachSpectrum.comap l.toBoundedRingHom p).le_norm _).trans (le_max_right _ _)
  obtain ⟨w, hw, hwinv⟩ := exists_unit_of_spectral_sub_bound B eB v hη.le hsmall hMbound hv
  let : Algebra R B := b.toAlgHom.toRingHom.toAlgebra
  have hMap : P.P.HasMap y := ⟨hy, ⟨w, hw⟩⟩
  let φ : T →ₐ[R] B := (P.P.lift y hMap).comp P.equivRing.toAlgHom
  have hφx : φ P.x = y := by simp [φ]
  have hφf (r : R) : φ (i (f r)) = b r := by
    rw [hi]
    exact φ.commutes r
  let β : S →ₐ[K] B :=
    { φ.toRingHom.comp i with
      commutes' := fun c => by
        change φ (i (algebraMap K S c)) = algebraMap K B c
        rw [← f.toAlgHom.commutes c]
        exact (hφf _).trans (b.toAlgHom.commutes c) }
  have hβ : β.comp f.toAlgHom = b.toAlgHom := AlgHom.ext hφf
  let b' := ofFiniteBanachTriangle f hf b β hβ
  refine ⟨b', ofFiniteBanachTriangle_comp f hf b β hβ, fun s hs => ?_⟩
  let y₁ : Bool → B := fun i => if i then ↑w⁻¹ else y
  have hy₁ (i : Bool) : SpectralBound (y₁ i - l (X₀ i)) δrep := by
    cases i
    · exact hyclose.mono (min_le_left _ _)
    · change SpectralBound ((↑w⁻¹ : B) - l (↑e⁻¹ : A)) δrep
      rw [← heBinv]
      exact hwinv.mono hηrep
  have hφeval (p : Polynomial R) : φ (p.aeval P.x) = p.eval₂ b.toAlgHom.toRingHom y := by
    rw [← aeval_algHom_apply, hφx, aeval_def]
    rfl
  have hb' : b' s = evalRep s B l b y₁ := by
    change φ (i s) = (num s).eval₂ b.toAlgHom.toRingHom y * (↑w⁻¹ : B) ^ n s
    apply eq_mul_inv_pow_of_mul_pow_eq w
    simpa only [map_mul, map_pow, hφeval, hw, v] using congrArg φ (hn s)
  rw [hb']
  exact hrep B l b y₁ hbrep hy₁ s hs

end Langlands.Analytic.BoundedAlgHom
