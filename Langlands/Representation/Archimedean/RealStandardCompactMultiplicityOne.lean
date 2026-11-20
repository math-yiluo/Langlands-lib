import Langlands.Representation.Archimedean.RealCompactBlockBasis
import Langlands.Representation.Archimedean.RealCompactFunctional
import Langlands.Representation.Archimedean.RealTemperedCommutantReduction

/-!
# Compact coefficient multiplicity one for real standard modules

The sign and Fourier equations on the orthogonal group are expressed in the
complex coordinates of the induction blocks.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealStandardCompactMultiplicityOne

open Langlands.LocalFactor.Archimedean
open RealCompactBlockBasis RealCompactWitnessExtension RealBlockFourierFinite
  PrincipalSeriesExtension GramFormula
open RealCompactRows (flip_inl flip_inr)
open RealCompactFunctional (V act gain gainScalar oneSign prod_oneSign_pow
  flipMatrix flipMatrix_eq_permMatrix
  FlipInvariant GainCovariant ElementaryGainCovariant FourierVanishing)
open RealTemperedCommutantReduction

variable {n : ℕ} {ds : List RealBlock}
variable {D : Type*} [AddCommGroup D] [Module ℂ D]

local notation "O(" n ")" => Matrix.unitaryGroup (Fin n) ℝ

/-- The least absolute mode of a nonzero-weight induction block. -/
def threshold (p : Pair n ds) : ℕ := p.datum.weight.natAbs + 1

private theorem below_threshold (p : Pair n ds) (j : ℤ) :
    j.natAbs < threshold p - 1 ↔ |j| < |p.datum.weight| := by
  simp only [threshold, Nat.add_sub_cancel, Int.abs_eq_natAbs, Int.ofNat_lt]

/-- The left diagonal sign on a singleton row. -/
def parity (i : Singleton n ds) : ℕ :=
  (RealBlockPosition.realPositionSign ds i.val).val

private theorem gain_one : gain (1 : Pair n ds → ℂ) (1 : Singleton n ds → ℂ) = 1 := by
  funext i
  rcases i with ⟨p, b⟩ | i <;> rfl

variable (Φ : Representation ℂ (Matrix (Rows n ds) (Rows n ds) ℂ) D)

private theorem flipMatrix_false :
    flipMatrix (β := Pair n ds) (γ := Singleton n ds) (fun _ => false) = 1 := by
  have h : RealCompactRows.flip (β := Pair n ds) (γ := Singleton n ds) (fun _ => false) = 1 := by
    ext i
    rcases i with ⟨p, b⟩ | i <;> simp
  rw [flipMatrix, h, map_one]

private theorem compactMatrix_rotation_eq (hRank : realRank ds = n)
    (p : Pair n ds) (θ : ℝ) :
    compactMatrix hRank (compactBlockRotation n p.val θ) =
      RealCompactFunctional.rotation (γ := Singleton n ds) p θ := by
  rw [compactMatrix_rotation, RealCompactFunctional.rotation]
  exact congrArg Matrix.diagonal (funext fun i => by
    rcases i with ⟨q, b⟩ | i <;> rfl)

private theorem signs_of_standardFunctional (hRank : realRank ds = n) (ℓ : D →ₗ[ℂ] ℂ)
    (hℓ : IsStandardFunctional ds (Φ.comp (compactMatrix hRank)) ℓ)
    (ε δ : Pair n ds → Bool) (τ : Singleton n ds → Bool) (x : D) :
    ℓ (Φ (Matrix.diagonal (gain (fun p => if ε p then -1 else 1)
          (fun i => if τ i then -1 else 1)) * flipMatrix δ) x) =
      gainScalar threshold parity (fun p => if ε p then -1 else 1)
        (fun i => if τ i then -1 else 1) * ℓ x := by
  have h := hℓ.1 (signParameters hRank ε δ τ) x
  have hg : signGain (fun i => (signParameters hRank ε δ τ i : ℝ)) =
      gain (fun p => if ε p then -1 else 1) (fun i => if τ i then -1 else 1) := by
    funext i
    have he := congrFun (signGain_signParameters hRank ε δ τ) i
    rcases i with ⟨p, b⟩ | i <;> exact he
  rw [MonoidHom.comp_apply,
    compactMatrix_signDiagonal hRank _ (RealCompactRows.flip δ)
      (by simpa only [signFlip_signParameters] using flip_inl δ) (flip_inr δ),
    hg, ← flipMatrix_eq_permMatrix, signCharacter_signParameters] at h
  exact h

private theorem isStandardFunctional_of_conditions (hRank : realRank ds = n) (ℓ : D →ₗ[ℂ] ℂ)
    (hFlip : ∀ δ x, ℓ (Φ (flipMatrix δ) x) = ℓ x)
    (hGain : ∀ (a : Pair n ds → ℂ) (d : Singleton n ds → ℂ) (x : D),
      ℓ (Φ (Matrix.diagonal (gain a d)) x) = gainScalar threshold parity a d * ℓ x)
    (hFourier : ∀ (p : Pair n ds) (j : ℤ), j.natAbs < threshold p - 1 → ∀ x : D,
      coeff j (fun θ => ℓ (Φ (RealCompactFunctional.rotation p θ) x)) = 0) :
    IsStandardFunctional ds (Φ.comp (compactMatrix hRank)) ℓ := by
  constructor
  · intro a x
    let δ := signFlip hRank (fun i => (a i : ℝ))
    have h : signGain (ds := ds) (fun i => (a i : ℝ)) =
        gain (fun p : Pair n ds => signReal (a p.val))
          (fun i : Singleton n ds => signReal (a i.val)) := by
      funext i
      rcases i with ⟨p, b⟩ | i <;> rfl
    rw [MonoidHom.comp_apply,
      compactMatrix_signDiagonal hRank _ (RealCompactRows.flip δ) (flip_inl δ) (flip_inr δ),
      h, ← flipMatrix_eq_permMatrix, signCharacter_eq hRank, map_mul, Module.End.mul_apply,
      hGain, hFlip]
    rfl
  · intro k d hk j hj x
    have hk' : k + 1 < n := hRank ▸ realInducedBlockAt_lt hk
    let p : Pair n ds := ⟨⟨k, by omega⟩, by simp [hk]⟩
    have hd : p.datum = d := Option.some.inj (p.induced_at.symm.trans hk)
    change coeff j (fun θ => ℓ (Φ (compactMatrix hRank (compactBlockRotation n p.val θ)) x)) = 0
    simp_rw [compactMatrix_rotation_eq]
    exact hFourier p j ((below_threshold p j).mpr (hd ▸ hj)) x

private theorem conditions_of_isStandardFunctional (hRank : realRank ds = n) (ℓ : D →ₗ[ℂ] ℂ)
    (hℓ : IsStandardFunctional ds (Φ.comp (compactMatrix hRank)) ℓ) :
    (∀ δ x, ℓ (Φ (flipMatrix δ) x) = ℓ x) ∧
    (∀ (p : Pair n ds) (x : D),
      ℓ (Φ (Matrix.diagonal (gain (oneSign p) 1)) x) =
        (-1) ^ threshold p * ℓ x) ∧
    (∀ (i : Singleton n ds) (x : D),
      ℓ (Φ (Matrix.diagonal (gain 1 (oneSign i))) x) =
        (-1) ^ parity i * ℓ x) ∧
    (∀ (p : Pair n ds) (j : ℤ), j.natAbs < threshold p - 1 → ∀ x : D,
      coeff j (fun θ => ℓ (Φ (RealCompactFunctional.rotation p θ) x)) = 0) := by
  have hSigns := signs_of_standardFunctional Φ hRank ℓ hℓ
  have hIdentity := flipMatrix_false (n := n) (ds := ds)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro δ x
    simpa [gainScalar, show (fun _ : Pair n ds => (1 : ℂ)) = 1 from rfl,
      show (fun _ : Singleton n ds => (1 : ℂ)) = 1 from rfl, gain_one] using
      hSigns (fun _ => false) δ (fun _ => false) x
  · intro p x
    have h : (fun q : Pair n ds => if decide (q = p) then (-1 : ℂ) else 1) = oneSign p := by
      funext q
      simp [oneSign]
    have hSign := hSigns (fun q => decide (q = p)) (fun _ => false) (fun _ => false) x
    rw [h] at hSign
    simpa [hIdentity, gainScalar, prod_oneSign_pow,
      show (fun _ : Singleton n ds => (1 : ℂ)) = 1 from rfl] using
        hSign
  · intro i x
    have h : (fun j : Singleton n ds => if decide (j = i) then (-1 : ℂ) else 1) = oneSign i := by
      funext j
      simp [oneSign]
    have hSign := hSigns (fun _ => false) (fun _ => false) (fun j => decide (j = i)) x
    rw [h] at hSign
    simpa [hIdentity, gainScalar, prod_oneSign_pow,
      show (fun _ : Pair n ds => (1 : ℂ)) = 1 from rfl] using
        hSign
  · intro p j hj x
    have h := hℓ.2 _ _ p.induced_at j ((below_threshold p j).mp hj) x
    simpa only [MonoidHom.comp_apply, compactMatrix_rotation_eq] using h

private theorem exists_scalarVector_of_functional [LinearOrder (Rows n ds)]
    (hRank : realRank ds = n) (ℓ : V (@threshold n ds) (@parity n ds) →ₗ[ℂ] ℂ)
    (hne : ℓ ≠ 0) (hFlip : FlipInvariant (@threshold n ds) (@parity n ds) ℓ)
    (hGain : GainCovariant (@threshold n ds) (@parity n ds) ℓ)
    (hFourier : FourierVanishing (@threshold n ds) (@parity n ds) ℓ)
    (hline : ∀ ℓ' : V (@threshold n ds) (@parity n ds) →ₗ[ℂ] ℂ,
      FlipInvariant (@threshold n ds) (@parity n ds) ℓ' →
      ElementaryGainCovariant (@threshold n ds) (@parity n ds) ℓ' →
      FourierVanishing (@threshold n ds) (@parity n ds) ℓ' → ∃ c : ℂ, ℓ' = c • ℓ) :
    ∃ f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n), f ≠ 0 ∧
      ∀ E : Module.End ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
        (∀ k x, E (realStandardRep n ds k x) = realStandardRep n ds k (E x)) →
        ∃ c : ℂ, E f = c • f := by
  let Φ := act (@threshold n ds) (@parity n ds)
  let ρ := Φ.comp (compactMatrix hRank)
  refine exists_scalarVector_of_compactCoefficients ρ ℓ hRank
    (isStandardFunctional_of_conditions Φ hRank ℓ hFlip hGain hFourier) hne ?_ ?_
  · intro x
    exact ℓ.continuous_of_finiteDimensional.comp
      (CompoundMinorProduct.continuous_action (continuous_compactMatrix hRank) x)
  · intro ℓ' hℓ'
    obtain ⟨hFlip', hPair', hSingleton', hFourier'⟩ :=
      conditions_of_isStandardFunctional Φ hRank ℓ' hℓ'
    exact hline ℓ' hFlip' ⟨hPair', hSingleton'⟩ hFourier'

/-- The real standard module has a nonzero vector scaled by every compact intertwiner. -/
theorem realStandardExistsCompactScalarVector (n : ℕ) (ds : List RealBlock)
    (hRank : realRank ds = n) :
    ∃ f : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n), f ≠ 0 ∧
      ∀ E : Module.End ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
        (∀ k x, E (realStandardRep n ds k x) = realStandardRep n ds k (E x)) →
        ∃ c : ℂ, E f = c • f := by
  let : LinearOrder (Rows n ds) :=
    LinearOrder.lift' (placement hRank) (placement hRank).injective
  obtain ⟨ℓ, hne, hFlip, hGain, hFourier, hline⟩ :=
    RealCompactFunctional.exists_functional (@threshold n ds) (@parity n ds)
      (fun p => Nat.zero_lt_succ p.datum.weight.natAbs)
      (fun i => Nat.le_of_lt_succ (RealBlockPosition.realPositionSign ds i.val).isLt)
  exact exists_scalarVector_of_functional hRank ℓ hne hFlip hGain hFourier hline

/-- The orthogonal action on the compound-minor coefficient model. -/
def compactSeedRep [LinearOrder (Rows n ds)] (hRank : realRank ds = n) :
    Representation ℂ (O(n)) (V (@threshold n ds) (@parity n ds)) :=
  (act (@threshold n ds) (@parity n ds)).comp (compactMatrix hRank)

/-- A compact intertwiner from the coefficient model with Lie-generating image
forces all simultaneous compact and Lie endomorphisms to be scalar. -/
theorem hasScalarCommutant_of_compactCyclicMap [LinearOrder (Rows n ds)]
    (hRank : realRank ds = n) (A : V (@threshold n ds) (@parity n ds) →ₗ[ℂ] KF n ds)
    (hA : ∀ k x, A (compactSeedRep hRank k x) = realStandardRep n ds k (A x))
    (hgen : ∀ W : Submodule ℂ (KF n ds), (∀ x, A x ∈ W) →
      (∀ Z, ∀ x ∈ W, realStandardLie n ds Z x ∈ W) → W = ⊤) :
    HasScalarCommutant n ds := by
  intro E hK hLie
  let ρ := compactSeedRep hRank
  let ev := kFiniteEval (realStandardModule n ds) 1
  obtain ⟨ℓ, _, _, _, _, hline⟩ :=
    RealCompactFunctional.exists_functional (@threshold n ds) (@parity n ds)
      (fun p => Nat.zero_lt_succ p.datum.weight.natAbs)
      (fun i => Nat.le_of_lt_succ (RealBlockPosition.realPositionSign ds i.val).isLt)
  have hform (B : V (@threshold n ds) (@parity n ds) →ₗ[ℂ] KF n ds)
      (hB : ∀ k x, B (ρ k x) = realStandardRep n ds k (B x)) :
      ∃ a : ℂ, ev.comp B = a • ℓ := by
    obtain ⟨hFlip, hPair, hSingle, hFourier⟩ :=
      conditions_of_isStandardFunctional _ hRank _ (evaluation_isStandardFunctional ρ B hB)
    exact hline _ hFlip ⟨hPair, hSingle⟩ hFourier
  have hEA (k : O(n)) (x : V (@threshold n ds) (@parity n ds)) :
      (E.comp A) (ρ k x) = realStandardRep n ds k ((E.comp A) x) := by
    simp only [LinearMap.comp_apply, ρ, hA, hK]
  obtain ⟨a, ha⟩ := hform A hA
  obtain ⟨b, hb⟩ := hform (E.comp A) hEA
  by_cases ha0 : a = 0
  · have hA0 : A = 0 := by
      refine compactIntertwiner_ext ρ hA (by simp) ?_
      simpa only [ev, ha0, zero_smul, LinearMap.comp_zero] using ha
    have hBot : (⊥ : Submodule ℂ (KF n ds)) = ⊤ :=
      hgen ⊥ (by simp [hA0]) (by simp)
    refine ⟨0, fun x => ?_⟩
    have hx : x ∈ (⊥ : Submodule ℂ (KF n ds)) := hBot ▸ Submodule.mem_top
    have hx0 : x = 0 := by simpa using hx
    rw [hx0, map_zero, smul_zero]
  · let c := b / a
    have hcA (k : O(n)) (x : V (@threshold n ds) (@parity n ds)) :
        (c • A) (ρ k x) = realStandardRep n ds k ((c • A) x) := by
      simp only [LinearMap.smul_apply, ρ, hA, map_smul]
    have he : E.comp A = c • A := by
      apply compactIntertwiner_ext ρ hEA hcA
      change ev.comp (E.comp A) = ev.comp (c • A)
      rw [LinearMap.comp_smul, ha, hb, smul_smul, div_mul_cancel₀ b ha0]
    let W : Submodule ℂ (KF n ds) := LinearMap.ker (E - c • LinearMap.id)
    have hW (x : KF n ds) : x ∈ W ↔ E x = c • x := by
      simp [W, sub_eq_zero]
    have hTop := hgen W (fun x => (hW _).mpr (DFunLike.congr_fun he x))
      (fun Z x hx => (hW _).mpr (by rw [hLie, (hW x).mp hx, map_smul]))
    exact ⟨c, fun x => (hW x).mp (hTop.symm ▸ Submodule.mem_top)⟩

end Langlands.Archimedean.RealStandardCompactMultiplicityOne
