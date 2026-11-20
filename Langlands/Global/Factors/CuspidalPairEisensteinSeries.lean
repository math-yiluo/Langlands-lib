import Langlands.Automorphic.CuspidalContragredientExistenceProof
import Langlands.Global.AdelicBlockDeterminantCharacter
import Langlands.Global.AdelicGLIwasawa
import Langlands.Global.GeneralLinearGlobalWhittaker
import Langlands.Group.GL.SingleBlock
import Langlands.Group.GL.TriangularParabolic
import Langlands.Representation.Shahidi.TwoBlocks
import Langlands.Topology.CompactNormCharacter

/-! # Eisenstein series induced from an actual cuspidal pair -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global.CuspidalPairEisenstein

open Automorphic AdelicBlockParabolic AdelicBlockDeterminantCharacter
  PrimitiveAdelicHeight NumberField
open scoped CategoryTheory.MonObj NNReal

/-- The standard upper parabolic with ordered blocks of sizes `r + 1` and `t + 1`. -/
abbrev blockShape (r t : ℕ) : GeneralLinear.BlockShape (r + t + 2) :=
  (Shahidi.twoBlocks (r + 1) (t + 1) (Nat.succ_pos _) (Nat.succ_pos _)).rankCast (by omega)

variable {F : Type u} [Field F] [NumberField F] {r t : ℕ}

/-- An actual realization of the full-operator contragredient of `T`. -/
def dualRealization [CompactSpace (AdeleQuotient F)] (T : CuspidalOperatorRealization F t) :
    CuspidalOperatorRealization F t :=
  (cuspidalContragredientExistence F t T).choose

/-- Smooth, right `K`-finite normalized sections of the actual cuspidal tensor.
In the compact picture, the Levi slices are finite linear combinations of products of
realized cusp forms. The slices at general adelic points are their smooth translates. -/
def IsSection [CompactSpace (AdeleQuotient F)]
    (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t)
    (φ : AdelicGL F (r + t + 2) → ℂ) : Prop :=
  (∀ b : FiniteAdelicGL F (r + t + 2),
    (fun a => φ (AdelicGL.pair F (r + t + 2) a b)) ∈
      ArchimedeanGL.smoothFunctions F (r + t + 2)) ∧
  (∃ J : OpenSubgroup (FiniteAdelicGL F (r + t + 2)),
    ∀ (j : J) (g : AdelicGL F (r + t + 2)),
      φ (g * AdelicGL.ofFinite F (r + t + 2) j.val) = φ g) ∧
  FiniteDimensional ℂ (Submodule.span ℂ (Set.range
    (fun k : standardCompact F (r + t + 2) => fun g => φ (g * k.val)))) ∧
  (∀ (n : (blockShape r t).unipotentSubgroup (Adeles F)) (g : AdelicGL F (r + t + 2)),
    φ (n.val * g) = φ g) ∧
  ∀ k : standardCompact F (r + t + 2),
    (fun m : FullLevi F (blockShape r t) =>
      ((leviHalfCharacter F (blockShape r t) m : ℂˣ) : ℂ)⁻¹ *
        φ ((blockShape r t).leviEmbedding (Adeles F) m * k.val)) ∈
      Submodule.span ℂ (Set.range fun v : T.Space × (dualRealization T').Space =>
        fun m : FullLevi F (blockShape r t) =>
          ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous v.1)
            (m (0 : Fin 2)) *
          ContinuousRationalFunctions.evaluate F (t + 1)
            ((dualRealization T').realization.toContinuous v.2) (m (1 : Fin 2)))

private theorem exists_parabolic_factor (F : Type u) [Field F] [NumberField F] (r t : ℕ)
    (g : AdelicGL F (r + t + 2)) :
    ∃ p : Full F (blockShape r t), ∃ k ∈ standardCompact F (r + t + 2), p.val * k = g := by
  obtain ⟨p, k, hg, hp, hk⟩ := exists_isStandardIwasawaFactorization F (r + t + 2) g
  exact ⟨⟨p, (blockShape r t).upperTriangularSubgroup_le_parabolic (Adeles F) hp⟩, k, hk,
    hg.symm⟩

/-- Shahidi's power `H(g)^s`. In a parabolic Iwasawa factorization `g = pk`, its
logarithm in the exponential is `s / (r + t + 2)` times `log δ_P(p)`. -/
def heightPower (F : Type u) [Field F] [NumberField F] (r t : ℕ)
    (s : ℂ) (g : AdelicGL F (r + t + 2)) : ℂ :=
  let p := (exists_parabolic_factor F r t g).choose
  Complex.exp (s / ((r + t + 2 : ℕ) : ℂ) *
    (Real.log ((parabolicCharacter F (blockShape r t) p : ℝ≥0) : ℝ) : ℂ))

/-- Any parabolic Iwasawa factorization computes the same twist. -/
theorem heightPower_eq (s : ℂ) {g : AdelicGL F (r + t + 2)}
    (p : Full F (blockShape r t)) {k : AdelicGL F (r + t + 2)}
    (hk : k ∈ standardCompact F (r + t + 2)) (hg : p.val * k = g) :
    heightPower F r t s g = Complex.exp (s / ((r + t + 2 : ℕ) : ℂ) *
      (Real.log ((parabolicCharacter F (blockShape r t) p : ℝ≥0) : ℝ) : ℂ)) := by
  let p₀ := (exists_parabolic_factor F r t g).choose
  obtain ⟨k₀, hk₀, hg₀⟩ := (exists_parabolic_factor F r t g).choose_spec
  change p₀.val * k₀ = g at hg₀
  let K := standardCompact F (r + t + 2)
  let J := K.comap ((blockShape r t).parabolic (Adeles F)).subtype
  let : T2Space (Adeles F) := adeles_t2Space F
  have hJ : IsCompact (J : Set (Full F (blockShape r t))) :=
    ((blockShape r t).isClosed_parabolic (Adeles F)).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_standardCompact F (r + t + 2))
  have hmem : p⁻¹ * p₀ ∈ J := by
    change p.val⁻¹ * p₀.val ∈ K
    have heq : p.val⁻¹ * p₀.val = k * k₀⁻¹ := calc
      p.val⁻¹ * p₀.val = p.val⁻¹ * (p₀.val * k₀) * k₀⁻¹ := by group
      _ = p.val⁻¹ * (p.val * k) * k₀⁻¹ := by rw [hg₀, hg]
      _ = k * k₀⁻¹ := by group
    rw [heq]
    exact K.mul_mem hk (K.inv_mem hk₀)
  let δ := parabolicCharacter F (blockShape r t)
  have hδ : δ (p⁻¹ * p₀) = 1 :=
    RankinSelberg.LastRowReduction.eq_one_of_isCompact δ.toMonoidHom δ.continuous J hJ hmem
  have heq : δ p₀ = δ p := by
    calc
      δ p₀ = δ (p * (p⁻¹ * p₀)) := by rw [mul_inv_cancel_left]
      _ = δ p := by rw [map_mul, hδ, mul_one]
  change Complex.exp (s / ((r + t + 2 : ℕ) : ℂ) * (Real.log ((δ p₀ : ℝ≥0) : ℝ) : ℂ)) = _
  rw [heq]

/-- The unconditional Eisenstein sum over `P(F) \ GL_(r+t+2)(F)`. -/
def eisensteinSeries (F : Type u) [Field F] [NumberField F] {r t : ℕ}
    (φ : AdelicGL F (r + t + 2) → ℂ) (s : ℂ) (g : AdelicGL F (r + t + 2)) : ℂ :=
  ∑' c : Quotient (QuotientGroup.rightRel ((blockShape r t).parabolic F)),
    let x := AdelicGL.rational F (r + t + 2) (Quotient.out c) * g
    φ x * heightPower F r t s x

/-- The generic Fourier coefficient at the identity, with normalized quotient Haar measure. -/
def coeff {r t : ℕ} (ψ : AddChar (Adeles F) ℂ)
    (φ : AdelicGL F (r + t + 2) → ℂ) (s : ℂ) : ℂ :=
  generalLinearWhittakerFunction F (r + t + 1) ψ (fun _ => 1)
    (fun g => eisensteinSeries F (r := r) (t := t) φ s
      (GeneralLinearGroupPoints.adelicEquiv F (r + t + 2) g)) 1

end Langlands.Global.CuspidalPairEisenstein
