import Langlands.Shimura.Unitary.HarrisSmallLevels
import Langlands.Shimura.Unitary.DefinitePositivity

/-!
# Sufficiently small levels for Harris's definite group

`HarrisSufficientlySmall σ hn vℓ vp L` says that the away level `K^{ℓ,p} = L` is sufficiently small
in Harris's sense (1999, p.310): (4.5) holds for every pair of compact `K_ℓ` and `C_p`. Smaller
levels stay sufficiently small (`HarrisSufficientlySmall.mono`). For an involution of the second
kind with the definite signature at every real place (`HasDefiniteSignature`), every compact open
level contains a compact open sufficiently small one
(`SecondKindInvolution.exists_harrisSufficientlySmall`).
-/

noncomputable section

open Langlands.Global
open scoped NumberField

set_option autoImplicit false

universe u v w

namespace Langlands.Shimura

namespace DefiniteForms

variable {A : Type w} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]

variable {σ} in
/-- (4.5) passes to smaller away levels. -/
theorem DividingLevelFree.mono_right {n : ℕ} {hn : n ≠ 0} {U : Subgroup (σ.DividingPoints n)}
    {L L' : Subgroup (σ.PrimeToPoints n)} (h : DividingLevelFree σ n hn U L) (hL : L' ≤ L) :
    DividingLevelFree σ n hn U L' := by
  intro g u hgu
  apply h g u
  obtain ⟨x, hx, k, hk, e⟩ := DoubleCoset.eq.1 hgu
  exact DoubleCoset.eq.2 ⟨x, hx, k, splitLevel_mono le_rfl hL hk, e⟩

variable {ℓ p : ℕ} (hn : ℓ * p ≠ 0) (vℓ : {v : FinitePlace ℚ // (ℓ : 𝓞 ℚ) ∈ v.asIdeal})
  (vp : {v : FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal})

/-- Harris's smallness of the away level `K^{ℓ,p} = L` (1999, p.310): `K_ℓ × C_p` acts without
fixed points on `GJ(ℚ) \ GJ(A_f) / K^{ℓ,p}` for every pair of compact `K_ℓ` and `C_p`. -/
def HarrisSufficientlySmall (L : Subgroup (σ.PrimeToPoints (ℓ * p))) : Prop :=
  ∀ (Kℓ : Subgroup (σ.Points (FiniteCompletion ℚ vℓ.1)))
    (Cp : Subgroup (σ.Points (FiniteCompletion ℚ vp.1))),
    IsCompact (Kℓ : Set (σ.Points (FiniteCompletion ℚ vℓ.1))) →
    IsCompact (Cp : Set (σ.Points (FiniteCompletion ℚ vp.1))) →
    HarrisDividingLevelFree σ (ℓ * p) hn (ellPlace p vℓ) (primePlace ℓ vp) Kℓ Cp L

variable {σ hn vℓ vp}

/-- Smaller away levels stay sufficiently small. -/
theorem HarrisSufficientlySmall.mono {L L' : Subgroup (σ.PrimeToPoints (ℓ * p))}
    (h : HarrisSufficientlySmall σ hn vℓ vp L) (hL : L' ≤ L) :
    HarrisSufficientlySmall σ hn vℓ vp L' :=
  fun Kℓ Cp hKℓ hCp => DividingLevelFree.mono_right (h Kℓ Cp hKℓ hCp) hL

/-- For a positive involution of a nonzero algebra and distinct primes `ℓ`, `p`, every compact
open `L₀ ≤ σ(A_f^{ℓp})` contains a compact open sufficiently small level. -/
theorem exists_harrisSufficientlySmall [Nontrivial A] (hℓ : ℓ.Prime) (hp : p.Prime) (hℓp : ℓ ≠ p)
    (hpos : (σ.baseChange ℝ).IsPositive) {L₀ : Subgroup (σ.PrimeToPoints (ℓ * p))}
    (hL₀o : IsOpen (L₀ : Set (σ.PrimeToPoints (ℓ * p))))
    (hL₀c : IsCompact (L₀ : Set (σ.PrimeToPoints (ℓ * p)))) :
    ∃ L ≤ L₀, IsOpen (L : Set (σ.PrimeToPoints (ℓ * p))) ∧
      IsCompact (L : Set (σ.PrimeToPoints (ℓ * p))) ∧ HarrisSufficientlySmall σ hn vℓ vp L :=
  exists_harrisDividingLevelFree hℓ hp hℓp hn hpos hL₀o hL₀c

end DefiniteForms

namespace SecondKindInvolution

variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [_root_.Algebra.IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {σ : SecondKindInvolution E K A} {n : ℕ}

/-- **Harris's sufficiently small levels exist for the definite group.** Let `σ` be an involution
of the second kind on a nonzero algebra `A`, finite over `E`, with the definite signature at every
real place. For distinct primes `ℓ`, `p`, every compact open `L₀ ≤ GJ(A_f^{ℓp})` contains a compact
open level `K^{ℓ,p}` such that Harris's (4.5) holds for every pair of compact `K_ℓ` and `C_p`. -/
theorem exists_harrisSufficientlySmall [Module.Finite E A] [Nontrivial A]
    (h : HasDefiniteSignature σ n) {ℓ p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hℓp : ℓ ≠ p)
    (hn : ℓ * p ≠ 0) (vℓ : {v : FinitePlace ℚ // (ℓ : 𝓞 ℚ) ∈ v.asIdeal})
    (vp : {v : FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal})
    {L₀ : Subgroup (σ.rationalInvolution.PrimeToPoints (ℓ * p))}
    (hL₀o : IsOpen (L₀ : Set (σ.rationalInvolution.PrimeToPoints (ℓ * p))))
    (hL₀c : IsCompact (L₀ : Set (σ.rationalInvolution.PrimeToPoints (ℓ * p)))) :
    letI : Module.Finite ℚ A := Module.Finite.trans E A
    ∃ L ≤ L₀, IsOpen (L : Set (σ.rationalInvolution.PrimeToPoints (ℓ * p))) ∧
      IsCompact (L : Set (σ.rationalInvolution.PrimeToPoints (ℓ * p))) ∧
      DefiniteForms.HarrisSufficientlySmall σ.rationalInvolution hn vℓ vp L := by
  let : Module.Finite ℚ A := Module.Finite.trans E A
  exact DefiniteForms.exists_harrisSufficientlySmall hℓ hp hℓp
    (isPositive_of_hasDefiniteSignature h) hL₀o hL₀c

end SecondKindInvolution

end Langlands.Shimura
