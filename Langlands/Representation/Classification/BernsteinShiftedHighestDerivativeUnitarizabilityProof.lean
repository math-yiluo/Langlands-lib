import Langlands.Representation.Classification.BernsteinShiftedHighestDerivativeUnitarizabilityStatement
import Langlands.Representation.Derivative.MirabolicDerivativeVanishing
import Langlands.Representation.Derivative.MirabolicHighestDerivativeDescent
import Langlands.Representation.Derivative.MirabolicPhiMinusUnitarityProof
import Langlands.Representation.Derivative.RankCastCompat
import Langlands.Representation.Unitary.Restriction

/-!
# Unitarizability of the shifted highest derivative

Bernstein 1984, §7.4(ii): for an irreducible unitarizable `π` of `GL_N`, `N ≥ 1`, and a
highest derivative order `h`, `ν^(1/2) π^(h)` is unitarizable. Restrict `π` to `P_N` and
apply `Φ⁻` `h - 1` times, which keeps unitarizability (`mirabolicPhiMinusUnitarity`,
Bernstein 1984, §9.3(ii)). Highestness forces the radical to act trivially on the result
`τ`, so `Ψ⁻ τ` is the Levi restriction of `τ` twisted by `|det|^(-1/2)`, which the shift
`ν^(1/2)` cancels. See the paired Markdown.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Classification.ShiftedHighestDerivative

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis Derivative Derivative.Mirabolic
open Jacquet.Localization

universe uF uV uW uG

/-- A common character twist of isomorphic smooth representations keeps unitarizability. -/
theorem isUnitarizable_twist_of_iso {G : Type uG} [Group G] [TopologicalSpace G]
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G)) {A B : SmoothRep.{0, uG, uW} ℂ G}
    (e : A ≅ B) (hB : IsUnitarizable (B.twist χ hχ).representation) :
    IsUnitarizable (A.twist χ hχ).representation :=
  hB.of_injective (twistIntertwining χ (SmoothRep.equivOfIso e).toIntertwiningMap)
    (SmoothRep.equivOfIso e).toLinearEquiv.injective

section Steps

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- If the radical acts trivially on a unitarizable `X`, then `ν^(1/2) Ψ⁻ X` is
unitarizable: it embeds in the Levi restriction of `X`. -/
theorem isUnitarizable_segmentFactor_psiMinus (n : ℕ) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uW} ℂ (mirabolic n F.Carrier),
      (∀ (u : radical n F.Carrier) (v : X),
        X.representation (u : mirabolic n F.Carrier) v = v) →
      IsUnitarizable X.representation →
      IsUnitarizable (T.segmentFactor ((Mirabolic.psiMinus T n).obj X) (1 / 2)).representation := by
  let := T.topology
  intro X hrad hX
  let f : Coinvariants X.representation (radical n F.Carrier) 1 →ₗ[ℂ] X :=
    lift X.representation (radical n F.Carrier) 1 LinearMap.id (fun u v => by
      rw [LinearMap.id_apply, LinearMap.id_apply, hrad u v, MonoidHom.one_apply, Units.val_one,
        one_smul])
  have hf : ∀ v : X, f (mk X.representation (radical n F.Carrier) 1 v) = v := fun _ => rfl
  have hc : ∀ g : GeneralLinear n F.Carrier,
      (T.determinantPowerCharacter n (1 / 2) g : ℂ) *
        (realPowerCharacter (T.determinantNorm n) (-(1 / 2 : ℝ)) g : ℂ) = 1 := by
    intro g
    rw [← Units.val_mul, ← MonoidHom.mul_apply, ← realPowerCharacter_add, add_neg_cancel,
      realPowerCharacter_zero, MonoidHom.one_apply, Units.val_one]
  refine (hX.comp (levi : GeneralLinear n F.Carrier →* mirabolic n F.Carrier)).of_injective
    { toLinearMap := f
      isIntertwining' := fun g => LinearMap.ext fun a => ?_ } ?_
  · obtain ⟨v, rfl⟩ := mk_surjective X.representation (radical n F.Carrier) 1 a
    change f ((T.determinantPowerCharacter n (1 / 2) g : ℂ) •
        ((realPowerCharacter (T.determinantNorm n) (-(1 / 2 : ℝ)) g : ℂ) •
          mk X.representation (radical n F.Carrier) 1 (X.representation (levi g) v))) =
      X.representation (levi g) (f (mk X.representation (radical n F.Carrier) 1 v))
    rw [smul_smul, hc, one_smul, hf, hf]
  · intro a a' h
    obtain ⟨v, rfl⟩ := mk_surjective X.representation (radical n F.Carrier) 1 a
    obtain ⟨v', rfl⟩ := mk_surjective X.representation (radical n F.Carrier) 1 a'
    change f _ = f _ at h
    rw [hf, hf] at h
    rw [h]

variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- A rank transport of `Φ⁻ X` is `Φ⁻` of the transported `X`, so a vanishing derivative
of `X` with one more `Φ⁻` step is a vanishing derivative of `Φ⁻ X`. -/
theorem subsingleton_rankCast_phiMinus {a n' i : ℕ} (h : a = n' + i)
    (h' : a + 1 = n' + (i + 1)) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uW} ℂ (mirabolic (a + 1) F.Carrier),
      Subsingleton ((mirabolicRankCast T h' ⋙ mirabolicDerivative T ψ n' (i + 1)).obj X) →
      Subsingleton ((mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n' i).obj
        ((Mirabolic.phiMinus T ψ a).obj X)) := by
  subst h
  exact fun _ hX => hX

/-- The induction on the number `j` of `Φ⁻` steps, given that `Φ⁻` preserves
unitarizability. -/
theorem shiftedDerivativeUnitarity_core
    (hΦ : letI := T.topology
      ∀ (m : ℕ) (X : SmoothRep.{0, uF, uW} ℂ (mirabolic (m + 1) F.Carrier)),
        IsUnitarizable X.representation →
          IsUnitarizable ((Mirabolic.phiMinus T ψ m).obj X).representation)
    (j : ℕ) :
    letI := T.topology
    ∀ (n : ℕ) (A : SmoothRep.{0, uF, uW} ℂ (mirabolic (n + j) F.Carrier)),
      (∀ (n' i : ℕ) (h : n + j = n' + i), n' < n →
        Subsingleton ((mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n' i).obj A)) →
      IsUnitarizable A.representation →
      IsUnitarizable
        (T.segmentFactor ((mirabolicDerivative T ψ n j).obj A) (1 / 2)).representation := by
  let := T.topology
  induction j with
  | zero =>
    intro n A hhigh hA
    have hrad : ∀ (u : radical n F.Carrier) (v : A),
        A.representation (u : mirabolic n F.Carrier) v = v := by
      cases n with
      | zero => exact radical_acts_trivially_zero T A
      | succ m =>
        refine radical_acts_trivially_of_phiMinus T ψ m A ?_
        refine subsingleton_of_forall_mirabolicDerivative T ψ m _ fun n' i h => ?_
        subst h
        exact hhigh n' (i + 1) rfl (by omega)
    exact isUnitarizable_segmentFactor_psiMinus T n A hrad hA
  | succ j ih =>
    intro n A hhigh hA
    exact ih n ((Mirabolic.phiMinus T ψ (n + j)).obj A)
      (fun n' i h hlt => subsingleton_rankCast_phiMinus T ψ h (by omega) A
        (hhigh n' (i + 1) (by omega) hlt))
      (hΦ (n + j) A hA)

/-- The core induction, after an arbitrary rank transport `N = n + j`. -/
theorem shiftedDerivativeUnitarity_cast
    (hΦ : letI := T.topology
      ∀ (m : ℕ) (X : SmoothRep.{0, uF, uW} ℂ (mirabolic (m + 1) F.Carrier)),
        IsUnitarizable X.representation →
          IsUnitarizable ((Mirabolic.phiMinus T ψ m).obj X).representation)
    {N n j : ℕ} (h : N = n + j) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uW} ℂ (mirabolic N F.Carrier),
      (∀ (n' i : ℕ) (h' : N = n' + i), n' < n →
        Subsingleton ((mirabolicRankCast T h' ⋙ mirabolicDerivative T ψ n' i).obj A)) →
      IsUnitarizable A.representation →
      IsUnitarizable (T.segmentFactor
        ((mirabolicRankCast T h ⋙ mirabolicDerivative T ψ n j).obj A) (1 / 2)).representation := by
  subst h
  exact shiftedDerivativeUnitarity_core T ψ hΦ j n

/-- `ν^(1/2) π^(h)` is unitarizable for a unitarizable `π` of `GL_(n+1)` and a highest
derivative order `h`, given that `Φ⁻` preserves unitarizability. -/
theorem isUnitarizable_shiftedHighestDerivative
    (hΦ : letI := T.topology
      ∀ (m : ℕ) (X : SmoothRep.{0, uF, uW} ℂ (mirabolic (m + 1) F.Carrier)),
        IsUnitarizable X.representation →
          IsUnitarizable ((Mirabolic.phiMinus T ψ m).obj X).representation)
    {n : ℕ} (π : letI := T.topology
      SmoothRep.{0, uF, uW} ℂ (GeneralLinear (n + 1) F.Carrier))
    (hπ : letI := T.topology; IsUnitarizable π.representation)
    (hd : letI := T.topology; GeneralLinearHighestDerivativeOrderData T ψ π) :
    letI := T.topology
    IsUnitarizable (T.segmentFactor
      ((generalLinearDerivative T ψ (n + 1) hd.order hd.le_rank).obj π) (1 / 2)).representation := by
  let := T.topology
  have hk : 0 < hd.order ∧ hd.order ≤ n + 1 := ⟨hd.positive, hd.le_rank⟩
  refine isUnitarizable_twist_of_iso _ _
    ((generalLinearRestrictionDerivativeIso T ψ n hd.order hk).app π).symm ?_
  refine shiftedDerivativeUnitarity_cast T ψ hΦ (mirabolic_rank_eq_of_order hk)
    ((generalLinearRestriction T n).obj π) (fun n' i h' hlt => ?_)
    (hπ.comp (mirabolic n F.Carrier).subtype)
  have hj : 0 < i + 1 ∧ i + 1 ≤ n + 1 := by omega
  have hsub := hd.higher_vanish (i + 1) hj.2 (by omega)
  have hsub' : Subsingleton ((mirabolicDerivativeOfOrder T ψ n (i + 1) hj).obj
      ((generalLinearRestriction T n).obj π)) :=
    (SmoothRep.equivOfIso
      ((generalLinearRestrictionDerivativeIso T ψ n (i + 1) hj).app π)).toLinearEquiv.injective.subsingleton
  exact subsingleton_rankCast_mirabolicDerivative_congr T ψ (mirabolic_rank_eq_of_order hj) h'
    (by omega) (by omega) _ hsub'

end Steps

end Langlands.Classification.ShiftedHighestDerivative

namespace Langlands.Classification

universe uF uV

/-- Bernstein 1984, §7.4(ii): unitarizability of the shifted highest derivative, given
that normalized `Φ⁻` preserves unitarizability. Irreducibility of `π` is not used. -/
theorem bernsteinShiftedHighestDerivativeUnitarizability_of_phiMinusUnitarity {p : ℕ}
    [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (hΦ : Derivative.MirabolicPhiMinusUnitarity.{uF, uV} F T) :
    BernsteinShiftedHighestDerivativeUnitarizability.{uF, uV} F T := by
  let := T.topology
  intro N hN ψ π _ hπ hd
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  exact ShiftedHighestDerivative.isUnitarizable_shiftedHighestDerivative T ψ (hΦ ψ) π hπ hd

/-- Bernstein 1984, §7.4(ii) (Tadic 1986, Theorem 2.5(iii), unitarizability part):
for an irreducible unitarizable `π` of `GL_N`, `N ≥ 1`, the shifted highest derivative
`ν^(1/2) π^(h)` is unitarizable. -/
theorem bernsteinShiftedHighestDerivativeUnitarizability {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    BernsteinShiftedHighestDerivativeUnitarizability.{uF, uV} F T :=
  bernsteinShiftedHighestDerivativeUnitarizability_of_phiMinusUnitarity F T
    (Derivative.Mirabolic.mirabolicPhiMinusUnitarity.{uF, uV} F T)

end Langlands.Classification
