import Langlands.Correspondence.HenniartUnramified.Concrete
import Langlands.Correspondence.HenniartNumericalReductionProof

/-! # Torsion numbers, breaks and Swan exponents through inertia types -/

noncomputable section

namespace Langlands.Henniart.Numerical

open Correspondence FiniteRepresentation FiniteRepresentation.SplitDegree Weil.Local
open VirtualRepresentation VirtualRepresentation.LocalWeil.Ramification

universe uF uW

section TwistAlgebra

variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

/-- Twists by two characters commute. -/
def twistCommEquiv (χ ψ : G →* ℂˣ) (ρ : Representation ℂ G V) :
    Representation.Equiv (Langlands.twist ψ (Langlands.twist χ ρ))
      (Langlands.twist χ (Langlands.twist ψ ρ)) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) fun g => by
    apply LinearMap.ext
    intro v
    change (ψ g : ℂ) • ((χ g : ℂ) • ρ g v) = (χ g : ℂ) • ((ψ g : ℂ) • ρ g v)
    rw [smul_comm]

/-- Twisting by a character and then by its inverse changes nothing. -/
def twistInvEquiv (χ : G →* ℂˣ) (ρ : Representation ℂ G V) :
    Representation.Equiv (Langlands.twist χ⁻¹ (Langlands.twist χ ρ)) ρ :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) fun g => by
    apply LinearMap.ext
    intro v
    change ((χ⁻¹ g : ℂˣ) : ℂ) • ((χ g : ℂ) • ρ g v) = ρ g v
    rw [smul_smul, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

/-- A twist stabilizer element of `ρ` stabilizes every twist of `ρ`. -/
def twistStabTransport (χ ψ : G →* ℂˣ) {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W}
    (e : Representation.Equiv (Langlands.twist χ ρ) ρ')
    (f : Representation.Equiv (Langlands.twist ψ ρ) ρ) :
    Representation.Equiv (Langlands.twist ψ ρ') ρ' :=
  (Langlands.twistEquiv ψ e.symm).trans
    ((twistCommEquiv χ ψ ρ).trans ((Langlands.twistEquiv χ f).trans e))

/-- Twist stabilizers of twist-equivalent representations agree. -/
theorem twist_stab_iff (χ ψ : G →* ℂˣ) {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W}
    (e : Representation.Equiv (Langlands.twist χ ρ) ρ') :
    Nonempty (Representation.Equiv (Langlands.twist ψ ρ) ρ) ↔
      Nonempty (Representation.Equiv (Langlands.twist ψ ρ') ρ') :=
  ⟨fun ⟨f⟩ => ⟨twistStabTransport χ ψ e f⟩,
    fun ⟨f⟩ => ⟨twistStabTransport χ⁻¹ ψ
      ((Langlands.twistEquiv χ⁻¹ e.symm).trans (twistInvEquiv χ ρ)) f⟩⟩

end TwistAlgebra

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Continuous irreducible representations of the local Weil group. -/
abbrev WeilObj : Type _ :=
  {A : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F) // A.IsContinuous ∧ A.IsIrreducible}

/-- The class of a continuous irreducible representation of rank `k + 1`. -/
def weilClassOf {k : ℕ} (A : WeilObj.{uF, uW} F) (h : A.1.rank = k + 1) :
    IrreducibleWeilClass.{uF, uW} F k.succPNat :=
  ⟨Quotient.mk _ A, h⟩

theorem weilClassOf_surjective {k : ℕ} (σ : IrreducibleWeilClass.{uF, uW} F k.succPNat) :
    ∃ (A : WeilObj.{uF, uW} F) (h : A.1.rank = k + 1), weilClassOf F A h = σ := by
  obtain ⟨c, hc⟩ := σ
  induction c using Quotient.inductionOn with
  | h A => exact ⟨A, hc, rfl⟩

/-- An unramified twist fixes the class exactly when it fixes a representative. -/
theorem weilUnramifiedTwist_weilClassOf {k : ℕ} (A : WeilObj.{uF, uW} F) (h : A.1.rank = k + 1)
    (z : ℂˣ) :
    weilUnramifiedTwist F k z (weilClassOf F A h) = weilClassOf F A h ↔
      Nonempty (Representation.Equiv
        (Langlands.twist (unramifiedCharacter (localDegree F) z).toMonoidHom A.1.representation)
        A.1.representation) :=
  Subtype.ext_iff.trans Quotient.eq

/-- Classes are equal exactly when representatives are isomorphic. -/
theorem weilClassOf_eq_iff {k : ℕ} (A B : WeilObj.{uF, uW} F) (hA : A.1.rank = k + 1)
    (hB : B.1.rank = k + 1) :
    weilClassOf F A hA = weilClassOf F B hB ↔
      Nonempty (Representation.Equiv A.1.representation B.1.representation) :=
  Subtype.ext_iff.trans Quotient.eq

/-- Orbit classes are equal exactly when representatives differ by an unramified twist. -/
theorem weilOrbit_eq_iff {k : ℕ} (A B : WeilObj.{uF, uW} F) (hA : A.1.rank = k + 1)
    (hB : B.1.rank = k + 1) :
    Weil.unramifiedOrbitClass (localDegree F) ⟨k.succPNat, weilClassOf F A hA⟩ =
        Weil.unramifiedOrbitClass (localDegree F) ⟨k.succPNat, weilClassOf F B hB⟩ ↔
      ∃ z : ℂˣ, Nonempty (Representation.Equiv
        (Langlands.twist (unramifiedCharacter (localDegree F) z).toMonoidHom B.1.representation)
        A.1.representation) := by
  rw [weilOrbitClass_eq_iff]
  refine exists_congr fun z => ?_
  exact Subtype.ext_iff.trans Quotient.eq

/-- The Swan exponent of a class in terms of the last break of a representative. -/
theorem hasWeilSwan_weilClassOf {k : ℕ} (A : WeilObj.{uF, uW} F) (h : A.1.rank = k + 1)
    (s : ℕ) :
    HasWeilSwan F (weilClassOf F A h) s ↔ (s : ℝ) = (k + 1 : ℕ) * lastBreak F A.1 :=
  hasWeilSwan_iff_rank_mul_lastBreak F _ A.1 rfl s

variable (φ : localWeilGroup F) (hφ : localDegree F φ = Multiplicative.ofAdd (1 : ℤ))

/-- The torsion number of a class is the period of any inertia type occurring in it. -/
theorem weilTorsionNumber_eq_period {k : ℕ} (A : WeilObj.{uF, uW} F) (h : A.1.rank = k + 1)
    (B : {B : FiniteRepresentation.{0, uF, uW} ℂ (weilSplit F φ hφ).inertia //
      (weilSplit F φ hφ).IsType B})
    (P : Representation.IntertwiningMap
      (A.1.representation.comp (weilSplit F φ hφ).inertia.subtype) B.1.representation)
    (hP : P ≠ 0) {m : ℕ}
    (hp : Function.minimalPeriod ((weilSplit F φ hφ).conjType 1)
      ((weilSplit F φ hφ).toClass B) = m + 1) :
    weilTorsionNumber F (weilClassOf F A h) = m + 1 := by
  obtain ⟨u, ⟨e⟩⟩ :=
    (weilStage F φ hφ m).twist_equiv_typeCoind B hp A.1.representation A.2.2 P hP
  have key : ∀ z : ℂˣ, weilUnramifiedTwist F k z (weilClassOf F A h) = weilClassOf F A h ↔
      z ∈ rootsOfUnity (m + 1) ℂ := by
    intro z
    rw [weilUnramifiedTwist_weilClassOf, twist_stab_iff _ _ e]
    exact ((weilStage F φ hφ m).typeCoind_twist_iff B hp z).trans (mem_rootsOfUnity _ _).symm
  unfold weilTorsionNumber
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  exact Complex.card_rootsOfUnity (m + 1)

/-- The last break of a coinduced representation is the break of its type. -/
theorem lastBreak_typeCoind {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {E : SplitDegree H} {m : ℕ} (S : Stage (weilSplit F φ hφ) E (m + 1))
    (B : {B : FiniteRepresentation.{0, uF, uW} ℂ (weilSplit F φ hφ).inertia //
      (weilSplit F φ hφ).IsType B})
    (hp : Function.minimalPeriod ((weilSplit F φ hφ).conjType 1)
      ((weilSplit F φ hφ).toClass B) = m + 1) :
    lastBreak F (FiniteRepresentation.of (S.typeCoind B hp)) =
      inertiaBreak F B.1.representation := by
  rw [lastBreak_eq_inertiaBreak]
  exact inertiaBreak_congr F fun v _ => S.typeCoind_trivial_iff B hp (upperGroup F v)

/-- Unramified twists do not change the last break. -/
theorem lastBreak_twist (A : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)) (z : ℂˣ) :
    lastBreak F (FiniteRepresentation.of
      (Langlands.twist (unramifiedCharacter (localDegree F) z).toMonoidHom A.representation)) =
      lastBreak F A := by
  rw [lastBreak_eq_inertiaBreak, lastBreak_eq_inertiaBreak]
  congr 1
  ext n : 1
  change ((unramifiedCharacter (localDegree F) z n : ℂˣ) : ℂ) • A.representation n =
    A.representation n
  rw [unramifiedCharacter_on_kernel (localDegree F) z n.2, Units.val_one, one_smul]

/-- The last break over an unramified stage is the break of the restricted type. -/
theorem lastBreak_stage (m : ℕ) {V : Type uW} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V]
    (τ : Representation ℂ (localWeilGroup ((unramifiedStage F (m + 1)).asPadicField (p := p))) V) :
    lastBreak _ (FiniteRepresentation.of τ) =
      inertiaBreak F ((weilStage F φ hφ m).block τ 0) := by
  rw [lastBreak_eq_inertiaBreak]
  unfold inertiaBreak
  congr 1
  ext v
  refine and_congr_right fun hv => ?_
  let S := weilStage F φ hφ m
  constructor
  · intro h
    have key : ∀ n : (weilSplit F φ hφ).inertia, (n : localWeilGroup F) ∈ upperGroup F v →
        S.block τ 0 n = 1 := by
      intro n hn
      have h0 : S.ι (S.κ n) ∈ upperGroup F v := by rw [S.ι_κ]; exact hn
      have h1 : S.κ n ∈ upperGroup _ v :=
        (unramifiedStage_mem_upperGroup F (m + 1) hv (S.κ n)).mp h0
      have h2 := h ⟨S.κ n, Langlands.ArithmeticStableTwist.upperGroup_le_localInertia _ hv h1⟩ h1
      change τ (S.κ ((weilSplit F φ hφ).cj 0 n)) = 1
      rw [cj_zero]
      exact h2
    exact key
  · intro h w hw
    have h1 : S.ι w ∈ upperGroup F v := (unramifiedStage_mem_upperGroup F (m + 1) hv w).mpr hw
    let n : (weilSplit F φ hφ).inertia := ⟨S.ι w, Langlands.ArithmeticStableTwist.upperGroup_le_localInertia F hv h1⟩
    have hn : S.κ n = w := S.injective (S.ι_κ n)
    have h2 := h n h1
    change τ (S.κ ((weilSplit F φ hφ).cj 0 n)) = 1 at h2
    rw [cj_zero, hn] at h2
    exact h2

end Langlands.Henniart.Numerical
