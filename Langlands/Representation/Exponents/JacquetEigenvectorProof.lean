import Langlands.Representation.Exponents.JacquetEigenvectorStatement
import Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof

/-!
# Ordinary eigenvectors for generalized normalized Jacquet exponents

A nonzero generalized-character vector of a commutative action, lying in a
finite-dimensional stable subspace, yields an ordinary eigenvector with the same
character. For the split centre of the normalized Jacquet module the stable
subspace is the space of vectors fixed by an open Levi subgroup, which is
finite-dimensional by normalized Jacquet admissibility.
-/

noncomputable section

namespace Langlands

universe uF uV uK uA uW

section Generic

variable {K : Type uK} [Field K] {A : Type uA} [CommMonoid A]
variable {W : Type uW} [AddCommGroup W] [Module K W]

/-- A shifted operator `π(a) - c` of a commutative action commutes with every `π(b)`. -/
theorem commute_sub_smul_one (π : Representation K A W) (a b : A) (c : K) :
    Commute (π a - c • 1) (π b) := by
  refine Commute.sub_left ?_ ((Commute.one_left _).smul_left c)
  change π a * π b = π b * π a
  rw [← map_mul, ← map_mul, mul_comm]

/-- Generalized character spaces of a commutative action are stable. -/
theorem map_mem_characterSpace (π : Representation K A W) (χ : A →* Kˣ) (k : ℕ)
    (a : A) {w : W} (hw : w ∈ characterSpace π χ k) : π a w ∈ characterSpace π χ k := by
  rw [mem_characterSpace] at hw ⊢
  intro b
  rw [← Module.End.mul_apply, ((commute_sub_smul_one π b a (χ b : K)).pow_left k).eq,
    Module.End.mul_apply, hw b, map_zero]

/-- An operator stabilizing `U` and killing `U` after `k` steps has a nonzero
kernel vector in `U`, provided `U` is nonzero. -/
theorem exists_mem_ker_of_pow_eq_zero {U : Submodule K W} (N : Module.End K W)
    (hN : ∀ w ∈ U, N w ∈ U) (k : ℕ) (hk : ∀ w ∈ U, (N ^ k) w = 0)
    {u : W} (hu : u ∈ U) (hu0 : u ≠ 0) :
    ∃ w ∈ U, w ≠ 0 ∧ N w = 0 := by
  by_contra h
  have hinj : ∀ j : ℕ, ∀ w ∈ U, (N ^ j) w = 0 → w = 0 := by
    intro j
    induction j with
    | zero =>
      intro w _ hw
      simpa using hw
    | succ j ih =>
      intro w hw hjw
      rw [pow_succ, Module.End.mul_apply] at hjw
      have hNw := ih (N w) (hN w hw) hjw
      by_contra hw0
      exact h ⟨w, hw, hw0, hNw⟩
  exact hu0 (hinj k u hu (hk u hu))

/-- A nonzero vector of a generalized character space lying in a
finite-dimensional stable subspace yields a nonzero common eigenvector with
the same character. -/
theorem exists_eigenvector_of_mem_characterSpace (π : Representation K A W)
    (χ : A →* Kˣ) (k : ℕ) (S : Submodule K W) [FiniteDimensional K S]
    (hS : ∀ a, ∀ w ∈ S, π a w ∈ S) {v : W} (hv : v ≠ 0) (hvS : v ∈ S)
    (hvk : v ∈ characterSpace π χ k) :
    ∃ w : W, w ≠ 0 ∧ ∀ a, π a w = (χ a : K) • w := by
  classical
  let P : ℕ → Prop := fun d => ∃ U : Submodule K W, U ≤ S ⊓ characterSpace π χ k ∧
    U ≠ ⊥ ∧ (∀ a, ∀ w ∈ U, π a w ∈ U) ∧ Module.finrank K U = d
  have hP : ∃ d, P d := ⟨_, S ⊓ characterSpace π χ k, le_rfl,
    (Submodule.ne_bot_iff _).mpr ⟨v, ⟨hvS, hvk⟩, hv⟩,
    fun a w hw => ⟨hS a w hw.1, map_mem_characterSpace π χ k a hw.2⟩, rfl⟩
  obtain ⟨U, hUle, hU0, hUst, hUd⟩ := Nat.find_spec hP
  have hUfin : FiniteDimensional K U :=
    Submodule.finiteDimensional_of_le (hUle.trans inf_le_left)
  have hker : ∀ a, U ≤ LinearMap.ker (π a - (χ a : K) • 1) := by
    intro a
    let N : Module.End K W := π a - (χ a : K) • 1
    have hN : ∀ w ∈ U, N w ∈ U := fun w hw => U.sub_mem (hUst a w hw) (U.smul_mem _ hw)
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff U).mp hU0
    obtain ⟨w₀, hw₀U, hw₀, hNw₀⟩ := exists_mem_ker_of_pow_eq_zero N hN k
      (fun w hw => (mem_characterSpace π χ k w).mp (hUle hw).2 a) hu hu0
    let U' := U ⊓ LinearMap.ker N
    have hU'st : ∀ b, ∀ w ∈ U', π b w ∈ U' := by
      intro b w hw
      refine ⟨hUst b w hw.1, ?_⟩
      change N (π b w) = 0
      rw [← Module.End.mul_apply, (commute_sub_smul_one π a b (χ a : K)).eq,
        Module.End.mul_apply]
      change π b (N w) = 0
      rw [show N w = 0 from hw.2, map_zero]
    have hU'0 : U' ≠ ⊥ := (Submodule.ne_bot_iff _).mpr ⟨w₀, ⟨hw₀U, hNw₀⟩, hw₀⟩
    have hmin := Nat.find_min' hP ⟨U', inf_le_left.trans hUle, hU'0, hU'st, rfl⟩
    by_contra hnot
    have hlt : U' < U := lt_of_le_of_ne inf_le_left (fun h => hnot (by
      rw [← h]
      exact inf_le_right))
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff U).mp hU0
  refine ⟨u, hu0, fun a => ?_⟩
  have h := hker a hu
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    sub_eq_zero] at h
  exact h

end Generic

namespace Parabolic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    {n : ℕ} (B : GeneralLinear.BlockShape n) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- On every quotient class, the inverse-half twist of the product-Levi
coinvariants acts as the normalized Jacquet action. -/
theorem twist_inverseHalfCharacter_leviCoinvariants_apply
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (m : B.Levi F.Carrier)
    (x : B.JacquetModule ρ) :
    twist (Jacquet.inverseHalfCharacter (T.leviModulus B))
        (leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype)) m x =
      T.normalizedJacquet B ρ m x := by
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ x
  rw [T.normalizedJacquet_mk]
  change (Jacquet.inverseHalfCharacter (T.leviModulus B) m : ℂ) •
      leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype) m (B.jacquetMk ρ v) = _
  rw [Jacquet.inverseHalfCharacter_apply, leviCoinvariants_mk]
  rfl

/-- The inverse-half twist of the product-Levi coinvariants is the normalized
Jacquet representation. -/
theorem twist_inverseHalfCharacter_leviCoinvariants
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    twist (Jacquet.inverseHalfCharacter (T.leviModulus B))
        (leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype)) =
      T.normalizedJacquet B ρ :=
  MonoidHom.ext fun m => LinearMap.ext fun x =>
    twist_inverseHalfCharacter_leviCoinvariants_apply F T B ρ m x

/-- The normalized Jacquet module of an admissible representation is admissible. -/
theorem isAdmissible_normalizedJacquet
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    letI := T.topology
    IsAdmissible ρ → IsAdmissible (T.normalizedJacquet B ρ) := by
  let := T.topology
  intro hρ
  have h : IsAdmissible (twist (Jacquet.inverseHalfCharacter (T.leviModulus B))
      (leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype))) :=
    normalizedJacquetAdmissibility F T B V ρ hρ
  rwa [twist_inverseHalfCharacter_leviCoinvariants F T B ρ] at h

/-- The split centre preserves the vectors fixed by any subgroup of the Levi. -/
theorem splitCentreJacquet_mem_fixedVectors
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (L : Subgroup (B.Levi F.Carrier))
    (a : Fin B.length → F.Carrierˣ) {w : B.JacquetModule ρ}
    (hw : w ∈ fixedVectors (T.normalizedJacquet B ρ) L) :
    T.splitCentreJacquet B ρ a w ∈ fixedVectors (T.normalizedJacquet B ρ) L := by
  intro l
  have hwl : T.normalizedJacquet B ρ (l : B.Levi F.Carrier) w = w := hw l
  have hz := Subgroup.mem_center_iff.mp (B.blockScalarLevi_mem_center F.Carrier a)
    (l : B.Levi F.Carrier)
  change T.normalizedJacquet B ρ (l : B.Levi F.Carrier)
      (T.normalizedJacquet B ρ (B.blockScalarLevi F.Carrier a) w) =
    T.normalizedJacquet B ρ (B.blockScalarLevi F.Carrier a) w
  rw [← Module.End.mul_apply, ← map_mul, hz, map_mul, Module.End.mul_apply, hwl]

end Parabolic

open Parabolic in
/-- Every generalized normalized upper Jacquet exponent of an admissible
representation has a nonzero eigenvector for the entire split centre, with the
same character. -/
theorem glJacquetExponentEigenvector : GLJacquetExponentEigenvectorStatement.{uF, uV} := by
  intro p _ F T n _ V _ _ ρ
  let := T.topology
  intro hρ B χ hχ
  obtain ⟨_, hgen⟩ := hχ
  obtain ⟨k, v, hv, hvk⟩ := (isGeneralizedEigencharacter_iff _ χ).mp hgen
  have hN := isAdmissible_normalizedJacquet F T B ρ hρ
  obtain ⟨L, hL⟩ := hN.1 v
  have : FiniteDimensional ℂ (fixedVectors (T.normalizedJacquet B ρ) L.toSubgroup) := hN.2 L
  exact exists_eigenvector_of_mem_characterSpace (T.splitCentreJacquet B ρ) χ k
    (fixedVectors (T.normalizedJacquet B ρ) L.toSubgroup)
    (fun a w hw => splitCentreJacquet_mem_fixedVectors F T B ρ L.toSubgroup a hw) hv hL
    ((mem_characterSpace _ χ k v).mpr hvk)

end Langlands
