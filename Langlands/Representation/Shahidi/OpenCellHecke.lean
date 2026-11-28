import Langlands.Representation.Shahidi.OpenCellBaseShell
import Langlands.Representation.Shahidi.OpenCellHeckeSplit
import Langlands.Representation.Conductor.UnramifiedSphericalWhittaker
import Langlands.Representation.Unramified.PrincipalSeriesHecke

/-! # Minuscule Hecke operators on lifted functions

The lift to `GL_((r+1)+(t+1))(K)` of a Levi-invariant Levi function that is left equivariant under
the two upper unipotent groups (by `θ₁`, `θ₂`) transforms on the left under the upper unipotent
group of the whole group by `θ'(u) = θ₁(u₁₁) θ₂(u₂₂)`. When moreover `θ₁` and `θ₂` are
integrally trivial and the coset labels are integral, at a torus point `ϖ^ν` with `ν` antitone on each block, its translates by the
minuscule coset representatives `labelledRep α` are its values at the torus points
`ϖ^(ν + 1_S)`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.Conductor Langlands.Unramified.MinusculeCosets
open Langlands.GeneralLinear.Iwasawa
open Langlands.Whittaker.UpperUnipotentCharacter (adjacentUnit)

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocHeckeTopology : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance ocHeckeValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocHeckeLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField

variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
variable {r t : ℕ}


section BlockFunctions

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀} {r t : ℕ}

/-- Left equivariance under the upper unipotent group of `GL_((r+1)+(t+1))` through the
characters `θ₁`, `θ₂` of the two diagonal blocks. -/
def IsBlockEquivariant (θ₁ : upperUnipotent (r + 1) F →* ℂˣ) (θ₂ : upperUnipotent (t + 1) F →* ℂˣ)
    (φ : Langlands.GeneralLinear ((r + 1) + (t + 1)) F → ℂ) : Prop :=
  ∀ (u : Langlands.GeneralLinear ((r + 1) + (t + 1)) F)
    (hu : u ∈ upperUnipotent ((r + 1) + (t + 1)) F) (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) F),
    φ (u * g) = (θ₁ ⟨topLeft u hu.1, topLeft_mem_upperUnipotent hu⟩ : ℂ) *
      (θ₂ ⟨botRight u hu.1, botRight_mem_upperUnipotent hu⟩ : ℂ) * φ g

/-- Right invariance under the integral matrices. -/
def IsRightIntegral (v : Valuation F Γ₀) (φ : Langlands.GeneralLinear ((r + 1) + (t + 1)) F → ℂ) :
    Prop :=
  ∀ g, ∀ k ∈ integralSubgroup v.integer (r + 1 + t), φ (g * k) = φ g

theorem blockSum_mem_upperUnipotent {u₁ : Langlands.GeneralLinear (r + 1) F}
    {u₂ : Langlands.GeneralLinear (t + 1) F} (h₁ : u₁ ∈ upperUnipotent (r + 1) F)
    (h₂ : u₂ ∈ upperUnipotent (t + 1) F) :
    blockSum (u₁, u₂) ∈ upperUnipotent ((r + 1) + (t + 1)) F := by
  refine ⟨fun (i j : Fin ((r + 1) + (t + 1))) hij => ?_,
    fun (i : Fin ((r + 1) + (t + 1))) => ?_⟩
  · change blockSum (u₁, u₂) i j = 0
    have hij' : (j : ℕ) < i := hij
    induction i using Fin.addCases <;> induction j using Fin.addCases
    · rw [blockSum_apply_left]
      apply h₁.1
      rw [Fin.val_castAdd, Fin.val_castAdd] at hij'
      exact hij'
    · rw [blockSum_apply_left_right]
    · rw [blockSum_apply_right_left]
    · rw [blockSum_apply_right]
      apply h₂.1
      rw [Fin.val_natAdd, Fin.val_natAdd] at hij'
      exact (Nat.add_lt_add_iff_left).1 hij'
  · change blockSum (u₁, u₂) i i = 1
    induction i using Fin.addCases
    · rw [blockSum_apply_left]
      exact h₁.2 _
    · rw [blockSum_apply_right]
      exact h₂.2 _

theorem blockSum_mem_integralSubgroup {k₁ : Langlands.GeneralLinear (r + 1) F}
    {k₂ : Langlands.GeneralLinear (t + 1) F} (h₁ : k₁ ∈ integralSubgroup v.integer r)
    (h₂ : k₂ ∈ integralSubgroup v.integer t) :
    blockSum (k₁, k₂) ∈ integralSubgroup v.integer (r + 1 + t) := by
  obtain ⟨a₁, b₁⟩ := (Conductor.mem_integralSubgroup _ _ _).1 h₁
  obtain ⟨a₂, b₂⟩ := (Conductor.mem_integralSubgroup _ _ _).1 h₂
  have hinv : (blockSum (k₁, k₂))⁻¹ = blockSum (k₁⁻¹, k₂⁻¹) := by
    rw [← map_inv]
    rfl
  refine (Conductor.mem_integralSubgroup _ _ _).2
    ⟨fun (i j : Fin ((r + 1) + (t + 1))) => ?_, fun (i j : Fin ((r + 1) + (t + 1))) => ?_⟩
  · induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp [a₁, a₂, zero_mem]
  · rw [hinv]
    induction i using Fin.addCases <;> induction j using Fin.addCases
    · rw [blockSum_apply_left]
      exact b₁ _ _
    · rw [blockSum_apply_left_right]
      exact zero_mem _
    · rw [blockSum_apply_right_left]
      exact zero_mem _
    · rw [blockSum_apply_right]
      exact b₂ _ _

theorem topLeft_blockSum {u₁ : Langlands.GeneralLinear (r + 1) F}
    {u₂ : Langlands.GeneralLinear (t + 1) F} (h : (blockSum (u₁, u₂)).val.IsUpperTriangular) :
    topLeft (blockSum (u₁, u₂)) h = u₁ := by
  apply Units.ext
  ext i j
  change blockSum (u₁, u₂) (i.castAdd (t + 1)) (j.castAdd (t + 1)) = u₁ i j
  exact blockSum_apply_left u₁ u₂ i j

theorem botRight_blockSum {u₁ : Langlands.GeneralLinear (r + 1) F}
    {u₂ : Langlands.GeneralLinear (t + 1) F} (h : (blockSum (u₁, u₂)).val.IsUpperTriangular) :
    botRight (blockSum (u₁, u₂)) h = u₂ := by
  apply Units.ext
  ext i j
  change blockSum (u₁, u₂) (i.natAdd (r + 1)) (j.natAdd (r + 1)) = u₂ i j
  exact blockSum_apply_right u₁ u₂ i j

variable {θ₁ : upperUnipotent (r + 1) F →* ℂˣ} {θ₂ : upperUnipotent (t + 1) F →* ℂˣ}
variable {ϖ : Fˣ}

/-- A block-equivariant right-integral function vanishes at `ϖ^ν` when `ν` is not antitone on
the first block, provided `θ₁` is nontrivial on every simple root group over `ϖ⁻¹𝒪`. -/
theorem eval_torus_eq_zero_of_not_antitone_first (hϖ : Iwasawa.IsUniformizingElement v ϖ)
    {φ : Langlands.GeneralLinear ((r + 1) + (t + 1)) F → ℂ} (hφ : IsBlockEquivariant θ₁ θ₂ φ)
    (hK : IsRightIntegral v φ)
    (hθ : ∀ i : Fin r, ∃ x : F, v x * v (ϖ : F) ≤ 1 ∧ θ₁ (adjacentUnit i x) ≠ 1)
    {ν : Fin ((r + 1) + (t + 1)) → ℤ} (hν : ¬ Antitone fun i : Fin (r + 1) => ν (i.castAdd (t + 1))) :
    φ (Iwasawa.torus ϖ ν) = 0 := by
  set d := Iwasawa.torus ϖ fun j : Fin (t + 1) => ν (j.natAdd (r + 1))
  have h := RankinSelberg.UnramifiedWhittaker.eval_torus_eq_zero_of_not_antitone (θ := θ₁) hϖ
    (f := fun h => φ (blockSum (h, d)))
    (fun u g => by
      have e : blockSum (u.val * g, d) = blockSum (u.val, 1) * blockSum (g, d) := by
        rw [← map_mul, Prod.mk_mul_mk, one_mul]
      have hu := blockSum_mem_upperUnipotent (t := t) u.2 (one_mem _)
      rw [e, hφ _ hu]
      have e1 : (⟨topLeft (blockSum (u.val, 1)) hu.1, topLeft_mem_upperUnipotent hu⟩ :
          upperUnipotent (r + 1) F) = u := Subtype.ext (topLeft_blockSum hu.1)
      have e2 : (⟨botRight (blockSum (u.val, 1)) hu.1, botRight_mem_upperUnipotent hu⟩ :
          upperUnipotent (t + 1) F) = 1 := Subtype.ext (botRight_blockSum hu.1)
      rw [e1, e2, map_one, Units.val_one, mul_one])
    (fun g k hk => by
      have e : blockSum (g * k, d) = blockSum (g, d) * blockSum (k, 1) := by
        rw [← map_mul, Prod.mk_mul_mk, mul_one]
      rw [e, hK _ _ (blockSum_mem_integralSubgroup hk (one_mem _))])
    hθ hν
  rwa [RankinSelberg.TwoBlockDominantRectangular.blockSum_torus, Fin.append_castAdd_natAdd] at h

/-- A block-equivariant right-integral function vanishes at `ϖ^ν` when `ν` is not antitone on
the second block, provided `θ₂` is nontrivial on every simple root group over `ϖ⁻¹𝒪`. -/
theorem eval_torus_eq_zero_of_not_antitone_second (hϖ : Iwasawa.IsUniformizingElement v ϖ)
    {φ : Langlands.GeneralLinear ((r + 1) + (t + 1)) F → ℂ} (hφ : IsBlockEquivariant θ₁ θ₂ φ)
    (hK : IsRightIntegral v φ)
    (hθ : ∀ i : Fin t, ∃ x : F, v x * v (ϖ : F) ≤ 1 ∧ θ₂ (adjacentUnit i x) ≠ 1)
    {ν : Fin ((r + 1) + (t + 1)) → ℤ} (hν : ¬ Antitone fun j : Fin (t + 1) => ν (j.natAdd (r + 1))) :
    φ (Iwasawa.torus ϖ ν) = 0 := by
  set d := Iwasawa.torus ϖ fun i : Fin (r + 1) => ν (i.castAdd (t + 1))
  have h := RankinSelberg.UnramifiedWhittaker.eval_torus_eq_zero_of_not_antitone (θ := θ₂) hϖ
    (f := fun h => φ (blockSum (d, h)))
    (fun u g => by
      have e : blockSum (d, u.val * g) = blockSum (1, u.val) * blockSum (d, g) := by
        rw [← map_mul, Prod.mk_mul_mk, one_mul]
      have hu := blockSum_mem_upperUnipotent (r := r) (one_mem _) u.2
      rw [e, hφ _ hu]
      have e1 : (⟨topLeft (blockSum (1, u.val)) hu.1, topLeft_mem_upperUnipotent hu⟩ :
          upperUnipotent (r + 1) F) = 1 := Subtype.ext (topLeft_blockSum hu.1)
      have e2 : (⟨botRight (blockSum (1, u.val)) hu.1, botRight_mem_upperUnipotent hu⟩ :
          upperUnipotent (t + 1) F) = u := Subtype.ext (botRight_blockSum hu.1)
      rw [e1, e2, map_one, Units.val_one, one_mul])
    (fun g k hk => by
      have e : blockSum (d, g * k) = blockSum (d, g) * blockSum (1, k) := by
        rw [← map_mul, Prod.mk_mul_mk, mul_one]
      rw [e, hK _ _ (blockSum_mem_integralSubgroup (one_mem _) hk)])
    hθ hν
  rwa [RankinSelberg.TwoBlockDominantRectangular.blockSum_torus, Fin.append_castAdd_natAdd] at h

/-- Two block-equivariant right-integral functions agreeing at every torus point agree. -/
theorem eq_of_eval_torus (hϖ : Iwasawa.IsUniformizingElement v ϖ)
    {φ φ' : Langlands.GeneralLinear ((r + 1) + (t + 1)) F → ℂ} (hφ : IsBlockEquivariant θ₁ θ₂ φ)
    (hφ' : IsBlockEquivariant θ₁ θ₂ φ') (hK : IsRightIntegral v φ) (hK' : IsRightIntegral v φ')
    (h : ∀ ν, φ (Iwasawa.torus ϖ ν) = φ' (Iwasawa.torus ϖ ν)) : φ = φ' := by
  funext g
  obtain ⟨u, hu, ν, k, hk, rfl⟩ := Iwasawa.exists_iwasawa (n := r + 1 + t) hϖ g
  rw [hK _ _ hk, hK' _ _ hk, hφ _ hu, hφ' _ hu, h]

theorem topLeft_torus_conj_radicalElement (ϖ : Fˣ) (ν : Fin ((r + 1) + (t + 1)) → ℤ)
    (S : Finset (Fin ((r + 1) + (t + 1))))
    (c : Fin ((r + 1) + (t + 1)) → Fin ((r + 1) + (t + 1)) → F)
    (h : (Iwasawa.torus ϖ ν * radicalElement S c * (Iwasawa.torus ϖ ν)⁻¹).val.IsUpperTriangular) :
    topLeft (Iwasawa.torus ϖ ν * radicalElement S c * (Iwasawa.torus ϖ ν)⁻¹) h =
      Iwasawa.torus ϖ (fun i => ν (i.castAdd (t + 1))) *
        radicalElement (firstPart S) (fun i j => c (i.castAdd (t + 1)) (j.castAdd (t + 1))) *
          (Iwasawa.torus ϖ (fun i => ν (i.castAdd (t + 1))))⁻¹ := by
  apply Units.ext
  ext i j
  change (Iwasawa.torus ϖ ν * radicalElement S c * (Iwasawa.torus ϖ ν)⁻¹)
    (i.castAdd (t + 1)) (j.castAdd (t + 1)) = _
  rw [RankinSelberg.UnramifiedWhittaker.torus_conj_apply,
    RankinSelberg.UnramifiedWhittaker.torus_conj_apply, radicalElement_apply, radicalElement_apply]
  simp only [isRadicalPair_castAdd_castAdd, Fin.castAdd_inj]

theorem botRight_torus_conj_radicalElement (ϖ : Fˣ) (ν : Fin ((r + 1) + (t + 1)) → ℤ)
    (S : Finset (Fin ((r + 1) + (t + 1))))
    (c : Fin ((r + 1) + (t + 1)) → Fin ((r + 1) + (t + 1)) → F)
    (h : (Iwasawa.torus ϖ ν * radicalElement S c * (Iwasawa.torus ϖ ν)⁻¹).val.IsUpperTriangular) :
    botRight (Iwasawa.torus ϖ ν * radicalElement S c * (Iwasawa.torus ϖ ν)⁻¹) h =
      Iwasawa.torus ϖ (fun j => ν (j.natAdd (r + 1))) *
        radicalElement (secondPart S) (fun i j => c (i.natAdd (r + 1)) (j.natAdd (r + 1))) *
          (Iwasawa.torus ϖ (fun j => ν (j.natAdd (r + 1))))⁻¹ := by
  apply Units.ext
  ext i j
  change (Iwasawa.torus ϖ ν * radicalElement S c * (Iwasawa.torus ϖ ν)⁻¹)
    (i.natAdd (r + 1)) (j.natAdd (r + 1)) = _
  rw [RankinSelberg.UnramifiedWhittaker.torus_conj_apply,
    RankinSelberg.UnramifiedWhittaker.torus_conj_apply, radicalElement_apply, radicalElement_apply]
  simp only [isRadicalPair_natAdd_natAdd, Fin.natAdd_inj]

/-- For `ν` antitone on each block, conjugating an integral radical element by `ϖ^ν` gives an
upper unipotent element whose two diagonal blocks are integral. -/
theorem blocks_torus_conj_radicalElement_mem (hϖ : v (ϖ : F) ≤ 1)
    {ν : Fin ((r + 1) + (t + 1)) → ℤ} (h₁ : Antitone fun i : Fin (r + 1) => ν (i.castAdd (t + 1)))
    (h₂ : Antitone fun j : Fin (t + 1) => ν (j.natAdd (r + 1)))
    (S : Finset (Fin ((r + 1) + (t + 1))))
    {c : Fin ((r + 1) + (t + 1)) → Fin ((r + 1) + (t + 1)) → F} (hc : ∀ a b, c a b ∈ v.integer)
    (hu : Iwasawa.torus ϖ ν * radicalElement S c * (Iwasawa.torus ϖ ν)⁻¹ ∈
      upperUnipotent ((r + 1) + (t + 1)) F) :
    topLeft _ hu.1 ∈ integralSubgroup v.integer r ∧
      botRight _ hu.1 ∈ integralSubgroup v.integer t := by
  rw [topLeft_torus_conj_radicalElement, botRight_torus_conj_radicalElement]
  exact ⟨RankinSelberg.UnramifiedWhittaker.torus_conj_radicalElement_mem hϖ h₁ _
      fun a b _ => hc _ _,
    RankinSelberg.UnramifiedWhittaker.torus_conj_radicalElement_mem hϖ h₂ _
      fun a b _ => hc _ _⟩

end BlockFunctions

section Equivariance

variable {θ₁ : upperUnipotent (r + 1) K.Carrier →* ℂˣ} {θ₂ : upperUnipotent (t + 1) K.Carrier →* ℂˣ}

/-- Left equivariance of a Levi function under the two upper unipotent groups. -/
def IsLeviEquivariant (θ₁ : upperUnipotent (r + 1) K.Carrier →* ℂˣ)
    (θ₂ : upperUnipotent (t + 1) K.Carrier →* ℂˣ)
    (Φ : Langlands.GeneralLinear (r + 1) K.Carrier → Langlands.GeneralLinear (t + 1) K.Carrier → ℂ) :
    Prop :=
  ∀ (u₁ : upperUnipotent (r + 1) K.Carrier) (u₂ : upperUnipotent (t + 1) K.Carrier) m₁ m₂,
    Φ (u₁.val * m₁) (u₂.val * m₂) = (θ₁ u₁ : ℂ) * (θ₂ u₂ : ℂ) * Φ m₁ m₂

/-- **Left equivariance of a lift under the upper unipotent group**, for a Levi-invariant,
Levi-equivariant `Φ`. -/
theorem liftFunction_unipotent_mul
    {Φ : Langlands.GeneralLinear (r + 1) K.Carrier → Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}
    (hΦ : IsLeviInvariant Φ) (hθ : IsLeviEquivariant θ₁ θ₂ Φ)
    {u : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier}
    (hu : u ∈ upperUnipotent ((r + 1) + (t + 1)) K.Carrier)
    (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    liftFunction hϖ Φ (u * g) =
      (θ₁ ⟨topLeft u hu.1, topLeft_mem_upperUnipotent hu⟩ : ℂ) *
        (θ₂ ⟨botRight u hu.1, botRight_mem_upperUnipotent hu⟩ : ℂ) * liftFunction hϖ Φ g := by
  have hdec := eq_upper_mul_blockSum u hu.1
  set P := liftUpper K r t (radicalCoordinate u hu.1) *
    liftLevi K r t (topLeft u hu.1) (botRight u hu.1)
  have hP : (P : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) = u := by
    rw [hdec]
    exact (upper_mul_blockSum_eq K r t _ _ _).symm
  obtain ⟨m₁, m₂, h1, h2⟩ := liftFunction_parabolic_mul_left hϖ hΦ P g
  rw [hP] at h2
  rw [h2, h1, liftFirst_mul, liftSecond_mul, liftFirst_liftUpper, liftSecond_liftUpper,
    liftFirst_liftLevi, liftSecond_liftLevi, one_mul, one_mul]
  exact hθ ⟨_, topLeft_mem_upperUnipotent hu⟩ ⟨_, botRight_mem_upperUnipotent hu⟩ m₁ m₂

variable {Φ : Langlands.GeneralLinear (r + 1) K.Carrier → Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}

theorem isBlockEquivariant_liftFunction (hΦ : IsLeviInvariant Φ) (hθ : IsLeviEquivariant θ₁ θ₂ Φ) :
    IsBlockEquivariant θ₁ θ₂ (liftFunction hϖ Φ) :=
  fun _ hu g => liftFunction_unipotent_mul hϖ hΦ hθ hu g

theorem isRightIntegral_liftFunction (hΦ : IsLeviInvariant Φ) :
    IsRightIntegral (ValuativeRel.valuation K.Carrier) (liftFunction hϖ Φ) :=
  fun g k hk => liftFunction_mul_integral hϖ hΦ g k hk

/-- The lift of a Levi-invariant `Φ` at a torus point is `Φ` at the two diagonal torus blocks. -/
theorem liftFunction_torus (hΦ : IsLeviInvariant Φ) (μ : Fin ((r + 1) + (t + 1)) → ℤ) :
    liftFunction hϖ Φ (Iwasawa.torus ϖ μ) =
      Φ (Iwasawa.torus ϖ fun i => μ (i.castAdd (t + 1)))
        (Iwasawa.torus ϖ fun j => μ (j.natAdd (r + 1))) := by
  have e : Iwasawa.torus ϖ μ = upper (r + 1) (t + 1) K.Carrier 0 *
      blockSum (Iwasawa.torus ϖ fun i => μ (i.castAdd (t + 1)),
        Iwasawa.torus ϖ fun j => μ (j.natAdd (r + 1))) * 1 := by
    rw [upper_zero, one_mul, mul_one, RankinSelberg.TwoBlockDominantRectangular.blockSum_torus,
      Fin.append_castAdd_natAdd]
  rw [e, liftFunction_law hϖ hΦ _ _ _ _ (one_mem _)]

variable {Λ : Type*} {σ : Λ → K.Carrier}

/-- **Translates by minuscule representatives at block-dominant torus points.** For a
Levi-invariant, Levi-equivariant `Φ` with integrally trivial block characters and integral coset
labels `σ`. -/
theorem liftFunction_torus_mul_labelledRep (hΦ : IsLeviInvariant Φ)
    (hθ : IsLeviEquivariant θ₁ θ₂ Φ)
    (hθ₁K : IsIntegrallyTrivial (ValuativeRel.valuation K.Carrier) θ₁)
    (hθ₂K : IsIntegrallyTrivial (ValuativeRel.valuation K.Carrier) θ₂)
    (hσ : ∀ x, σ x ∈ (ValuativeRel.valuation K.Carrier).integer)
    {ν : Fin ((r + 1) + (t + 1)) → ℤ} (h₁ : Antitone fun i : Fin (r + 1) => ν (i.castAdd (t + 1)))
    (h₂ : Antitone fun j : Fin (t + 1) => ν (j.natAdd (r + 1))) {k : ℕ}
    (α : CosetIndex Λ ((r + 1) + (t + 1)) k) :
    liftFunction hϖ Φ (Iwasawa.torus ϖ ν * labelledRep ϖ σ α) =
      liftFunction hϖ Φ (Iwasawa.torus ϖ (ν + subsetExponent α.1.1)) := by
  set S := α.1.1
  set c := liftCoeff σ S α.2
  have hc : ∀ a b, c a b ∈ (ValuativeRel.valuation K.Carrier).integer := by
    intro a b
    simp only [c, liftCoeff]
    split_ifs
    · exact hσ _
    · exact zero_mem _
  have heq : Iwasawa.torus ϖ ν * labelledRep ϖ σ α =
      (Iwasawa.torus ϖ ν * radicalElement S c * (Iwasawa.torus ϖ ν)⁻¹) *
        Iwasawa.torus ϖ (ν + subsetExponent S) := by
    rw [labelledRep, cosetRep, subsetTorus, ← RankinSelberg.UnramifiedWhittaker.torus_mul_torus]
    group
    rfl
  have hu := RankinSelberg.UnramifiedWhittaker.torus_conj_mem_upperUnipotent ϖ ν
    (radicalElement_mem_upperUnipotent S c)
  obtain ⟨hk₁, hk₂⟩ := blocks_torus_conj_radicalElement_mem hϖ.1.le h₁ h₂ S hc hu
  rw [heq, liftFunction_unipotent_mul hϖ hΦ hθ hu, hθ₁K _ hk₁, hθ₂K _ hk₂]
  simp

/-- Summing over the labelled representatives at a block-dominant torus point, under the
hypotheses of `liftFunction_torus_mul_labelledRep`. -/
theorem sum_liftFunction_torus_mul_labelledRep [Fintype Λ] (hΦ : IsLeviInvariant Φ)
    (hθ : IsLeviEquivariant θ₁ θ₂ Φ)
    (hθ₁K : IsIntegrallyTrivial (ValuativeRel.valuation K.Carrier) θ₁)
    (hθ₂K : IsIntegrallyTrivial (ValuativeRel.valuation K.Carrier) θ₂)
    (hσ : ∀ x, σ x ∈ (ValuativeRel.valuation K.Carrier).integer)
    {ν : Fin ((r + 1) + (t + 1)) → ℤ} (h₁ : Antitone fun i : Fin (r + 1) => ν (i.castAdd (t + 1)))
    (h₂ : Antitone fun j : Fin (t + 1) => ν (j.natAdd (r + 1))) (k : ℕ) :
    ∑ α : CosetIndex Λ ((r + 1) + (t + 1)) k, liftFunction hϖ Φ (Iwasawa.torus ϖ ν * labelledRep ϖ σ α) =
      ∑ S : {S : Finset (Fin ((r + 1) + (t + 1))) // S.card = k},
        (Fintype.card Λ : ℂ) ^ Fintype.card (RadicalPairs S.1) *
          liftFunction hϖ Φ (Iwasawa.torus ϖ (ν + subsetExponent S.1)) := by
  classical
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp_rw [fun w : RadicalPairs S.1 → Λ =>
    liftFunction_torus_mul_labelledRep hϖ hΦ hθ hθ₁K hθ₂K hσ h₁ h₂ (α := ⟨S, w⟩)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
  push_cast
  ring

end Equivariance

end Langlands.Shahidi.OpenCell
