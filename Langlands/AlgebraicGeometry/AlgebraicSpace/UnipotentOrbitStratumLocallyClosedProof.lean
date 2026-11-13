import Langlands.AlgebraicGeometry.AlgebraicSpace.StabilizerFibreLocalDimensionProof
import Langlands.AlgebraicGeometry.RelativeDimensionSublevelOpennessProof
import Mathlib.Topology.LocallyClosed

/-!
# Orbit-dimension strata are locally closed: proof

Clause 1 of Conrad's Example 5.5. The stabilizer fibre over `v` has the same dimension
as its local dimension at the identity point `e(v)`, the image of `v` under the identity
section of the stabilizer scheme. That local dimension is upper semicontinuous on the
stabilizer scheme, so its pullback along the identity section has open sublevel sets on
`V`. A function to `WithBot ℕ∞` with nonnegative values and open sublevel sets has
locally closed level sets, and the stratum of orbit dimension `d` is such a level set.
The argument uses only that `G` is locally of finite type.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open Langlands (GroupScheme)
open Langlands.GroupScheme (SchemeAction)
open Langlands.AlgebraicGeometry.SchemeFiberGeometry
  (relativeTopologicalKrullDimAt RelativeDimensionSublevelOpenness
    relativeDimensionSublevelOpenness_proof relativeTopologicalKrullDimAt_nonneg)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace UnipotentOrbitStratum

section Levels

variable {X : Type*} [TopologicalSpace X] (f : X → WithBot ℕ∞)
  (hopen : ∀ m : ℕ, IsOpen {x | f x ≤ m}) (hnn : ∀ x, 0 ≤ f x)
include hopen hnn

/-- Every sublevel set `{f ≤ e}` is open when those at natural bounds are. -/
theorem isOpen_le_of_sublevels (e : WithBot ℕ∞) : IsOpen {x | f x ≤ e} := by
  induction e using WithBot.recBotCoe with
  | bot =>
    convert isOpen_empty
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, le_bot_iff]
    intro h
    have := hnn x
    rw [h] at this
    exact absurd this (by decide)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      convert isOpen_univ
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact WithBot.coe_top (α := ℕ∞) ▸ le_top
    | coe m =>
      simpa only [WithBot.coe_natCast] using hopen m

/-- Every strict sublevel set `{f < e}` is open when the sublevels at natural bounds are. -/
theorem isOpen_lt_of_sublevels (e : WithBot ℕ∞) : IsOpen {x | f x < e} := by
  induction e using WithBot.recBotCoe with
  | bot =>
    convert isOpen_empty
    ext x
    simp
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have : {x | f x < ((⊤ : ℕ∞) : WithBot ℕ∞)} = ⋃ m : ℕ, {x | f x ≤ m} := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
        constructor
        · intro h
          induction hx : f x using WithBot.recBotCoe with
          | bot => exact ⟨0, by simp⟩
          | coe a =>
            rw [hx] at h
            induction a using ENat.recTopCoe with
            | top => exact absurd h (lt_irrefl _)
            | coe n => exact ⟨n, by simp⟩
        · rintro ⟨m, hm⟩
          refine lt_of_le_of_lt hm ?_
          rw [← WithBot.coe_natCast]
          exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top m)
      rw [this]
      exact isOpen_iUnion hopen
    | coe m =>
      cases m with
      | zero =>
        convert isOpen_empty
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        simpa using hnn x
      | succ m =>
        have : {x | f x < (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)} = {x | f x ≤ m} := by
          ext x
          simp only [Set.mem_ofPred_eq]
          rw [WithBot.coe_natCast, Nat.cast_add, Nat.cast_one]
          exact ENat.WithBot.lt_add_one_iff
        rw [this]
        exact hopen m

/-- A level set `{f = e}` is locally closed: it is the open set `{f ≤ e}` minus the open
set `{f < e}`. -/
theorem isLocallyClosed_level_of_sublevels (e : WithBot ℕ∞) : IsLocallyClosed {x | f x = e} := by
  refine ⟨{x | f x ≤ e}, {x | f x < e}ᶜ, isOpen_le_of_sublevels f hopen hnn e,
    (isOpen_lt_of_sublevels f hopen hnn e).isClosed_compl, ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_lt]
  constructor
  · intro h
    exact ⟨h.le, h.ge⟩
  · rintro ⟨h₁, h₂⟩
    exact le_antisymm h₁ h₂

end Levels

/-- Adding a natural number is injective on `WithBot ℕ∞`. -/
theorem withBot_add_natCast_cancel {x y : WithBot ℕ∞} (d : ℕ)
    (h : x + (d : WithBot ℕ∞) = y + (d : WithBot ℕ∞)) : x = y := by
  have hd : (d : WithBot ℕ∞) ≠ ⊥ := by
    rw [← WithBot.coe_natCast]
    exact WithBot.coe_ne_bot
  induction x using WithBot.recBotCoe with
  | bot =>
    have h' : y + (d : WithBot ℕ∞) = ⊥ := by rw [← h]; exact WithBot.bot_add _
    rcases WithBot.add_eq_bot.mp h' with hy | hy
    · exact hy.symm
    · exact absurd hy hd
  | coe a =>
    induction y using WithBot.recBotCoe with
    | bot =>
      have h' : (a : WithBot ℕ∞) + (d : WithBot ℕ∞) = ⊥ := by rw [h]; exact WithBot.bot_add _
      rcases WithBot.add_eq_bot.mp h' with hy | hy
      · exact absurd hy WithBot.coe_ne_bot
      · exact absurd hy hd
    | coe b =>
      rw [← WithBot.coe_natCast, ← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_inj] at h
      exact congrArg _ (WithTop.add_right_cancel (ENat.natCast_ne_top d) h)

variable {S : Scheme.{u}} {G : GroupScheme S} {V : Over S}

/-- The identity section `v ↦ (1, v)` of the stabilizer scheme over `V`. -/
def stabilizerUnit (a : SchemeAction G V) :
    V ⟶ Limits.pullback (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V)) :=
  pullback.lift (lift 1 (𝟙 V)) (𝟙 V) (by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, Category.id_comp]
      exact a.act_one (𝟙 V)
    · simp)

theorem stabilizerUnit_snd (a : SchemeAction G V) :
    stabilizerUnit a ≫ pullback.snd (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V)) = 𝟙 V :=
  pullback.lift_snd _ _ _

/-- The orbit-dimension stratum of an action of a group scheme locally of finite type is
locally closed. -/
theorem isLocallyClosed_orbitStratum (a : SchemeAction G V) (hG : LocallyOfFiniteType G.X.hom)
    (d : ℕ) : IsLocallyClosed {v : V.left | HasOrbitDimension a v d} := by
  set σ := pullback.snd (lift a.hom (snd G.X V)) (lift (𝟙 V) (𝟙 V)) with hσ
  have := StabilizerFibre.locallyOfFiniteType_proj a hG
  let ε := (stabilizerUnit a).left
  have hεσ : ∀ v, σ.left (ε v) = v := by
    intro v
    have h : ε ≫ σ.left = 𝟙 V.left := by
      rw [← Over.comp_left, stabilizerUnit_snd]
      rfl
    exact congrArg (fun φ : V.left ⟶ V.left => φ v) h
  let δ : V.left → WithBot ℕ∞ := fun v => topologicalKrullDim (σ.left.fiber v)
  have hδ : ∀ v, δ v = relativeTopologicalKrullDimAt σ.left (ε v) := by
    intro v
    rw [stabilizerFibreLocalDimension S G V a hG (ε v), hεσ v]
  have hopen : ∀ m : ℕ, IsOpen {v | δ v ≤ m} := by
    intro m
    have h := (relativeDimensionSublevelOpenness_proof σ.left m).preimage ε.continuous
    convert h using 1
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hδ v]
    rfl
  have hnn : ∀ v, 0 ≤ δ v := fun v => (hδ v).symm ▸ relativeTopologicalKrullDimAt_nonneg _ _
  by_cases hex : ∃ e : WithBot ℕ∞, topologicalKrullDim G.X.left = e + (d : WithBot ℕ∞)
  · obtain ⟨e, he⟩ := hex
    convert isLocallyClosed_level_of_sublevels δ hopen hnn e using 1
    ext v
    change topologicalKrullDim G.X.left = δ v + (d : WithBot ℕ∞) ↔ δ v = e
    rw [he]
    constructor
    · intro h
      exact (withBot_add_natCast_cancel d h).symm
    · rintro rfl
      rfl
  · convert isClosed_empty.isLocallyClosed
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    exact hex ⟨_, h⟩

end UnipotentOrbitStratum

open UnipotentOrbitStratum in
/-- Conrad's Example 5.5, clause 1: the orbit-dimension strata of a unipotent algebraic
group acting on a reduced scheme of finite type are locally closed. -/
theorem unipotentOrbitStratumLocallyClosed :
    UnipotentOrbitStratumLocallyClosedStatement.{u} := by
  intro K _ _ _ G hG V _ a d
  exact isLocallyClosed_orbitStratum a hG.2.1 d

end Langlands.AlgebraicGeometry.AlgebraicSpace
