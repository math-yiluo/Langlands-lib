import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerTorusSumCoefficient
import Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement
import Langlands.AllField.Group.GL.BlockModulusSupplement
import Langlands.AllField.Group.GL.CompactOpenSupplement
/-!
# Whittaker values on the antidominant torus cone as smooth matrix coefficients

For a smooth representation `π` of `GL_(m+1)(F)`, a Whittaker functional `ℓ` and a
vector `v`, there are a positive principal level `K(r)` fixing `v` and a smooth
functional `L`, fixed by `K(r)`, such that `L (π(ϖ^lam) v) = ℓ (π(ϖ^lam) v)` for every
antitone exponent vector `lam`. The functional is the average
`L w = ∫_{K(r)} ℓ (π(g⁻¹) w) dg` for the Haar measure of unit mass on `K(r)`; the Iwahori
factorization of `K(r)` shows that the integrand is constant on the antitone cone.
-/

noncomputable section

open MeasureTheory Topology

namespace Langlands.AllField.RankinSelberg.SquareIntegrableWhittakerTorusSum
open Langlands.RankinSelberg.SquareIntegrableWhittakerTorusSum hiding exists_smooth_eq_on_antitone
open Langlands.AllField.RankinSelberg.SquareIntegrableWhittakerTorusSum
open Langlands.RankinSelberg
open Langlands.AllField.RankinSelberg

universe uG uV uF

/-! ### Averaging a functional over a compact open subgroup -/

section Averaging



end Averaging

/-! ### Principal levels and the antitone torus cone

The conjugation steps reuse the public `GeneralLinear.principal_upper_conj` and
`GeneralLinear.principal_lower_inv_conj` from
`Langlands.Group.GL.PrincipalLevelDominance`. -/

section Conjugation

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear


end Conjugation

/-! ### Smooth functionals agreeing with a Whittaker functional on the antitone cone -/

section Coefficient

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker
open Langlands.HarmonicAnalysis

/-- For a smooth representation of `GL_(m+1)(F)`, a standard Whittaker functional `ℓ`, a
vector `v` and an element `ϖ` of valuation at most one, there are a positive principal level
`K(r)` fixing `v` and a smooth functional `L`, invariant under `K(r)`, with
`L (π(ϖ^lam) v) = ℓ (π(ϖ^lam) v)` for every antitone exponent vector `lam`. -/
theorem exists_smooth_eq_on_antitone (F : Type uF) [Field F]
    (T : LocalFieldData F) (m : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (ψ : UnitaryAdditiveCharacter F) {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V),
      IsSmooth π → ∀ (ℓ : glFunctionals ψ m π) (v : V) (ϖ : Fˣ),
      ValuativeRel.valuation F (ϖ : F) ≤ 1 →
      ∃ r : ℕ, 0 < r ∧
        (∀ g ∈ Conductor.principalLevelSubgroup F m r, π g v = v) ∧
        ∃ L : Module.Dual ℂ V, L ∈ smoothVectors π.dual ∧
          (∀ g ∈ Conductor.principalLevelSubgroup F m r, ∀ w, L (π g w) = L w) ∧
          ∀ lam : Fin (m + 1) → ℤ, Antitone lam →
            L (π (Iwasawa.torus ϖ lam) v) = ℓ.val (π (Iwasawa.torus ϖ lam) v) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.generalLinearTopologicalGroup (m + 1)
  intro ψ V _ _ π hπ ℓ v ϖ hϖ
  let := borel (Langlands.GeneralLinear (m + 1) F)
  have : BorelSpace (Langlands.GeneralLinear (m + 1) F) := ⟨rfl⟩
  -- A level fixing `v`.
  obtain ⟨Kv, hKv⟩ := hπ v
  have hfix : ∀ g ∈ Kv, π g v = v := fun g hg =>
    (Representation.mem_invariants _ v).1 hKv ⟨g, hg⟩
  obtain ⟨r₁, hr₁, hK₁⟩ := Conductor.exists_pos_principalLevelOpenSubgroup_subset F m
    (Kv.isOpen.mem_nhds Kv.one_mem)
  -- A level inside the kernel of the standard character.
  have hker : IsOpen ((standardCharacter ψ m).ker : Set (upperUnipotent (m + 1) F)) := by
    let := T.upperUnipotentNonarchimedean (m + 1)
    exact isOpen_ker_of_continuous_complex_character _
      (standardCharacterContinuous ψ m).continuous
  have hN := hker.mem_nhds (standardCharacter ψ m).ker.one_mem
  rw [Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hN
  obtain ⟨O, hO, hOK⟩ := hN
  obtain ⟨r₂, -, hK₂⟩ := Conductor.exists_pos_principalLevelOpenSubgroup_subset F m hO
  set r := max r₁ r₂
  have hr : 0 < r := lt_max_of_lt_left hr₁
  have hv : ∀ g ∈ Conductor.principalLevelSubgroup F m r, π g v = v := fun g hg =>
    hfix g (hK₁ (Conductor.principalLevelSubgroup_antitone F m (le_max_left _ _) hg))
  have hℓ : ∀ u ∈ upperUnipotent (m + 1) F,
      u ∈ Conductor.principalLevelSubgroup F m r → ∀ w, ℓ.val (π u w) = ℓ.val w := by
    intro u hu hK w
    have h₁ : u ∈ O :=
      hK₂ (Conductor.principalLevelSubgroup_antitone F m (le_max_right _ _) hK)
    have h₂ : (⟨u, hu⟩ : upperUnipotent (m + 1) F) ∈ Subtype.val ⁻¹' O := h₁
    have hθ := MonoidHom.mem_ker.mp (hOK h₂)
    have h := ℓ.property ⟨u, hu⟩ w
    rw [hθ, Units.val_one, one_mul] at h
    exact h
  let K := Conductor.principalLevelOpenSubgroup F m r
  have hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 1) F)) :=
    Conductor.isCompact_principalLevelOpenSubgroup F m r
  refine ⟨r, hr, hv, averagedFunctional π hπ K hK ℓ.val,
    averagedFunctional_mem_smoothVectors π hπ K hK ℓ.val,
    fun g hg w => averagedFunctional_apply_mul π hπ K hK ℓ.val g hg w, ?_⟩
  intro lam hlam
  exact averagedFunctional_apply_of_forall π hπ K hK ℓ.val
    (fun g hg => apply_inv_torus_eq hr hℓ hv hϖ hlam hg)

end Coefficient

end Langlands.AllField.RankinSelberg.SquareIntegrableWhittakerTorusSum
