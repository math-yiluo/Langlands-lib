import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Jacquet.Coinvariants
import Langlands.Representation.Jacquet.ExactProof
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Analysis.Local.QuotientTopology

/-!
# Jacquet vanishing for compact induction detected by a scalar

Let `U` be a normal subgroup of a locally compact topological group `P` in which
every compact subset lies in a compact open subgroup, and let `S` be a closed
subgroup of `P`. If an element of `S ∩ U` acts on the inducing representation by a
scalar different from one, then the `U`-coinvariants of `c-Ind_S^P σ` vanish.
-/

noncomputable section

namespace Langlands.Whittaker

open Induction

universe uP uW

variable {P : Type uP} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A compactly induced function is supported in `S * C` for a compact set `C`. -/
theorem exists_isCompact_support_subset_mul [LocallyCompactSpace P]
    (S : Subgroup P) (hS : IsClosed (S : Set P)) (σ : Representation ℂ S W)
    (f : CompactFunctions S σ) :
    ∃ C : Set P, IsCompact C ∧
      ∀ g : P, eval S σ f.1 g ≠ 0 → ∃ s : S, ∃ c ∈ C, g = (s : P) * c := by
  obtain ⟨C, hC, hCim⟩ :=
    QuotientIntegration.leftQuotient_exists_isCompact_image S hS f.2
  refine ⟨C, hC, fun g hg => ?_⟩
  have hmem : quotientMap S g ∈ quotientSupport S (eval S σ f.1) := ⟨g, hg, rfl⟩
  rw [← hCim] at hmem
  obtain ⟨c, hc, hcg⟩ := hmem
  have hgc : g * c⁻¹ ∈ S := QuotientGroup.rightRel_apply.mp (Quotient.exact hcg)
  exact ⟨⟨g * c⁻¹, hgc⟩, c, hc, by simp⟩

/-- If an element of `S ∩ U` acts on `σ` by a scalar `c ≠ 1`, the actual
`U`-coinvariants of the compact induction `c-Ind_S^P σ` are zero. -/
theorem subsingleton_coinvariants_compactInduced_of_scalar [LocallyCompactSpace P]
    (U S : Subgroup P) [hUn : U.Normal] (hS : IsClosed (S : Set P))
    (hU : ∀ C : Set U, IsCompact C →
      ∃ K : OpenSubgroup U, IsCompact (K : Set U) ∧ C ⊆ (K : Set U))
    (σ : Representation ℂ S W) (x : S) (hx : (x : P) ∈ U) (c : ℂ) (hc : c ≠ 1)
    (hσ : ∀ w, σ x w = c • w) :
    Subsingleton (Jacquet.Coinvariants (compactInduced S σ) U) := by
  let ρ := (compactInduced S σ).comp U.subtype
  have hρ : IsSmooth ρ :=
    isSmooth_comp U.subtype continuous_subtype_val (compactInduced_smooth S σ)
  suffices hzero : ∀ f, Jacquet.mk (compactInduced S σ) U f = 0 by
    refine ⟨fun a b => ?_⟩
    obtain ⟨f, rfl⟩ := Jacquet.mk_surjective (compactInduced S σ) U a
    obtain ⟨g, rfl⟩ := Jacquet.mk_surjective (compactInduced S σ) U b
    rw [hzero f, hzero g]
  intro f
  obtain ⟨C, hC, hsupp⟩ := exists_isCompact_support_subset_mul S hS σ f
  -- The conjugates of `x` by the compact set `C` lie in one compact open subgroup.
  let φ : P → U := fun p => ⟨p⁻¹ * (x : P) * p, by
    simpa using hUn.conj_mem (x : P) hx p⁻¹⟩
  have hφ : Continuous φ :=
    ((continuous_inv.mul continuous_const).mul continuous_id).subtype_mk _
  obtain ⟨K, hK, hCK⟩ := hU (φ '' C) (hC.image hφ)
  let h := Compact.averageMap ρ hρ K hK f
  have hfix : ∀ k : K, ρ (k : U) h = h := fun k =>
    Compact.averageMap_mem_fixedVectors ρ hρ K hK f k
  -- Evaluation of the average vanishes wherever every translate of `f` vanishes.
  have heval_zero (g : P) (hg : ∀ k : K, eval S σ f.1 (g * ((k : U) : P)) = 0) :
      eval S σ h.1 g = 0 := by
    classical
    let := Compact.finite_orbit_of_smooth ρ hρ K hK f
    let := Fintype.ofFinite (Compact.orbit (ρ.comp K.toSubgroup.subtype) f)
    let Z : Submodule ℂ (CompactFunctions S σ) :=
      { carrier := {v | eval S σ v.1 g = 0}
        add_mem' := by
          intro a b ha hb
          change eval S σ a.1 g + eval S σ b.1 g = 0
          rw [show eval S σ a.1 g = 0 from ha, show eval S σ b.1 g = 0 from hb, add_zero]
        zero_mem' := rfl
        smul_mem' := by
          intro r a ha
          change r • eval S σ a.1 g = 0
          rw [show eval S σ a.1 g = 0 from ha, smul_zero] }
    have hmem : h ∈ Z := by
      change Compact.orbitMean (ρ.comp K.toSubgroup.subtype) f ∈ Z
      rw [Compact.orbitMean_eq_finiteMean]
      unfold Compact.finiteMean
      refine Z.smul_mem _ (Z.sum_mem fun y _ => ?_)
      obtain ⟨k, hk⟩ := y.property
      change eval S σ y.val.1 g = 0
      rw [← hk]
      exact hg k
    exact hmem
  -- At a point of `C`, the scalar action of `x` forces the average to vanish.
  have heval_C (q : P) (hq : φ q ∈ (K : Set U)) : eval S σ h.1 q = 0 := by
    have hcov := h.1.1.property x q
    have htrans := congrArg (fun v : CompactFunctions S σ => eval S σ v.1 q)
      (hfix ⟨φ q, hq⟩)
    change h.1.1.1 (q * (q⁻¹ * (x : P) * q)) = h.1.1.1 q at htrans
    rw [show q * (q⁻¹ * (x : P) * q) = (x : P) * q by group] at htrans
    change h.1.1.1 ((x : P) * q) = σ x (h.1.1.1 q) at hcov
    rw [htrans, hσ] at hcov
    have h1 : (1 - c) • h.1.1.1 q = 0 := by
      rw [sub_smul, one_smul, ← hcov, sub_self]
    exact (smul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hc.symm)
  have hh : h = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change eval S σ h.1 g = 0
    by_cases hg : ∀ k : K, eval S σ f.1 (g * ((k : U) : P)) = 0
    · exact heval_zero g hg
    · push Not at hg
      obtain ⟨k, hk⟩ := hg
      obtain ⟨s, q, hqC, hgk⟩ := hsupp _ hk
      have hkg := congrArg (fun v : CompactFunctions S σ => eval S σ v.1 g) (hfix k)
      change h.1.1.1 (g * ((k : U) : P)) = h.1.1.1 g at hkg
      have hcov := h.1.1.property s q
      change h.1.1.1 ((s : P) * q) = σ s (h.1.1.1 q) at hcov
      change h.1.1.1 g = 0
      have hq0 := heval_C q (hCK ⟨q, hqC, rfl⟩)
      change h.1.1.1 q = 0 at hq0
      rw [← hkg, hgk, hcov, hq0, map_zero]
  have hker : f ∈ Representation.Coinvariants.ker (ρ.comp K.toSubgroup.subtype) :=
    (Compact.averageMap_eq_zero_iff ρ hρ K hK f).mp hh
  exact (Jacquet.mk_eq_zero _ _ f).mpr (coinvariants_ker_comp_subgroup_le ρ K.toSubgroup hker)

end Langlands.Whittaker
