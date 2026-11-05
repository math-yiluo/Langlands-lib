import Langlands.Representation.Exponents.CentralDecompositionAlgebra
import Mathlib.RingTheory.Finiteness.Basic

noncomputable section

open scoped IsMulCommutative

namespace Langlands.CentralDecomposition

universe uR uG uV

variable {R : Type uR} [Field R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- Open fixed spaces are stable under the full center. -/
theorem admissible_centerFinite [TopologicalSpace G]
    (ρ : Representation R G V) (hρ : IsAdmissible ρ) : IsCenterFinite ρ := by
  intro v
  obtain ⟨K, hv⟩ := hρ.1 v
  let W : Subrepresentation (ρ.comp (Subgroup.center G).subtype) :=
    { toSubmodule := fixedVectors ρ K.toSubgroup
      apply_mem_toSubmodule := by
        intro z w hw
        change ∀ k : K, ρ (k : G) (ρ (z : G) w) = ρ (z : G) w
        change ∀ k : K, ρ (k : G) w = w at hw
        intro k
        calc ρ (k : G) (ρ (z : G) w) = ρ (z : G) (ρ (k : G) w) := by
               rw [← Module.End.mul_apply, ← Module.End.mul_apply,
                 ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.property (k : G)]
             _ = ρ (z : G) w := by rw [hw k] }
  exact ⟨W, hρ.2 K, hv⟩

/-- All algebraic characters give an independent family, even before smoothness. -/
theorem algebraic_independent (ρ : Representation R G V) :
    iSupIndep (fun χ : Subgroup.center G →* Rˣ =>
      (generalizedCentralCharacterSpace ρ χ).toSubmodule) := by
  let f : Subgroup.center G → Module.End R V := fun z => ρ (z : G)
  have hi := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (by
      change Commute (ρ (j : G)) (ρ (i : G))
      exact (show Commute (j : G) (i : G) from
        Subgroup.mem_center_iff.mp i.property (j : G)).map ρ) μ)
  let c : (Subgroup.center G →* Rˣ) → (Subgroup.center G → R) :=
    fun χ z => (χ z : R)
  have hc : Function.Injective c := by
    intro χ ψ h
    apply MonoidHom.ext
    intro z
    apply Units.ext
    exact congrFun h z
  apply (hi.comp hc).mono
  intro χ v hv
  obtain ⟨n, hn⟩ := (mem_generalizedCentralCharacterSpace ρ χ v).mp hv
  change v ∈ ⨅ z : Subgroup.center G, Module.End.maxGenEigenspace (ρ (z : G)) (χ z : R)
  rw [Submodule.mem_iInf]
  intro z
  exact Module.End.mem_genEigenspace_top.mpr ⟨n, hn z⟩

/-- A nonzero smooth generalized-character vector forces an open character kernel. -/
theorem open_kernel_of_nonzero [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation R G V) (hρ : IsSmooth ρ)
    (χ : Subgroup.center G →* Rˣ) {v : V} (hv : v ≠ 0)
    (hχv : v ∈ generalizedCentralCharacterSpace ρ χ) :
    IsOpen (χ.ker : Set (Subgroup.center G)) := by
  obtain ⟨K, hK⟩ := hρ v
  obtain ⟨n, hn⟩ := (mem_generalizedCentralCharacterSpace ρ χ v).mp hχv
  let H : Subgroup (Subgroup.center G) := K.toSubgroup.comap (Subgroup.center G).subtype
  have hH : IsOpen (H : Set (Subgroup.center G)) :=
    K.isOpen.preimage continuous_subtype_val
  apply Subgroup.isOpen_mono (H₁ := H) (H₂ := χ.ker) ?_ hH
  intro z hz
  have hfix : ρ (z : G) v = v := hK ⟨(z : G), hz⟩
  have hpow (m : ℕ) : ((ρ (z : G) - (χ z : R) • 1) ^ m) v =
      (1 - (χ z : R)) ^ m • v := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hfix]
      rw [show v - (χ z : R) • v = (1 - (χ z : R)) • v by rw [sub_smul, one_smul],
        smul_smul, pow_succ]
  have hz0 : (1 - (χ z : R)) ^ n = 0 :=
    (smul_eq_zero.mp ((hpow n).symm.trans (hn z))).resolve_right hv
  have hz1 : (χ z : R) = 1 := (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz0)).symm
  apply Units.ext
  simpa using hz1

/-- Center-finite representations are spanned by their uniform algebraic spaces. -/
theorem algebraic_spanning [IsAlgClosed R] (ρ : Representation R G V)
    (hρ : IsCenterFinite ρ) :
    (⨆ χ : Subgroup.center G →* Rˣ,
      (generalizedCentralCharacterSpace ρ χ).toSubmodule) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨W, hW, hv⟩ := hρ v
  let : Module.Finite R W.toSubmodule := hW
  have hspan := finite_action_spanning W.toRepresentation
  have hle : (⨆ (χ : Subgroup.center G →* Rˣ) (n : ℕ),
        ⨅ z : Subgroup.center G,
          Module.End.genEigenspace (W.toRepresentation z) (χ z : R) n) ≤
      (⨆ χ : Subgroup.center G →* Rˣ,
        (generalizedCentralCharacterSpace ρ χ).toSubmodule).comap W.toSubmodule.subtype := by
    refine iSup_le fun χ => iSup_le fun n => ?_
    intro w hw
    apply Submodule.mem_iSup_of_mem χ
    apply (mem_generalizedCentralCharacterSpace ρ χ (w : V)).mpr
    refine ⟨n, fun z => ?_⟩
    rw [Submodule.mem_iInf] at hw
    exact (Module.End.mem_genEigenspace_nat.mp
      (Module.End.mapsTo_genEigenspace_of_comp W.toSubmodule.subtype
        (by rfl) (χ z : R) n (hw z)))
  rw [hspan] at hle
  exact hle (show (⟨v, hv⟩ : W.toSubmodule) ∈ ⊤ from trivial)

/-- Smoothness removes all nonsmooth algebraic characters from the span. -/
theorem smooth_spanning [TopologicalSpace G] [IsTopologicalGroup G] [IsAlgClosed R]
    (ρ : Representation R G V) (hs : IsSmooth ρ) (hc : IsCenterFinite ρ) :
    (⨆ χ : {χ : Subgroup.center G →* Rˣ //
        IsOpen (χ.ker : Set (Subgroup.center G))},
      (generalizedCentralCharacterSpace ρ χ.val).toSubmodule) = ⊤ := by
  apply top_unique
  rw [← algebraic_spanning ρ hc]
  refine iSup_le fun χ => ?_
  intro v hv
  by_cases hz : v = 0
  · subst v
    exact Submodule.zero_mem _
  · exact Submodule.mem_iSup_of_mem ⟨χ, open_kernel_of_nonzero ρ hs χ hz hv⟩ hv

/-- Passing to the actual group-algebra submodules preserves a spanning family. -/
theorem asSubmodule_iSup_eq_top {ι : Type*} (ρ : Representation R G V)
    (S : ι → Subrepresentation ρ) (hS : (⨆ i, (S i).toSubmodule) = ⊤) :
    (⨆ i, (S i).asSubmodule) = ⊤ := by
  apply Submodule.restrictScalars_injective R (MonoidAlgebra R G) ρ.asModule
  rw [Submodule.restrictScalars_iSup, Submodule.restrictScalars_top]
  exact hS

/-- Compactness of the actual group-algebra module gives finite support and one
positive exponent, simultaneously for all algebraic central characters. -/
theorem finite_support_uniform [IsAlgClosed R] (ρ : Representation R G V)
    (hc : IsCenterFinite ρ) [Module.Finite (MonoidAlgebra R G) ρ.asModule] :
    {χ : Subgroup.center G →* Rˣ | generalizedCentralCharacterSpace ρ χ ≠ ⊥}.Finite ∧
    ∃ n : ℕ, 0 < n ∧ ∀ χ : Subgroup.center G →* Rˣ,
      generalizedCentralCharacterSpace ρ χ = centralCharacterSpace ρ χ n := by
  classical
  have hi := algebraic_independent ρ
  have hspan := algebraic_spanning ρ hc
  have haspan := asSubmodule_iSup_eq_top ρ
    (fun χ => generalizedCentralCharacterSpace ρ χ) hspan
  have hfg : (⊤ : Submodule (MonoidAlgebra R G) ρ.asModule).FG := Module.Finite.fg_top
  have hk := (Submodule.fg_iff_compact _).mp hfg
  obtain ⟨s, hs⟩ := hk.exists_finset_of_le_iSup
    (fun χ : Subgroup.center G →* Rˣ => (generalizedCentralCharacterSpace ρ χ).asSubmodule)
    haspan.ge
  have hs' : (⨆ χ ∈ s, (generalizedCentralCharacterSpace ρ χ).asSubmodule) = ⊤ :=
    top_unique hs
  have hsR := congrArg (Submodule.restrictScalars R) hs'
  simp only [Submodule.restrictScalars_iSup, Submodule.restrictScalars_top] at hsR
  have hfin : {χ : Subgroup.center G →* Rˣ |
      generalizedCentralCharacterSpace ρ χ ≠ ⊥}.Finite := by
    apply s.finite_toSet.subset
    intro χ hχ
    apply hi.mem_of_biSup_eq_top hsR
    intro h
    exact hχ (Subrepresentation.toSubmodule_injective h)
  let D : ℕ →o Submodule (MonoidAlgebra R G) ρ.asModule :=
    { toFun := fun n => ⨆ χ : Subgroup.center G →* Rˣ, (centralCharacterSpace ρ χ n).asSubmodule
      monotone' := by
        intro m n hmn
        exact iSup_mono fun χ => (centralCharacterSpace_mono ρ χ hmn) }
  have hD : (⨆ n, D n) = ⊤ := by
    apply Submodule.restrictScalars_injective R (MonoidAlgebra R G) ρ.asModule
    change (⨆ (n : ℕ) (χ : Subgroup.center G →* Rˣ),
      (centralCharacterSpace ρ χ n).asSubmodule).restrictScalars R =
      (⊤ : Submodule (MonoidAlgebra R G) ρ.asModule).restrictScalars R
    simp only [Submodule.restrictScalars_iSup, Submodule.restrictScalars_top]
    change (⨆ (n : ℕ) (χ : Subgroup.center G →* Rˣ),
      (centralCharacterSpace ρ χ n).toSubmodule) = ⊤
    rw [iSup_comm]
    exact hspan
  obtain ⟨m, hm⟩ := hfg.stabilizes_of_iSup_eq D hD
  have hm' : D (m + 1) = ⊤ := top_unique (hm.le.trans (D.monotone (Nat.le_succ m)))
  have hmR := congrArg (Submodule.restrictScalars R) hm'
  change (⨆ χ : Subgroup.center G →* Rˣ,
    (centralCharacterSpace ρ χ (m + 1)).asSubmodule).restrictScalars R =
    (⊤ : Submodule (MonoidAlgebra R G) ρ.asModule).restrictScalars R at hmR
  simp only [Submodule.restrictScalars_iSup, Submodule.restrictScalars_top] at hmR
  have heq : (fun χ : Subgroup.center G →* Rˣ =>
      (centralCharacterSpace ρ χ (m + 1)).toSubmodule) =
      (fun χ => (generalizedCentralCharacterSpace ρ χ).toSubmodule) := by
    apply (hi.le_iff_eq_of_iSup_eq_top hmR).mp
    intro χ
    exact le_iSup (fun n => (centralCharacterSpace ρ χ n).toSubmodule) (m + 1)
  refine ⟨hfin, m + 1, Nat.succ_pos m, fun χ => ?_⟩
  apply Subrepresentation.toSubmodule_injective
  exact (congrFun heq χ).symm

end Langlands.CentralDecomposition

namespace Langlands

universe uR uG uV

/-- Casselman's center-finiteness and full uniform central-character decomposition. -/
theorem centralCharacterDecomposition :
    CentralCharacterDecompositionStatement.{uR, uG, uV} := by
  intro R _ _ G _ _ _ _ _ _ V _ _ ρ
  refine ⟨CentralDecomposition.admissible_centerFinite ρ, ?_⟩
  intro _ hs hc
  refine ⟨⟨(CentralDecomposition.algebraic_independent ρ).comp Subtype.val_injective,
    CentralDecomposition.smooth_spanning ρ hs hc⟩, ?_⟩
  intro hfg
  let : Module.Finite (MonoidAlgebra R G) ρ.asModule := hfg
  obtain ⟨hfin, n, hn, heq⟩ := CentralDecomposition.finite_support_uniform ρ hc
  refine ⟨hfin.subset (fun χ hχ => hχ.2), n, hn, fun χ _ => heq χ⟩

end Langlands
