import Langlands.BushnellKutzko.SplitTypeJacquet.StandardType
import Langlands.BushnellKutzko.SplitTypeJacquet.FiniteReorder
import Langlands.BushnellKutzko.SplitTypeJacquet.CoarseCut

/-! # Jacquet nonvanishing for inhomogeneous level-zero types in standard coordinates

Let `E` be a finite cuspidal datum with two different block labels, and let `π` be an admissible
smooth representation of `GL_{m+1}(F)` with a nonzero intertwiner from the standard type
`stdType E`. Reorder the blocks of `E` so that some cut `j` separates the labels: no block before
the cut has the label of a block after it. The reordering does not change the parabolic
intertwining dimension into the vectors fixed by the principal congruence subgroup. The compression criterion for the reordered type then gives a
nonzero Jacquet module along the coarse corner, hence along a conjugate of the unipotent radical
of a proper two-block parabolic. -/

open Matrix ValuativeRel Langlands.GeneralLinear Langlands.Geometric Langlands.FiniteGeneralLinear
  Langlands.Jacquet

noncomputable section

namespace Langlands.BushnellKutzko.SplitTypeJacquet

open Langlands.ProductLeviChamber (twoBlock)
open Langlands.Whittaker.UpperUnipotentCoinvariant (cutShape_parabolic_ne_top)

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {m : ℕ}

/-- `J1` of a block function, as an open subgroup. -/
def J1Open (blk : Fin (m + 1) → ℕ) : OpenSubgroup (GL (Fin (m + 1)) F) where
  toSubgroup := J1 F blk
  isOpen' := Subgroup.isOpen_mono (principalLevel_one_le_J1 blk)
    (Conductor.principalLevelOpenSubgroup F m 1).isOpen

theorem isCompact_J1Open (blk : Fin (m + 1) → ℕ) :
    IsCompact ((J1Open blk : OpenSubgroup (GL (Fin (m + 1)) F)) : Set (GL (Fin (m + 1)) F)) := by
  refine (Conductor.isCompact_levelOpenSubgroup F m 0).of_isClosed_subset
    (J1Open blk).isClosed ?_
  intro g hg
  change g ∈ Conductor.levelSubgroup F m 0
  rw [Conductor.levelSubgroup_zero]
  exact J0_le_Kint _ (J1_le_J0 hg)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (m + 1)) F) V)

/-- An intertwiner from a standard type takes values fixed by the principal congruence subgroup
and is equivariant for the parabolic over the residue field. -/
theorem exists_parabolicIntertwiner (E : HarishChandraDatum (m + 1) 𝓀[F])
    (g : E.leviRep →ₗ[ℂ] V)
    (hg : ∀ (x : J0 F (blkOf E.shape)) (w : E.leviRep), g (stdType E x w) = π x (g w)) :
    ∃ gb : E.leviRep →ₗ[ℂ] fixK1 π, (∀ w, (gb w : V) = g w) ∧
      ∀ q : E.shape.parabolic 𝓀[F],
        gb ∘ₗ parabolicRep E q = descended π (q : GeneralLinear (m + 1) 𝓀[F]) ∘ₗ gb := by
  have hfix : ∀ w, g w ∈ fixK1 π := by
    intro w
    rw [mem_fixK1_iff]
    intro k hk
    have hkJ1 : k ∈ J1 F (blkOf E.shape) := principalLevel_one_le_J1 _ hk
    rw [← hg ⟨k, J1_le_J0 hkJ1⟩, stdType_eq_one_of_mem_J1 E _ hkJ1]
    rfl
  refine ⟨g.codRestrict (fixK1 π) hfix, fun w => rfl, fun q => ?_⟩
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  let x : Kint F m := IntegralReduction.lift (ValuativeRel.valuation F).integer m q
  have hxred : red F m x = q :=
    IntegralReduction.reduction_lift (ValuativeRel.valuation F).integer m q
  have hxJ : (x : GL (Fin (m + 1)) F) ∈ J0 F (blkOf E.shape) :=
    (red_mem_parabolic_iff x).mp (by rw [hxred]; exact q.2)
  have e1 : stdType E ⟨x, hxJ⟩ = parabolicRep E q := by
    change parabolicRep E (redJ0 E.shape ⟨x, hxJ⟩) = _
    congr 1
    apply Subtype.ext
    rw [coe_redJ0]
    exact hxred
  change g (parabolicRep E q w) = ((descended π (q : GeneralLinear (m + 1) 𝓀[F])
    (g.codRestrict (fixK1 π) hfix w) : fixK1 π) : V)
  rw [← e1, hg, ← hxred, descended_red]
  rfl

/-- A parabolic intertwiner into the fixed vectors gives an intertwiner from the standard
type. -/
theorem stdType_intertwiner_of_parabolic (E : HarishChandraDatum (m + 1) 𝓀[F])
    (gb : E.leviRep →ₗ[ℂ] fixK1 π)
    (hgb : ∀ q : E.shape.parabolic 𝓀[F],
      gb ∘ₗ parabolicRep E q = descended π (q : GeneralLinear (m + 1) 𝓀[F]) ∘ₗ gb)
    (x : J0 F (blkOf E.shape)) (w : E.leviRep) :
    ((fixK1 π).subtype ∘ₗ gb) (stdType E x w) = π x (((fixK1 π).subtype ∘ₗ gb) w) := by
  have h := LinearMap.congr_fun (hgb (redJ0 E.shape x)) w
  change ((gb (parabolicRep E (redJ0 E.shape x) w) : fixK1 π) : V) = _
  rw [show gb (parabolicRep E (redJ0 E.shape x) w) = _ from h]
  change ((descended π ((redJ0 E.shape x : E.shape.parabolic 𝓀[F]) :
    GeneralLinear (m + 1) 𝓀[F]) (gb w) : fixK1 π) : V) = _
  rw [coe_redJ0, descended_red]
  rfl

/-- **Jacquet nonvanishing for inhomogeneous level-zero types, in standard coordinates.** -/
theorem standard_jacquet (hπ : IsAdmissible π) (E : HarishChandraDatum (m + 1) 𝓀[F])
    (hE : ∃ i i', E.blockLabel i ≠ E.blockLabel i') (f : E.leviRep →ₗ[ℂ] V)
    (hf : ∀ (x : J0 F (blkOf E.shape)) (w : E.leviRep), f (stdType E x w) = π x (f w))
    (hf0 : f ≠ 0) :
    ∃ B : BlockShape (m + 1), B.parabolic F ≠ ⊤ ∧
      ∃ g : GL (Fin (m + 1)) F,
        ¬ Subsingleton (Jacquet.Coinvariants π (B.conjugateUnipotent g)) := by
  classical
  obtain ⟨σ, j, hj0, hjl, hsep⟩ := exists_permute_separated E hE
  let E' := permuteDatum E σ
  have hdisj' : ∀ i i' : Fin E'.shape.length, (i : ℕ) < j → j ≤ (i' : ℕ) →
      E'.blockLabel i ≠ E'.blockLabel i' := fun i i' hi hi' => hsep i i' hi hi'
  have hfin : FiniteDimensional ℂ (fixK1 π) :=
    hπ.2 (Conductor.principalLevelOpenSubgroup F m 1)
  let X : FDRep ℂ (GeneralLinear (m + 1) 𝓀[F]) := FiniteRep.ofRepresentation (descended π)
  let e := FiniteRep.modelEquiv (descended π)
  have he : ∀ (h : GeneralLinear (m + 1) 𝓀[F]) (x : fixK1 π), e (descended π h x) = X.ρ h (e x) :=
    fun h x => LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' h) x
  have he' : ∀ (h : GeneralLinear (m + 1) 𝓀[F]) (y : X), e.symm (X.ρ h y) =
      descended π h (e.symm y) := fun h y =>
    LinearMap.congr_fun (e.symm.toIntertwiningMap.isIntertwining' h) y
  -- the parabolic intertwiner attached to `f`
  obtain ⟨gb, hgbv, hgb⟩ := exists_parabolicIntertwiner π E f hf
  let I : Representation.IntertwiningMap
      (FiniteRep.pullbackRep (E.shape.leviProjection 𝓀[F]) E.leviRep).ρ
      (X.ρ.comp (E.shape.parabolic 𝓀[F]).subtype) :=
    ⟨e.toLinearEquiv.toLinearMap ∘ₗ gb, fun q => LinearMap.ext fun (w : E.leviRep) => by
      change e (gb (parabolicRep E q w)) = X.ρ (q : GeneralLinear (m + 1) 𝓀[F]) (e (gb w))
      have h1 : gb (parabolicRep E q w) = descended π (q : GeneralLinear (m + 1) 𝓀[F]) (gb w) :=
        LinearMap.congr_fun (hgb q) w
      rw [h1, he]⟩
  have hI : I ≠ 0 := by
    intro h
    apply hf0
    apply LinearMap.ext
    intro w
    have hw : e (gb w) = 0 := by
      have : I w = 0 := by rw [h]; rfl
      exact this
    have hw' : gb w = 0 := by
      have := congrArg e.symm hw
      rwa [Representation.Equiv.symm_apply_apply, map_zero] at this
    rw [LinearMap.zero_apply, ← hgbv w, hw']
    rfl
  have hpos := (Module.finrank_pos_iff_exists_ne_zero (R := ℂ)).mpr ⟨I, hI⟩
  rw [finrank_parabolicHom_eq_of_labels_eq E E' (permuteDatum_labels E σ).symm X] at hpos
  obtain ⟨I', hI'⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℂ)).mp hpos
  let gb' : E'.leviRep →ₗ[ℂ] fixK1 π := e.symm.toLinearEquiv.toLinearMap ∘ₗ I'.toLinearMap
  have hgb' : ∀ q : E'.shape.parabolic 𝓀[F],
      gb' ∘ₗ parabolicRep E' q = descended π (q : GeneralLinear (m + 1) 𝓀[F]) ∘ₗ gb' := by
    intro q
    apply LinearMap.ext
    intro w
    have h1 := LinearMap.congr_fun (I'.isIntertwining' q) w
    change e.symm (I' (parabolicRep E' q w)) = descended π (q : GeneralLinear (m + 1) 𝓀[F])
      (e.symm (I' w))
    rw [show I' (parabolicRep E' q w) = X.ρ (q : GeneralLinear (m + 1) 𝓀[F]) (I' w) from h1, he']
  let f' : E'.leviRep →ₗ[ℂ] V := (fixK1 π).subtype ∘ₗ gb'
  have hf' := stdType_intertwiner_of_parabolic π E' gb' hgb'
  have hf'0 : f' ≠ 0 := by
    intro h
    apply hI'
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    have h1 : gb' w = 0 := Subtype.ext (LinearMap.congr_fun h w)
    have h2 : e (gb' w) = I' w := Representation.Equiv.apply_symm_apply e (I' w)
    change I' w = 0
    rw [← h2, h1, map_zero]
  -- the compression criterion along the coarse corner
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (ValuativeRel.valuation F).integer
  have hcoarse := not_subsingleton_coinvariants_coarseN (j := j) π hπ.1
    (J1Open (blkOf E'.shape)) (isCompact_J1Open _) hϖ rfl (stdType E')
    (stdType_eq_one_of_mem_J1 E') (fun g hg hg0 => stdType_test π E' j hdisj' g hg hg0)
    f' hf' hf'0
  -- the corner as a conjugate of a proper two-block radical
  set b := Fintype.card (Late (blkOf E'.shape) j) with hb
  let late0 : Fin (m + 1) := E'.shape.index ⟨j, hjl⟩ ⟨0, E'.shape.positive _⟩
  let early0 : Fin (m + 1) :=
    E'.shape.index ⟨0, show 0 < E.shape.length by omega⟩ ⟨0, E'.shape.positive _⟩
  have hlate0 : j ≤ blkOf E'.shape late0 := by
    simp only [late0, blkOf, blockIndex_index]
    exact le_refl _
  have hearly0 : ¬ j ≤ blkOf E'.shape early0 := by
    simp only [early0, blkOf, blockIndex_index]
    omega
  have hb0 : 0 < b := Fintype.card_pos_iff.mpr ⟨⟨late0, hlate0⟩⟩
  have hbn : b < m + 1 := by
    have := Fintype.card_subtype_lt (p := fun p : Fin (m + 1) => j ≤ blkOf E'.shape p) hearly0
    simpa [hb] using this
  obtain ⟨τ, hτ⟩ := exists_perm_late (blkOf E'.shape) j
  exact ⟨twoBlock (m + 1) b hb0 hbn, cutShape_parabolic_ne_top (m + 1) b hb0 hbn,
    permutation (m + 1) F τ,
    not_subsingleton_coinvariants_of_le π (conjugateUnipotent_le_coarseN hb0 hbn hτ) hcoarse⟩

end Langlands.BushnellKutzko.SplitTypeJacquet
