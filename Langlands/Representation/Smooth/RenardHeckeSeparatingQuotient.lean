import Langlands.Representation.Smooth.RenardHeckeSeparationAux
import Langlands.Algebra.NonnilpotentLeftResolventProof
import Langlands.Algebra.LeftShiftSimpleQuotientProof
import Langlands.Algebra.NonUnitalLeftShiftSimpleQuotientProof
import Mathlib.Tactic.NoncommRing

/-! # Separating full-Hecke quotients from countable compact-open corners -/

noncomputable section

universe u

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Renard.Smooth

open Hecke

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- The actual corner inclusion into the full Hecke algebra's unitization. -/
def cornerUnitizationInclusion :
    HeckeAlgebra.Corner μ K hK →ₙₐ[ℂ] Unitization ℂ (HeckeAlgebra μ) :=
  (Unitization.inrNonUnitalAlgHom ℂ (HeckeAlgebra μ)).comp
    (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK)

/-- Compression of a unitized element back into the actual compact-open corner. -/
def cornerUnitizationCompression (b : Unitization ℂ (HeckeAlgebra μ)) :
    HeckeAlgebra.Corner μ K hK :=
  b.fst • 1 + HeckeAlgebra.Corner.project μ K hK b.snd

/-- Compression is the actual sandwich by the corner's identity in the unitization. -/
theorem cornerUnitizationCompression_eq (b : Unitization ℂ (HeckeAlgebra μ)) :
    cornerUnitizationInclusion μ K hK (cornerUnitizationCompression μ K hK b) =
      cornerUnitizationInclusion μ K hK 1 * b * cornerUnitizationInclusion μ K hK 1 := by
  apply Unitization.ext
  · simp [cornerUnitizationInclusion, cornerUnitizationCompression]
  · change b.fst • HeckeAlgebra.normalizedIndicator μ K hK +
      HeckeAlgebra.normalizedIndicator μ K hK * b.snd *
        HeckeAlgebra.normalizedIndicator μ K hK =
        (((Unitization.inr (HeckeAlgebra.normalizedIndicator μ K hK) :
          Unitization ℂ (HeckeAlgebra μ)) * b *
          Unitization.inr (HeckeAlgebra.normalizedIndicator μ K hK)).snd)
    simp only [
      Unitization.snd_mul, Unitization.fst_mul, Unitization.fst_inr,
      Unitization.snd_inr, zero_mul, zero_smul, zero_add, add_zero,
      add_mul, smul_mul_assoc, HeckeAlgebra.normalizedIndicator_idempotent]

/-- A corner element without a left inverse stays without one after adding `1-e`. -/
theorem corner_no_leftInverse_unitization
    (c : HeckeAlgebra.Corner μ K hK) (hc : ∀ d, d * c ≠ 1) :
    ∀ b : Unitization ℂ (HeckeAlgebra μ),
      b * (cornerUnitizationInclusion μ K hK c +
        (1 - cornerUnitizationInclusion μ K hK 1)) ≠ 1 := by
  let j := cornerUnitizationInclusion μ K hK
  have hj : Function.Injective j := Unitization.inr_injective.comp
    (HeckeAlgebra.Corner.toHeckeAlgebra_injective μ K hK)
  have he : j 1 * j 1 = j 1 := by rw [← map_mul, one_mul]
  have hl : j 1 * j c = j c := by rw [← map_mul, one_mul]
  have hr : j c * j 1 = j c := by rw [← map_mul, mul_one]
  have hx : (j c + (1 - j 1)) * j 1 = j c := by
    rw [add_mul, sub_mul, one_mul, he, sub_self, add_zero, hr]
  intro b hb
  apply hc (cornerUnitizationCompression μ K hK b)
  apply hj
  rw [map_mul, cornerUnitizationCompression_eq]
  change j 1 * b * j 1 * j c = j 1
  calc
    _ = j 1 * b * j c := by rw [mul_assoc (j 1 * b), hl]
    _ = j 1 * (b * (j c + (1 - j 1))) * j 1 := by
      simp only [mul_assoc, hx]
    _ = j 1 := by rw [hb, mul_one, he]

/-- A nonnilpotent corner element acts nontrivially in a simple full-unitization quotient.
The class of `1` is fixed by the corner's identity and is its nonzero eigenvector. -/
theorem exists_separating_unitization_quotient [SigmaCompactSpace G]
    (f : HeckeAlgebra.Corner μ K hK) (hf : ¬ IsNilpotent f) :
    ∃ (I : Submodule (Unitization ℂ (HeckeAlgebra μ)) (Unitization ℂ (HeckeAlgebra μ)))
      (z : ℂ), z ≠ 0 ∧ IsSimpleModule (Unitization ℂ (HeckeAlgebra μ))
        (Unitization ℂ (HeckeAlgebra μ) ⧸ I) ∧
      I.mkQ 1 ≠ 0 ∧ cornerUnitizationInclusion μ K hK 1 • I.mkQ 1 = I.mkQ 1 ∧
      cornerUnitizationInclusion μ K hK f • I.mkQ 1 = z • I.mkQ 1 := by
  let C := HeckeAlgebra.Corner μ K hK
  let U := Unitization ℂ (HeckeAlgebra μ)
  let j := cornerUnitizationInclusion μ K hK
  obtain ⟨z, hz, hleft⟩ := nonnilpotentLeftResolvent C
    (heckeCorner_rank_le_aleph0 μ K hK) f hf
  let c : C := f - algebraMap ℂ C z
  let x : U := j c + (1 - j 1)
  have hnoleft : ∀ b : U, b * x ≠ 1 :=
    corner_no_leftInverse_unitization μ K hK c hleft
  obtain ⟨I, _, hI, hsimple, hsep⟩ := leftShiftSimpleQuotient U (x + 1) 1 one_ne_zero
    (by simpa using hnoleft)
  have hxI : x ∈ I := hI (by
    apply Submodule.subset_span
    simp only [map_one, add_sub_cancel_right, Set.mem_singleton_iff])
  have hv : I.mkQ 1 ≠ 0 := by
    intro hzero
    apply hsep
    rw [hzero, smul_zero]
  have hxv : x • I.mkQ 1 = 0 := by
    rw [← LinearMap.map_smul, smul_eq_mul, mul_one]
    exact (Submodule.Quotient.mk_eq_zero _).2 hxI
  have he : j 1 * j 1 = j 1 := by rw [← map_mul, one_mul]
  have hxc : (1 - j 1) * x = 1 - j 1 := by
    have hl : j 1 * j c = j c := by rw [← map_mul, one_mul]
    dsimp only [x]
    noncomm_ring [he, hl]
  have hev : j 1 • I.mkQ 1 = I.mkQ 1 := by
    have hh : (1 - j 1) • I.mkQ 1 = 0 := by
      rw [← hxc, mul_smul, hxv, smul_zero]
    exact (sub_eq_zero.mp (by simpa only [sub_smul, one_smul] using hh)).symm
  refine ⟨I, z, hz, hsimple, hv, hev, ?_⟩
  have hcmap : j c = j f - z • j 1 := by
    simp only [c, map_sub, Algebra.algebraMap_eq_smul_one, map_smul]
  change (j f) • I.mkQ 1 = z • I.mkQ 1
  have hs : x • I.mkQ 1 = (j f) • I.mkQ 1 - z • I.mkQ 1 := by
    dsimp only [x]
    rw [add_smul, sub_smul, one_smul, hev, sub_self, add_zero, hcmap, sub_smul,
      smul_assoc, hev]
  exact sub_eq_zero.mp (hs.symm.trans hxv)

/-- The canonical full-Hecke action on the actual unitization quotient. -/
def separatingQuotientAction
    (I : Submodule (Unitization ℂ (HeckeAlgebra μ)) (Unitization ℂ (HeckeAlgebra μ))) :
    HeckeAlgebra μ →ₙₐ[ℂ] Module.End ℂ (Unitization ℂ (HeckeAlgebra μ) ⧸ I) :=
  Unitization.lift.symm
    (_root_.Algebra.lsmul ℂ ℂ (Unitization ℂ (HeckeAlgebra μ) ⧸ I))

/-- A nonnilpotent corner element is separated by an original additively simple,
nondegenerate full-Hecke module on the same actual quotient carrier. -/
theorem exists_separating_nondegenerate_quotient
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SigmaCompactSpace G]
    (f : HeckeAlgebra.Corner μ K hK) (hf : ¬ IsNilpotent f) :
    ∃ I : Submodule (Unitization ℂ (HeckeAlgebra μ)) (Unitization ℂ (HeckeAlgebra μ)),
      let ρ := separatingQuotientAction μ I
      letI := Langlands.Algebra.NonUnitalModule.ofLinearEndHom ρ
      Langlands.Algebra.IsNondegenerate (HeckeAlgebra μ) (Unitization ℂ (HeckeAlgebra μ) ⧸ I) ∧
      (Nontrivial (Unitization ℂ (HeckeAlgebra μ) ⧸ I) ∧
        ∀ S : Langlands.Algebra.NonUnitalSubmodule (HeckeAlgebra μ)
          (Unitization ℂ (HeckeAlgebra μ) ⧸ I), S.toAddSubgroup = ⊥ ∨ S.toAddSubgroup = ⊤) ∧
      ρ f.val ≠ 0 := by
  obtain ⟨I, z, hz, hs, hv, _, hfv⟩ := exists_separating_unitization_quotient μ K hK f hf
  let ρ := separatingQuotientAction μ I
  have hs' : letI := Langlands.Algebra.CompatibleUnitization.module ρ
      IsSimpleModule (Unitization ℂ (HeckeAlgebra μ))
        (Unitization ℂ (HeckeAlgebra μ) ⧸ I) := by
    have hmod : Langlands.Algebra.CompatibleUnitization.module ρ =
        (inferInstance : Module (Unitization ℂ (HeckeAlgebra μ))
          (Unitization ℂ (HeckeAlgebra μ) ⧸ I)) :=
      unitizationQuotient_module_eq (HeckeAlgebra μ) I
    rw [hmod]
    exact hs
  have hρf : ρ f.val (I.mkQ 1) ≠ 0 := by
    change cornerUnitizationInclusion μ K hK f • I.mkQ 1 ≠ 0
    rw [hfv]
    exact smul_ne_zero hz hv
  have hρ : ρ ≠ 0 := by
    intro hh
    apply hρf
    rw [hh, NonUnitalAlgHom.zero_apply, LinearMap.zero_apply]
  let := Langlands.Algebra.NonUnitalModule.ofLinearEndHom ρ
  have hadd := Langlands.Algebra.CompatibleUnitization.simpleUnitizationRestriction ρ hρ hs'
  refine ⟨I, ?_, hadd, ?_⟩
  · intro m
    obtain ⟨a, rfl⟩ :=
      Langlands.Algebra.CompatibleUnitization.simpleUnitizationOrbit ρ hρ hs' (I.mkQ 1) hv m
    obtain ⟨J, _, hJ, hJa⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G
      {HeckeAlgebra.toTestFunction μ a} (⊤ : OpenSubgroup G)
    let e := HeckeAlgebra.normalizedIndicator μ J hJ
    refine ⟨⟨e, HeckeAlgebra.normalizedIndicator_idempotent μ J hJ⟩, ?_⟩
    change ρ e (ρ a (I.mkQ 1)) = ρ a (I.mkQ 1)
    have hea : e * a = a :=
      HeckeAlgebra.normalizedIndicator_mul_of_leftInvariant μ J hJ a
        (hJa (HeckeAlgebra.toTestFunction μ a) (Finset.mem_singleton_self _)).1
    rw [← Module.End.mul_apply, ← map_mul, hea]
  · intro hh
    exact hρf (congrArg (fun F : Module.End ℂ (Unitization ℂ (HeckeAlgebra μ) ⧸ I) =>
      F (I.mkQ 1)) hh)

end Langlands.Renard.Smooth
