import Langlands.LinearAlgebra.RootDatumWeylChambers
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-! # Based correction fixing a coweight face -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Function IsAddIndecomposable

namespace Langlands.LinearAlgebra.RootDatumBasedCorrection

open RootDatumWeylChambers

variable {J M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (P : RootDatum J M N)

/-- Reflections at roots vanishing on a coweight fix that coweight. -/
theorem fixes_coweight (ν : N)
    (w : reflectionSubgroup P {i | P.root' i ν = 0}) :
    w.val.coweightEquiv ν = ν := by
  obtain ⟨w, hw⟩ := w
  induction hw using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    change P.root' i ν = 0 at hi
    change P.coreflection i ν = ν
    simp [P.coreflection_apply, hi]
  | one => rfl
  | mul a b ha hb ia ib =>
    change b.coweightEquiv (a.coweightEquiv ν) = ν
    rw [ia, ib]
  | inv a ha ia =>
    change a.coweightEquiv.symm ν = ν
    apply a.coweightEquiv.injective
    simpa only [LinearEquiv.apply_symm_apply] using ia.symm

/-- Fixing a coweight preserves every root's evaluation on it. -/
theorem root_evaluation_eq (δ : P.Aut) (ν : N)
    (hδ : δ.coweightEquiv ν = ν) (i : J) :
    P.root' (δ.indexEquiv i) ν = P.root' i ν := by
  have h := δ.root'_coweightEquiv i (δ.coweightEquiv ν)
  simp only [LinearEquiv.symm_apply_apply] at h
  rwa [hδ] at h

private theorem regular_symm (δ : P.Aut) {f : N}
    (hf : ∀ i, P.root' i f ≠ 0) :
    ∀ i, P.root' i (δ.coweightEquiv.symm f) ≠ 0 := by
  intro i
  obtain ⟨j, rfl⟩ := δ.indexEquiv.surjective i
  simpa only [δ.root'_coweightEquiv] using hf j

variable [Fintype J]

/-- A correction in the zero-root reflection subgroup preserves all positive
roots of a regular coweight refining the fixed coweight's signs. -/
theorem exists_positive_correction (ν f : N)
    [Finite (reflectionSubgroup P {i | P.root' i ν = 0})]
    (hf : ∀ i, P.root' i f ≠ 0)
    (hface : ∀ i, P.root' i ν ≠ 0 →
      (0 < P.root' i f ↔ 0 < P.root' i ν))
    (δ : P.Aut) (hδ : δ.coweightEquiv ν = ν) :
    ∃ w : reflectionSubgroup P {i | P.root' i ν = 0},
      (∀ i, 0 < P.root' i f ↔ 0 < P.root' ((w.val * δ).indexEquiv i) f) ∧
      (∀ i, P.root' ((w.val * δ).indexEquiv i) ν = P.root' i ν) := by
  obtain ⟨w, hw⟩ := exists_same_signs P {i | P.root' i ν = 0}
    (regular_symm P δ hf) hf
  have hθ : (w.val * δ).coweightEquiv ν = ν := by
    change δ.coweightEquiv (w.val.coweightEquiv ν) = ν
    rw [fixes_coweight P ν w, hδ]
  have heval := root_evaluation_eq P (w.val * δ) ν hθ
  refine ⟨w, fun i => ?_, heval⟩
  by_cases hi : P.root' i ν = 0
  · have hδi : δ.indexEquiv i ∈ {i | P.root' i ν = 0} := by
      change P.root' (δ.indexEquiv i) ν = 0
      rw [root_evaluation_eq P δ ν hδ, hi]
    have h := hw (δ.indexEquiv i) hδi
    rw [δ.root'_coweightEquiv] at h
    have he : P.root' ((w.val * δ).indexEquiv i) f =
        P.root' (δ.indexEquiv i) (w.val.coweightEquiv f) := by
      change P.root' (w.val.indexEquiv (δ.indexEquiv i)) f = _
      have h := w.val.root'_coweightEquiv (δ.indexEquiv i) (w.val.coweightEquiv f)
      simpa only [LinearEquiv.symm_apply_apply] using h
    rwa [he]
  · have hi' : P.root' ((w.val * δ).indexEquiv i) ν ≠ 0 := by
      rwa [heval i]
    exact (hface i hi).trans ((by rw [heval i] : 0 < P.root' i ν ↔
      0 < P.root' ((w.val * δ).indexEquiv i) ν).trans (hface _ hi').symm)

omit [Fintype J] in
private theorem maps_baseOf (f : M →+ ℤ) (δ : P.Aut)
    (hpos : ∀ i, 0 < f (P.root i) ↔ 0 < f (P.root (δ.indexEquiv i))) :
    ∀ i ∈ baseOf P.root f, δ.indexEquiv i ∈ baseOf P.root f := by
  intro i hi
  refine ⟨(hpos i).mp hi.1, ?_⟩
  intro j hj k hk hdec
  change 0 < f (P.root j) at hj
  change 0 < f (P.root k) at hk
  have hroot (l : J) :
      δ.weightEquiv.symm (P.root l) = P.root (δ.indexEquiv.symm l) := by
    apply δ.weightEquiv.injective
    simp [RootPairing.Hom.root_weightMap_apply]
  have hd := congrArg δ.weightEquiv.symm hdec
  simp only [map_add, hroot, Equiv.symm_apply_apply] at hd
  have hj' : 0 < f (P.root (δ.indexEquiv.symm j)) := by
    apply (hpos _).mpr
    simpa only [Equiv.apply_symm_apply] using hj
  have hk' : 0 < f (P.root (δ.indexEquiv.symm k)) := by
    apply (hpos _).mpr
    simpa only [Equiv.apply_symm_apply] using hk
  rcases hi.2 _ hj' _ hk' hd with hj0 | hk0
  · exact False.elim (P.ne_zero _ hj0)
  · exact False.elim (P.ne_zero _ hk0)

omit [Fintype J] in
/-- A root-datum automorphism preserving positive roots permutes the
indecomposable positive indices. -/
theorem mem_baseOf_iff (f : M →+ ℤ) (δ : P.Aut)
    (hpos : ∀ i, 0 < f (P.root i) ↔ 0 < f (P.root (δ.indexEquiv i))) (i : J) :
    i ∈ baseOf P.root f ↔ δ.indexEquiv i ∈ baseOf P.root f := by
  constructor
  · exact maps_baseOf P f δ hpos i
  · intro hi
    have hpos' (j : J) :
        0 < f (P.root j) ↔ 0 < f (P.root (δ.symm.indexEquiv j)) := by
      simpa only [RootPairing.Equiv.inv_indexEquiv, Equiv.apply_symm_apply] using
        (hpos (δ.indexEquiv.symm j)).symm
    simpa using maps_baseOf P f δ.symm hpos' (δ.indexEquiv i) hi

/-- Correct an automorphism inside the zero-root reflection subgroup so that
it permutes a prescribed compatible base and its zero-root subset. The same
correction fixes the whole zero-coroot annihilator pointwise. -/
theorem exists_based_correction (ν f : N)
    [Finite (reflectionSubgroup P {i | P.root' i ν = 0})]
    (hf : ∀ i, P.root' i f ≠ 0)
    (hface : ∀ i, P.root' i ν ≠ 0 →
      (0 < P.root' i f ↔ 0 < P.root' i ν))
    (B : P.Base)
    (hB : (B.support : Set J) = baseOf P.root
      ((P.flip.toLinearMap f) : M →+ ℤ))
    (δ : P.Aut) (hδ : δ.coweightEquiv ν = ν) :
    ∃ (w : reflectionSubgroup P {i | P.root' i ν = 0})
      (e : Equiv.Perm B.support),
      (∀ i : B.support, (e i : J) = (w.val * δ).indexEquiv i) ∧
      (∀ i : B.support, P.root' i ν = 0 ↔ P.root' (e i) ν = 0) ∧
      (∀ x : M, (∀ i, P.root' i ν = 0 → P.toLinearMap x (P.coroot i) = 0) →
        w.val.weightEquiv x = x) ∧
      (∀ x y, P.toLinearMap (w.val.weightEquiv (δ.weightEquiv x))
        (w.val.coweightEquiv.symm (δ.coweightEquiv.symm y)) = P.toLinearMap x y) ∧
      (∀ i : B.support,
        w.val.coweightEquiv.symm (δ.coweightEquiv.symm (P.coroot i)) =
          P.coroot (e i)) := by
  obtain ⟨w, hpos, heval⟩ := exists_positive_correction P ν f hf hface δ hδ
  let θ := w.val * δ
  have hsupport (i : J) : i ∈ B.support ↔ θ.indexEquiv i ∈ B.support := by
    have h := mem_baseOf_iff P ((P.flip.toLinearMap f) : M →+ ℤ) θ hpos i
    simpa only [← hB, Finset.mem_coe] using h
  let e : Equiv.Perm B.support := θ.indexEquiv.subtypeEquiv hsupport
  refine ⟨w, e, fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro i
    change P.root' i ν = 0 ↔ P.root' (θ.indexEquiv i) ν = 0
    rw [heval]
  · intro x hx
    exact fixes_annihilator P _ w x (fun i hi => hx i hi)
  · intro x y
    calc
      _ = P.toLinearMap (δ.weightEquiv x) (δ.coweightEquiv.symm y) := by
        rw [w.val.toLinearMap_weightEquiv, LinearEquiv.apply_symm_apply]
      _ = P.toLinearMap x y := by
        rw [δ.toLinearMap_weightEquiv, LinearEquiv.apply_symm_apply]
  · intro i
    apply w.val.coweightEquiv.injective
    simp only [LinearEquiv.apply_symm_apply]
    apply δ.coweightEquiv.injective
    simp only [LinearEquiv.apply_symm_apply]
    change P.coroot i = θ.coweightEquiv (P.coroot (θ.indexEquiv i))
    simp [RootPairing.Hom.coroot_coweightMap_apply]

/-- A based correction with its simultaneous lattice identities. -/
structure Correction (ν : N) (B : P.Base) (δ : P.Aut) where
  weyl : reflectionSubgroup P {i | P.root' i ν = 0}
  perm : Equiv.Perm B.support
  index_eq : ∀ i : B.support, (perm i : J) = (weyl.val * δ).indexEquiv i
  zero_iff : ∀ i : B.support, P.root' i ν = 0 ↔ P.root' (perm i) ν = 0
  fixed : ∀ x : M, (∀ i, P.root' i ν = 0 → P.toLinearMap x (P.coroot i) = 0) →
    weyl.val.weightEquiv x = x
  pairing : ∀ x y, P.toLinearMap (weyl.val.weightEquiv (δ.weightEquiv x))
    (weyl.val.coweightEquiv.symm (δ.coweightEquiv.symm y)) = P.toLinearMap x y
  coroot : ∀ i : B.support,
    weyl.val.coweightEquiv.symm (δ.coweightEquiv.symm (P.coroot i)) = P.coroot (perm i)

/-- Choose a correction for a base coming from a regular refinement of the
fixed coweight. -/
noncomputable def correction (ν f : N)
    [Finite (reflectionSubgroup P {i | P.root' i ν = 0})]
    (hf : ∀ i, P.root' i f ≠ 0)
    (hface : ∀ i, P.root' i ν ≠ 0 →
      (0 < P.root' i f ↔ 0 < P.root' i ν))
    (B : P.Base)
    (hB : (B.support : Set J) = baseOf P.root
      ((P.flip.toLinearMap f) : M →+ ℤ))
    (δ : P.Aut) (hδ : δ.coweightEquiv ν = ν) : Correction P ν B δ :=
  Classical.choice <| by
    obtain ⟨w, e, hi, hz, hx, hp, hc⟩ := exists_based_correction P ν f hf hface B hB δ hδ
    exact ⟨⟨w, e, hi, hz, hx, hp, hc⟩⟩

end Langlands.LinearAlgebra.RootDatumBasedCorrection
