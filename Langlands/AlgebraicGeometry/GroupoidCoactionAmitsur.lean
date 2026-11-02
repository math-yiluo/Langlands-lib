import Langlands.AlgebraicGeometry.GroupoidCoactionInduced
import Langlands.AlgebraicGeometry.GroupoidCoactionCocycleUniversal
import Langlands.AlgebraicGeometry.FaithfullyFlatAmitsurDegreeOne
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Comparing induced groupoid cocycles with the Amitsur complex -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}

variable (e : B ⊗[(invariantRing t)] B ≃ₐ[B] C)
variable (he : ∀ b : B, e ((1 : B) ⊗ₜ[(invariantRing t)] b) = t b)
variable (N : Type v) [AddCommGroup N] [Module (invariantRing t) N]

/-- Flatten a coefficient tensor using an effective relation-ring presentation. -/
def amitsurCocycleEquiv : C ⊗[B] (B ⊗[(invariantRing t)] N) ≃ₗ[(invariantRing t)] B ⊗[(invariantRing t)] (B ⊗[(invariantRing t)] N) :=
  ((AlgebraTensorModule.cancelBaseChange (invariantRing t) B B C N).restrictScalars (invariantRing t)).trans
    (((e.symm.toLinearEquiv.restrictScalars (invariantRing t)).rTensor N).trans
      (TensorProduct.assoc (invariantRing t) B B N))

@[simp] theorem amitsurCocycleEquiv_tmul (c : C) (b : B) (n : N) :
    amitsurCocycleEquiv e N (c ⊗ₜ[B] (b ⊗ₜ[(invariantRing t)] n)) =
      TensorProduct.assoc (invariantRing t) B B N ((b • e.symm c) ⊗ₜ[(invariantRing t)] n) := by
  simp [amitsurCocycleEquiv]

@[simp] theorem amitsur_symm_source (b : B) :
    e.symm (algebraMap B C b) = b ⊗ₜ[(invariantRing t)] (1 : B) := e.symm.commutes b

include he in
@[simp] theorem amitsur_symm_target (b : B) :
    e.symm (t b) = (1 : B) ⊗ₜ[(invariantRing t)] b := by rw [← he b, e.symm_apply_apply]


/-- The first edge of the universal triple, with source in the middle factor. -/
def amitsurFirst : C →+* (B ⊗[invariantRing t] (B ⊗[invariantRing t] B)) :=
  (Algebra.TensorProduct.includeRight : B ⊗[(invariantRing t)] B →ₐ[(invariantRing t)] (B ⊗[invariantRing t] (B ⊗[invariantRing t] B))).toRingHom.comp
    e.symm.toRingHom

/-- The second edge of the universal triple. -/
def amitsurSecond : C →ₐ[B] (B ⊗[invariantRing t] (B ⊗[invariantRing t] B)) :=
  (Algebra.TensorProduct.map (AlgHom.id B B)
    (Algebra.TensorProduct.includeLeft : B →ₐ[(invariantRing t)] B ⊗[(invariantRing t)] B)).comp e.symm.toAlgHom

/-- The composite edge of the universal triple. -/
def amitsurThird : C →ₐ[B] (B ⊗[invariantRing t] (B ⊗[invariantRing t] B)) :=
  (Algebra.TensorProduct.map (AlgHom.id B B)
    (Algebra.TensorProduct.includeRight : B →ₐ[(invariantRing t)] B ⊗[(invariantRing t)] B)).comp e.symm.toAlgHom

include he in
/-- The first two triple edges are composable. -/
theorem amitsur_compat :
    (amitsurFirst e).comp (algebraMap B C) =
      (amitsurSecond e).toRingHom.comp t := by
  ext b
  simp [amitsurFirst, amitsurSecond, amitsur_symm_target e he]

include he in
/-- The last triple edge has the required target. -/
theorem amitsur_target :
    (amitsurThird e).toRingHom.comp t = (amitsurFirst e).comp t := by
  ext b
  simp [amitsurFirst, amitsurThird, amitsur_symm_target e he]

/-- Flatten the module tensor over the triple-coordinate algebra. -/
def amitsurTripleEquiv :
    (B ⊗[invariantRing t] (B ⊗[invariantRing t] B)) ⊗[B] (B ⊗[(invariantRing t)] N) ≃ₗ[(invariantRing t)] B ⊗[(invariantRing t)] (B ⊗[(invariantRing t)] (B ⊗[(invariantRing t)] N)) :=
  ((AlgebraTensorModule.cancelBaseChange (invariantRing t) B B (B ⊗[invariantRing t] (B ⊗[invariantRing t] B)) N).restrictScalars (invariantRing t)).trans
    ((TensorProduct.assoc (invariantRing t) B (B ⊗[(invariantRing t)] B) N).trans
      ((TensorProduct.assoc (invariantRing t) B B N).lTensor B))

include he in
/-- The induced coaction coboundary becomes the Amitsur differential. -/
theorem amitsur_coboundary (m : B ⊗[(invariantRing t)] N) :
    amitsurCocycleEquiv e N ((induced t N).coboundary m) =
      AmitsurDegreeOne.d0 (invariantRing t) B N m := by
  induction m using TensorProduct.inductionOn with
  | tmul b n =>
    simp [coboundary_apply, amitsur_symm_target e he, amitsurCocycleEquiv,
      Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

@[simp] theorem amitsurCocycleEquiv_symm_tmul (a b : B) (n : N) :
    (amitsurCocycleEquiv e N).symm (a ⊗ₜ[invariantRing t] (b ⊗ₜ[invariantRing t] n)) =
      e (a ⊗ₜ[invariantRing t] b) ⊗ₜ[B] ((1 : B) ⊗ₜ[invariantRing t] n) := by
  apply (amitsurCocycleEquiv e N).injective
  simp

@[simp] theorem amitsurTripleEquiv_tmul (a b c d : B) (n : N) :
    amitsurTripleEquiv (t := t) N
      ((a ⊗ₜ[invariantRing t] (b ⊗ₜ[invariantRing t] c)) ⊗ₜ[B]
        (d ⊗ₜ[invariantRing t] n)) =
      (d * a) ⊗ₜ[invariantRing t] (b ⊗ₜ[invariantRing t] (c ⊗ₜ[invariantRing t] n)) := by
  simp [amitsurTripleEquiv, TensorProduct.smul_tmul', smul_eq_mul]

/-- The three edges of a triple turn the groupoid cocycle expression into d1. -/
theorem amitsur_cocycle_comparison (x : C ⊗[B] (B ⊗[invariantRing t] N)) :
    AmitsurDegreeOne.d1 (invariantRing t) B N (amitsurCocycleEquiv e N x) =
      amitsurTripleEquiv (t := t) N
        (coactionCompose t (B ⊗[invariantRing t] N)
            (induced t N).coaction (induced t N).map_smul
            (amitsurFirst e) (amitsurSecond e) (amitsur_compat e he) x -
          LinearMap.rTensor _ (amitsurThird e).toLinearMap x +
          LinearMap.rTensor _ (amitsurSecond e).toLinearMap x) := by
  obtain ⟨y, rfl⟩ := (amitsurCocycleEquiv e N).symm.surjective x
  induction y using TensorProduct.inductionOn with
  | tmul a z =>
    induction z using TensorProduct.inductionOn with
    | tmul b n =>
      simp [amitsurFirst, amitsurSecond, amitsurThird,
        Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul]
    | add z z' hz hz' =>
      simp only [TensorProduct.tmul_add, map_add, map_sub] at *
      rw [hz, hz']
      abel
  | add y y' hy hy' =>
    simp only [map_add, map_sub] at *
    rw [hy, hy']
    abel

include he in
/-- Induced coactions for a faithfully flat effective relation have no one-cocycles
modulo coboundaries. -/
theorem induced_oneCohomologyVanishes_of_faithfullyFlat
    (hE : RingEtaleEquivalenceRelation t)
    [Module.FaithfullyFlat (invariantRing t) B] :
    (induced t N).OneCohomologyVanishes := by
  intro x hx
  have hc := hx.specialize hE (amitsurFirst e) (amitsurSecond e) (amitsurThird e)
    (amitsur_compat e he) (amitsur_target e he)
  have hz : AmitsurDegreeOne.d1 (invariantRing t) B N
      (amitsurCocycleEquiv e N x) = 0 := by
    rw [amitsur_cocycle_comparison e he N, hc]
    simp
  obtain ⟨m, hm⟩ := AmitsurDegreeOne.exists_primitive (invariantRing t) B N
    (amitsurCocycleEquiv e N x) hz
  refine ⟨m, (amitsurCocycleEquiv e N).injective ?_⟩
  rw [amitsur_coboundary e he N, hm]

include he in
/-- The published invariant-lifting predicate holds for these induced coactions. -/
theorem induced_isAcyclic_of_faithfullyFlat
    (hE : RingEtaleEquivalenceRelation t)
    [Module.FaithfullyFlat (invariantRing t) B] :
    (induced t N).IsAcyclic := by
  let : Module.Flat B C := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  exact isAcyclic_of_oneCohomologyVanishes (induced t N)
    (induced_oneCohomologyVanishes_of_faithfullyFlat e he N hE)

end Langlands.AlgebraicGeometry.GroupoidCoaction
