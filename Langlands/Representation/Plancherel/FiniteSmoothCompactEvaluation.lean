import Langlands.Representation.Plancherel.FiniteSmoothFamilyTransport
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Detecting finite smooth families by compact evaluations -/

noncomputable section

namespace Langlands.Plancherel

universe uJ uI uV uW uH

variable {J : Type uJ} [Fintype J]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A finite tuple of finite scalar-smooth families is a finite scalar-smooth family. -/
theorem mem_finiteSmoothFamilies_pi {ι : Type uI} [Fintype ι]
    (F : (J → Circle) → (ι → V))
    (hF : ∀ i, (fun z => F z i) ∈ finiteSmoothFamilies J V) :
    F ∈ finiteSmoothFamilies J (ι → V) := by
  classical
  have hsum := (finiteSmoothFamilies J (ι → V)).sum_mem
    (fun i (_ : i ∈ Finset.univ) => mem_finiteSmoothFamilies_linearMap
      (hF i) (LinearMap.single ℂ (fun _ : ι => V) i))
  convert hsum using 1
  ext z i
  simp

/-- A linear injection detects finite scalar smoothness, even for an
infinite-dimensional coefficient space. -/
theorem mem_finiteSmoothFamilies_of_injective_linearMap
    (T : W →ₗ[ℂ] V) (hT : Function.Injective T) (F : (J → Circle) → W)
    (hF : (fun z => T (F z)) ∈ finiteSmoothFamilies J V) :
    F ∈ finiteSmoothFamilies J W := by
  have hh := mem_finiteSmoothFamilies_linearMap hF T.leftInverse
  simpa only [LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hT)] using hh

variable {H : Type uH} [Group H]

/-- The actual subspace whose evaluations are right invariant under a fixed
subgroup. No topology on either coefficient space is needed. -/
def rightInvariantEvaluationSubmodule (E : W →ₗ[ℂ] (H → V)) (L : Subgroup H) :
    Submodule ℂ W where
  carrier := {w | ∀ k (l : L), E w (k * (l : H)) = E w k}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw k l
    simp only [map_add, Pi.add_apply, hv k l, hw k l]
  smul_mem' := by
    intro c v hv k l
    simp only [map_smul, Pi.smul_apply, hv k l]

variable [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]

/-- On a compact group, a common open right stabilizer reduces the finite
scalar-smooth condition to finitely many point evaluations. -/
theorem mem_finiteSmoothFamilies_of_common_open_stabilizer
    (E : W →ₗ[ℂ] (H → V)) (hE : Function.Injective E)
    (F : (J → Circle) → W) (L : OpenSubgroup H)
    (hL : ∀ z k (l : L), E (F z) (k * (l : H)) = E (F z) k)
    (hF : ∀ k, (fun z => E (F z) k) ∈ finiteSmoothFamilies J V) :
    F ∈ finiteSmoothFamilies J W := by
  classical
  let S := rightInvariantEvaluationSubmodule E L.toSubgroup
  let _ := Fintype.ofFinite (H ⧸ L.toSubgroup)
  let T : S →ₗ[ℂ] ((H ⧸ L.toSubgroup) → V) :=
    { toFun := fun w q => E w.val q.out
      map_add' := by intros; funext q; exact congrFun (E.map_add _ _) q.out
      map_smul' := by intros; funext q; exact congrFun (E.map_smul _ _) q.out }
  have hT : Function.Injective T := by
    intro v w hvw
    apply Subtype.ext
    apply hE
    funext k
    let q : H ⧸ L.toSubgroup := QuotientGroup.mk k
    have hmem : q.out⁻¹ * k ∈ L :=
      QuotientGroup.leftRel_apply.mp (Quotient.exact q.out_eq)
    have hv := v.property q.out ⟨q.out⁻¹ * k, hmem⟩
    have hw := w.property q.out ⟨q.out⁻¹ * k, hmem⟩
    simpa only [mul_inv_cancel_left] using hv.trans ((congrFun hvw q).trans hw.symm)
  let F' : (J → Circle) → S := fun z => ⟨F z, hL z⟩
  have htuple : (fun z => T (F' z)) ∈
      finiteSmoothFamilies J ((H ⧸ L.toSubgroup) → V) :=
    mem_finiteSmoothFamilies_pi _ (fun q => hF q.out)
  exact mem_finiteSmoothFamilies_linearMap
    (mem_finiteSmoothFamilies_of_injective_linearMap T hT F' htuple) S.subtype

end Langlands.Plancherel
