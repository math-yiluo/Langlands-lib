import Langlands.Correspondence.HenniartUnramified.Clifford

/-! # Reciprocity, twists, kernels and continuity of the explicit coinduction -/

noncomputable section

namespace Langlands.FiniteRepresentation.SplitDegree

open Representation LinearMap

universe uG uH uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {H : Type uH} [Group H] [TopologicalSpace H]
variable {D : SplitDegree G} {E : SplitDegree H} {m : ℕ}

section Recip

variable (D) (m)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The Frobenius reciprocity map, in the coordinates of the explicit coinduction. -/
def recip {V' : Type uW} [AddCommGroup V'] [Module ℂ V'] (ρ' : Representation ℂ G V')
    (P : V' →ₗ[ℂ] V) : V' →ₗ[ℂ] (Fin (m + 1) → V) :=
  LinearMap.pi fun k : Fin (m + 1) => P ∘ₗ ρ' (D.lift ^ (k : ℕ))

@[simp] theorem recip_apply {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (ρ' : Representation ℂ G V') (P : V' →ₗ[ℂ] V) (v : V') (k : Fin (m + 1)) :
    recip D m ρ' P v k = P (ρ' (D.lift ^ (k : ℕ)) v) := rfl

theorem recip_ne_zero {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (ρ' : Representation ℂ G V') (P : V' →ₗ[ℂ] V) (hP : P ≠ 0) : recip D m ρ' P ≠ 0 := by
  intro h
  apply hP
  apply LinearMap.ext
  intro v
  have := congrFun (LinearMap.congr_fun h v) 0
  simpa using this

end Recip

namespace Stage

variable (S : Stage D E (m + 1))
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ H V)

/-- A stage intertwiner gives an intertwiner into the coinduction. -/
theorem recip_intertwines {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (ρ' : Representation ℂ G V') (P : V' →ₗ[ℂ] V)
    (hP : ∀ h : H, P ∘ₗ ρ' (S.ι h) = τ h ∘ₗ P) (g : G) :
    recip D m ρ' P ∘ₗ ρ' g = S.coind τ g ∘ₗ recip D m ρ' P := by
  apply D.intertwines_of_inertia_and_lift ρ' (S.coind τ)
  · intro n
    apply LinearMap.ext
    intro v
    funext k
    simp only [comp_apply, recip_apply, coind_inertia, inertiaRep_apply]
    have h1 : D.lift ^ (k : ℕ) * (n : G) = S.ι (S.κ (D.cj k n)) * D.lift ^ (k : ℕ) := by
      rw [S.ι_κ, coe_cj]
      group
    rw [← Module.End.mul_apply, ← map_mul, h1, map_mul, Module.End.mul_apply]
    exact LinearMap.congr_fun (hP _) _
  · apply LinearMap.ext
    intro v
    funext k
    simp only [comp_apply, recip_apply, coind_lift]
    by_cases hk : k = Fin.last m
    · subst hk
      rw [cycUnit_apply_last, recip_apply]
      simp only [Fin.val_last, Fin.val_zero, pow_zero, map_one, Module.End.one_apply]
      rw [← Module.End.mul_apply, ← map_mul, ← pow_succ, ← S.ι_lift]
      exact LinearMap.congr_fun (hP _) v
    · rw [cycUnit_apply_of_ne _ _ _ _ hk, recip_apply, coe_finRotate_of_ne_last hk,
        ← Module.End.mul_apply, ← map_mul, ← pow_succ]

/-- The diagonal operator with entries `u ^ k`. -/
def diagPow (u : ℂˣ) : (Fin (m + 1) → V) ≃ₗ[ℂ] (Fin (m + 1) → V) :=
  LinearEquiv.piCongrRight fun k : Fin (m + 1) => LinearEquiv.smulOfUnit (u ^ (k : ℕ))

@[simp] theorem diagPow_apply (u : ℂˣ) (v : Fin (m + 1) → V) (k : Fin (m + 1)) :
    diagPow u v k = ((u ^ (k : ℕ) : ℂˣ) : ℂ) • v k := rfl

/-- Unramified twists by `f`th roots of unity fix the coinduction. -/
theorem twist_equiv_of_pow_eq_one (u : ℂˣ) (hu : u ^ (m + 1) = 1) :
    Nonempty ((Langlands.twist (Weil.Local.unramifiedCharacter D.degree u).toMonoidHom
      (S.coind τ)).Equiv (S.coind τ)) := by
  let χ := (Weil.Local.unramifiedCharacter D.degree u).toMonoidHom
  have hχN (n : D.inertia) : χ n = 1 :=
    Weil.Local.unramifiedCharacter_on_kernel _ _ n.property
  have hχT : χ D.lift = u := Weil.Local.unramifiedCharacter_degree_one _ _ D.lift_degree
  refine ⟨Representation.Equiv.mk (diagPow u) ?_⟩
  intro g
  revert g
  apply D.intertwines_of_inertia_and_lift (Langlands.twist χ (S.coind τ)) (S.coind τ)
  · intro n
    apply LinearMap.ext
    intro v
    funext k
    change diagPow u ((χ n : ℂ) • S.coind τ n v) k = S.coind τ n (diagPow u v) k
    rw [hχN, Units.val_one, one_smul, coind_inertia]
    simp only [diagPow_apply, inertiaRep_apply, map_smul]
  · apply LinearMap.ext
    intro v
    funext k
    change diagPow u ((χ D.lift : ℂ) • S.coind τ D.lift v) k = S.coind τ D.lift (diagPow u v) k
    rw [hχT, coind_lift]
    by_cases hk : k = Fin.last m
    · subst hk
      simp only [diagPow_apply, Pi.smul_apply, cycUnit_apply_last, Fin.val_last, Fin.val_zero,
        pow_zero, Units.val_one, one_smul, smul_smul]
      rw [← Units.val_mul, ← pow_succ, hu, Units.val_one, one_smul]
    · simp only [diagPow_apply, Pi.smul_apply, cycUnit_apply_of_ne _ _ _ _ hk,
        coe_finRotate_of_ne_last hk, smul_smul, ← Units.val_mul, ← pow_succ]

/-- The coinduction is trivial on a normal subgroup of inertia exactly when its first block is. -/
theorem coind_trivial_iff (N : Subgroup G) [N.Normal] :
    (∀ n : D.inertia, (n : G) ∈ N → S.coind τ n = 1) ↔
      (∀ n : D.inertia, (n : G) ∈ N → S.block τ 0 n = 1) := by
  constructor
  · intro h n hn
    apply LinearMap.ext
    intro a
    have := congrFun (LinearMap.congr_fun (h n hn) (Pi.single 0 a)) 0
    simpa [coind_inertia, cj_zero] using this
  · intro h n hn
    apply LinearMap.ext
    intro v
    funext k
    rw [coind_inertia, inertiaRep_apply, Module.End.one_apply]
    have hk : ((D.cj k n : D.inertia) : G) ∈ N := by
      rw [coe_cj]
      exact Subgroup.Normal.conj_mem inferInstance _ hn _
    have := LinearMap.congr_fun (h _ hk) (v k)
    simpa [cj_zero] using this

/-- Continuity of the coinduction. -/
theorem continuous_coind [IsTopologicalGroup G] [FiniteDimensional ℂ V]
    (hτ : (FiniteRepresentation.of τ).IsContinuous) :
    (FiniteRepresentation.of (S.coind τ)).IsContinuous := by
  apply D.continuous_extend
  let : TopologicalSpace (Module.End ℂ V) := moduleTopology ℂ (Module.End ℂ V)
  have : IsModuleTopology ℂ (Module.End ℂ V) := ⟨rfl⟩
  let : TopologicalSpace (Module.End ℂ (Fin (m + 1) → V)) :=
    moduleTopology ℂ (Module.End ℂ (Fin (m + 1) → V))
  have : IsModuleTopology ℂ (Module.End ℂ (Fin (m + 1) → V)) := ⟨rfl⟩
  have := IsModuleTopology.toContinuousAdd ℂ (Module.End ℂ (Fin (m + 1) → V))
  let diag : (Fin (m + 1) → Module.End ℂ V) →ₗ[ℂ] Module.End ℂ (Fin (m + 1) → V) :=
    { toFun := fun T => LinearMap.pi fun k => (T k).comp (LinearMap.proj k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hdiag : Continuous diag := IsModuleTopology.continuous_of_linearMap diag
  have hτ' : Continuous τ := hτ
  have hcomp : Continuous fun n : D.inertia => fun k : Fin (m + 1) => τ (S.κ (D.cj k n)) :=
    continuous_pi fun k => hτ'.comp (S.continuous_κ.comp (D.continuous_cj k))
  change Continuous (S.inertiaRep τ)
  exact (hdiag.comp hcomp).congr fun n => rfl

end Stage

end Langlands.FiniteRepresentation.SplitDegree
