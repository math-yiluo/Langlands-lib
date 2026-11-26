import Langlands.Correspondence.HenniartUnramified.Irreducible
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Extension of inertia types to a stage and uniqueness up to unramified twist -/

noncomputable section

namespace Langlands.FiniteRepresentation.SplitDegree

open Representation LinearMap

universe uG uH uV uW

section General

variable {K : Type*} [Group K] {L : Type*} [Group L]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Character twists preserve irreducibility. -/
theorem isIrreducible_twist (χ : L →* ℂˣ) (ρ : Representation ℂ L V) (h : ρ.IsIrreducible) :
    (Langlands.twist χ ρ).IsIrreducible := by
  let e : Subrepresentation ρ ≃o Subrepresentation (Langlands.twist χ ρ) :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        change (χ g : ℂ) • ρ g v ∈ S.toSubmodule
        exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have h := S.toSubmodule.smul_mem ((χ g)⁻¹ : ℂˣ) (S.apply_mem_toSubmodule g hv)
        change ((χ g)⁻¹ : ℂˣ) • ((χ g : ℂ) • ρ g v) ∈ S.toSubmodule at h
        rwa [Units.smul_def, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          one_smul] at h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact (OrderIso.isSimpleOrder_iff e).mp h

/-- An equivalence persists after precomposition. -/
def equivComp {W : Type uW} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ L V}
    {σ : Representation ℂ L W} (e : ρ.Equiv σ) (c : K →* L) :
    Representation.Equiv (ρ.comp c) (σ.comp c) :=
  Representation.Equiv.mk e.toLinearEquiv fun k => e.isIntertwining' (c k)

end General

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {H : Type uH} [Group H] [TopologicalSpace H]
variable {D : SplitDegree G} {E : SplitDegree H} {m : ℕ}

namespace Stage

variable (S : Stage D E (m + 1))

theorem κ_mem (n : D.inertia) : S.κ n ∈ E.inertia := by
  have h := S.degree_ι (S.κ n)
  rw [S.ι_κ] at h
  have h0 : D.intDegree (n : G) = 0 := congrArg Multiplicative.toAdd n.property
  rw [h0] at h
  have h1 : E.intDegree (S.κ n) = 0 := by
    rcases mul_eq_zero.mp h.symm with h2 | h2
    · exact absurd h2 (by positivity)
    · exact h2
  change E.degree (S.κ n) = 1
  exact Multiplicative.toAdd.injective h1

theorem ι_mem {h : H} (hh : h ∈ E.inertia) : S.ι h ∈ D.inertia := by
  change D.degree (S.ι h) = 1
  apply Multiplicative.toAdd.injective
  change D.intDegree (S.ι h) = 0
  rw [S.degree_ι]
  have : E.intDegree h = 0 := congrArg Multiplicative.toAdd hh
  rw [this, mul_zero]

/-- `κ` as a map of inertia groups. -/
def κJ : D.inertia →* E.inertia := S.κ.codRestrict _ S.κ_mem

/-- `ι` as a map of inertia groups. -/
def ιJ : E.inertia →* D.inertia :=
  (S.ι.comp E.inertia.subtype).codRestrict _ fun h => S.ι_mem h.2

@[simp] theorem coe_κJ (n : D.inertia) : (S.κJ n : H) = S.κ n := rfl

@[simp] theorem coe_ιJ (h : E.inertia) : (S.ιJ h : G) = S.ι h := rfl

@[simp] theorem ιJ_κJ (n : D.inertia) : S.ιJ (S.κJ n) = n := Subtype.ext (S.ι_κ n)

@[simp] theorem κJ_ιJ (h : E.inertia) : S.κJ (S.ιJ h) = h :=
  Subtype.ext (S.injective (by rw [coe_κJ, S.ι_κ, coe_ιJ]))

theorem ιJ_surjective : Function.Surjective S.ιJ := fun n => ⟨S.κJ n, S.ιJ_κJ n⟩

theorem continuous_ιJ : Continuous S.ιJ :=
  (S.continuous_ι.comp continuous_subtype_val).subtype_mk _

theorem ιJ_conj (h : E.inertia) :
    S.ιJ (MulAut.conjNormal E.lift h) = D.cj (m + 1) (S.ιJ h) := by
  apply Subtype.ext
  rw [coe_ιJ, coe_cj, coe_ιJ, MulAut.conjNormal_apply, map_mul, map_mul, map_inv, S.ι_lift]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- An inertia type fixed by conjugation with `lift ^ (m+1)` extends to the stage, with first
block the type itself. -/
theorem exists_extension (x : Representation ℂ D.inertia V)
    (e : Representation.Equiv (x.comp (D.cj (m + 1))) x) :
    ∃ τ : Representation ℂ H V, S.block τ 0 = x ∧
      τ.comp E.inertia.subtype = x.comp S.ιJ ∧
      ∀ [IsTopologicalGroup H] [FiniteDimensional ℂ V],
        (FiniteRepresentation.of x).IsContinuous → (FiniteRepresentation.of τ).IsContinuous := by
  let π := x.comp S.ιJ
  have hπ : π.comp (MulAut.conjNormal E.lift).toMonoidHom = (x.comp (D.cj (m + 1))).comp S.ιJ := by
    ext h : 1
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, π, S.ιJ_conj]
  let e' : Representation.Equiv π (π.comp (MulAut.conjNormal E.lift).toMonoidHom) := by
    rw [hπ]
    exact equivComp e.symm S.ιJ
  obtain ⟨U, hU⟩ := E.exists_compatibleOperator π e'
  refine ⟨E.extend π U hU, ?_, ?_, ?_⟩
  · ext n : 1
    simp only [block_apply, cj_zero]
    rw [← coe_κJ, E.extend_on_inertia]
    simp [π]
  · ext h : 1
    exact E.extend_on_inertia π U hU h
  · intro _ _ hx
    apply E.continuous_extend
    let _ : TopologicalSpace (Module.End ℂ V) := moduleTopology ℂ (Module.End ℂ V)
    have hx' : Continuous x := hx
    exact hx'.comp S.continuous_ιJ

/-- Unramified character values along the stage map. -/
theorem unramifiedCharacter_ι (u : ℂˣ) (h : H) :
    Weil.Local.unramifiedCharacter D.degree u (S.ι h) =
      Weil.Local.unramifiedCharacter E.degree (u ^ (m + 1)) h := by
  rw [Weil.Local.unramifiedCharacter_apply, Weil.Local.unramifiedCharacter_apply]
  change u ^ D.intDegree (S.ι h) = (u ^ (m + 1)) ^ E.intDegree h
  rw [S.degree_ι, ← zpow_natCast, ← zpow_mul]

end Stage

end Langlands.FiniteRepresentation.SplitDegree
