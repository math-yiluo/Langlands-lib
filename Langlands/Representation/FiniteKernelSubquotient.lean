import Langlands.Automorphic.ConstantTermFiltration
import Langlands.Correspondence.UnramifiedNormalization
import Mathlib.RepresentationTheory.Irreducible

/-! A simple full-operator quotient descends along one finite-equivariant projection. -/

noncomputable section
set_option autoImplicit false

open scoped MonoidAlgebra

namespace Langlands

open Representation

private theorem exists_submodule_of_finiteKernels
    {R V W : Type*} [Ring R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    [IsSimpleModule R W] {k : ℕ} (K : Fin k → Submodule R V)
    (q : V →ₗ[R] W) (hq : Function.Surjective q)
    (hkill : ∀ x, (∀ i, x ∈ K i) → q x = 0) :
    ∃ (i : Fin k) (A : Submodule R V), Function.Surjective (q.comp A.subtype) ∧
      ∀ x : A, x.val ∈ K i → q x.val = 0 := by
  let K' : Fin (k + 1) → Submodule R V := Fin.cons ⊥ K
  let c (j : Fin (k + 1)) : V →ₗ[R] V ⧸ K' j := (K' j).mkQ
  have hsep (x : V) (hx : ∀ j, c j x = 0) : x = 0 :=
    (Submodule.mem_bot R).mp ((Submodule.Quotient.mk_eq_zero (p := ⊥)).mp (hx 0))
  obtain ⟨j, x, p, hLater, _, hpx, hqx⟩ := Automorphic.exists_cyclic_term_quotient c hsep q hq
  cases j using Fin.cases with
  | zero =>
      apply (hqx (hkill x fun i => ?_)).elim
      have hzero : c i.succ x = 0 :=
        hLater i.succ (Nat.zero_lt_succ i.val) (Submodule.mem_span_singleton_self x)
      exact (Submodule.Quotient.mk_eq_zero (p := K i)).mp hzero
  | succ i =>
      let A := R ∙ x
      let x' : A := ⟨x, Submodule.mem_span_singleton_self x⟩
      have hqA : q.comp A.subtype ≠ 0 := by
        intro h
        exact hqx (congrArg (fun f : A →ₗ[R] W => f x') h)
      refine ⟨i, A, (LinearMap.surjective_or_eq_zero (q.comp A.subtype)).resolve_right hqA, ?_⟩
      intro y hy
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp y.property
      let z : R ∙ c i.succ x := ⟨c i.succ x, Submodule.mem_span_singleton_self _⟩
      have hz : a • z = 0 := by
        apply Subtype.ext
        change a • (K i).mkQ x = 0
        rw [← map_smul, ha]
        exact (Submodule.Quotient.mk_eq_zero (p := K i)).mpr hy
      calc
        q y.val = a • q x := by rw [← ha, map_smul]
        _ = a • p z := congrArg (a • ·) hpx.symm
        _ = p (a • z) := (p.map_smul a z).symm
        _ = 0 := by rw [hz, map_zero]

section RangeDescent

variable {G V Y W : Type*} [Monoid G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G Y} {τ : Representation ℂ G W}
  (f : ρ.IntertwiningMap σ) (q : ρ.IntertwiningMap τ)
  (hker : f.toLinearMap.ker ≤ q.toLinearMap.ker)

private def rangeDescentLinear : f.range.toSubmodule →ₗ[ℂ] W :=
  (f.toLinearMap.ker.liftQ q.toLinearMap hker) ∘ₗ f.toLinearMap.quotKerEquivRange.symm.toLinearMap

private theorem rangeDescentLinear_apply (x : V) :
    rangeDescentLinear f q hker (f.toLinearMap.rangeRestrict x) = q x := by
  change f.toLinearMap.ker.liftQ q.toLinearMap hker
    (f.toLinearMap.quotKerEquivRange.symm (f.toLinearMap.rangeRestrict x)) = q x
  have h : f.toLinearMap.quotKerEquivRange.symm (f.toLinearMap.rangeRestrict x) =
      f.toLinearMap.ker.mkQ x :=
    LinearMap.quotKerEquivRange_symm_apply_image f.toLinearMap x _
  rw [h]
  rfl

/-- Factor a second intertwiner through the actual range of the first when it kills its kernel. -/
def descendIntertwinerToRange : f.range.toRepresentation.IntertwiningMap τ where
  toLinearMap := rangeDescentLinear f q hker
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    obtain ⟨x, rfl⟩ := f.toLinearMap.surjective_rangeRestrict v
    have hf : f.range.toRepresentation g (f.toLinearMap.rangeRestrict x) =
        f.toLinearMap.rangeRestrict (ρ g x) :=
      Subtype.ext (IntertwiningMap.isIntertwining ρ σ f g x).symm
    change rangeDescentLinear f q hker (f.range.toRepresentation g (f.toLinearMap.rangeRestrict x)) =
      τ g (rangeDescentLinear f q hker (f.toLinearMap.rangeRestrict x))
    rw [hf, rangeDescentLinear_apply, rangeDescentLinear_apply]
    exact IntertwiningMap.isIntertwining ρ τ q g x

@[simp] theorem descendIntertwinerToRange_apply (x : V) :
    descendIntertwinerToRange f q hker (f.toLinearMap.rangeRestrict x) = q x :=
  rangeDescentLinear_apply f q hker x

end RangeDescent

/-- A finite collection of projections that intertwine the restricted group action
retains the simple full-operator quotient on one actual projected subrepresentation.
The projector kernels must be stable for the full action. -/
theorem exists_subquotient_of_finiteProjections
    {M G V W ι : Type*} [Monoid M] [Group G] [Fintype ι]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {Y : ι → Type*} [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)]
    {ρ : Representation ℂ M V} {τ : Representation ℂ M W} [τ.IsIrreducible]
    (α : G →* M) (q : ρ.IntertwiningMap τ) (hq : Function.Surjective q)
    (σ : ∀ i, Representation ℂ G (Y i))
    (f : ∀ i, Representation.IntertwiningMap (ρ.comp α) (σ i))
    (K : ι → Subrepresentation ρ) (hK : ∀ i x, x ∈ K i ↔ f i x = 0)
    (hkill : ∀ x, (∀ i, f i x = 0) → q x = 0) :
    ∃ i, Correspondence.IsSubquotientOf (σ i) (τ.comp α) := by
  classical
  let e := Fintype.equivFin ι
  let qM := IntertwiningMap.equivLinearMapAsModule ρ τ q
  let KM (j : Fin (Fintype.card ι)) := (K (e.symm j)).asSubmodule
  have hkillM (x : ρ.asModule) (hx : ∀ j, x ∈ KM j) : qM x = 0 := by
    apply hkill x
    intro i
    have hmem : x ∈ (K i).asSubmodule := by simpa only [KM, Equiv.symm_apply_apply] using hx (e i)
    exact (hK i x).mp ((Subrepresentation.mem_asSubmodule_iff (σ := K i) (v := x)).mp hmem)
  obtain ⟨j, P, hP, hker⟩ := exists_submodule_of_finiteKernels KM qM hq hkillM
  let i := e.symm j
  let A : Subrepresentation ρ := Subrepresentation.ofSubmodule' P
  let A₀ : Subrepresentation (ρ.comp α) :=
    ⟨A.toSubmodule, fun g => A.apply_mem_toSubmodule (α g)⟩
  let q₀ : A₀.toRepresentation.IntertwiningMap (τ.comp α) :=
    ⟨q.toLinearMap.comp A₀.toSubmodule.subtype, fun g =>
      LinearMap.ext fun x => IntertwiningMap.isIntertwining ρ τ q (α g) x.val⟩
  let f₀ : A₀.toRepresentation.IntertwiningMap (σ i) :=
    ⟨(f i).toLinearMap.comp A₀.toSubmodule.subtype, fun g =>
      LinearMap.ext fun x => IntertwiningMap.isIntertwining (ρ.comp α) (σ i) (f i) g x.val⟩
  have h₀ : f₀.toLinearMap.ker ≤ q₀.toLinearMap.ker := by
    intro x hx
    exact hker ⟨x.val, x.prop⟩ ((hK i x.val).mpr hx)
  refine ⟨i, f₀.range, descendIntertwinerToRange f₀ q₀ h₀, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hP y
  let x₀ : A₀.toSubmodule := ⟨x.val, x.prop⟩
  refine ⟨f₀.toLinearMap.rangeRestrict x₀, ?_⟩
  exact (descendIntertwinerToRange_apply f₀ q₀ h₀ x₀).trans hx

end Langlands
