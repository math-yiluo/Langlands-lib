import Langlands.Automorphic.UnitaryContragredientCriterion
import Langlands.Representation.Compact.LocallyFiniteIsotypicProjection
import Langlands.Representation.Compact.ProjectionProof
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Projecting to a fixed finite level and infinite compact type -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.KFiniteDual.IsotypicProjection

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type*} [Group K] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {d : ℕ} (τ : Representation ℂ K (Fin d → ℂ)) [τ.IsIrreducible]
  (ρ : Representation ℂ G V) (κ : Representation ℂ K V)
  [IsSemisimpleModule (MonoidAlgebra ℂ K) κ.asModule]
  (hρ : Langlands.IsSmooth ρ) (L : OpenSubgroup G) (hL : IsCompact (L : Set G))

/-- First take the infinite compact type, then take the finite compact-open average. -/
def jointCompactProjection : Module.End ℂ V :=
  (Compact.averageMap ρ hρ L hL).comp (intertwiner τ κ).toLinearMap

theorem jointCompactProjection_fixed {v : V}
    (hfin : v ∈ fixedVectors ρ L.toSubgroup) (hinf : v ∈ CompactSplitting.isotypicPart τ κ) :
    jointCompactProjection τ ρ κ hρ L hL v = v := by
  have hfix : intertwiner τ κ v = v := by
    rw [← intertwiner_range] at hinf
    obtain ⟨w, rfl⟩ := hinf
    exact LinearMap.congr_fun (intertwiner_idempotent τ κ).eq w
  change Compact.averageMap ρ hρ L hL (intertwiner τ κ v) = v
  rw [hfix]
  exact Compact.averageMap_id ρ hρ L hL v hfin

/-- With commuting finite and infinite compact actions, joint admissibility
makes the range of the joint projection finite-dimensional. -/
theorem finiteDimensional_range_jointCompactProjection
    (hcomm : ∀ g k v, ρ g (κ k v) = κ k (ρ g v)) (hadm : Langlands.IsJointlyAdmissible ρ κ) :
    FiniteDimensional ℂ (jointCompactProjection τ ρ κ hρ L hL).range := by
  let H := Langlands.jointMultiplicitySpace ρ κ L.toSubgroup τ
  let B := LinearMap.range (KFiniteDual.evalSum H)
  let avg := Compact.averageMap ρ hρ L hL
  let _ : FiniteDimensional ℂ H := hadm L d τ
  let _ : FiniteDimensional ℂ B := LinearMap.finiteDimensional_range _
  have havg (k : K) (v : V) : κ k (avg v) = avg (κ k v) := by
    let f : ρ.IntertwiningMap ρ :=
      ⟨κ k, fun g => LinearMap.ext fun v => (hcomm g k v).symm⟩
    exact LinearMap.congr_fun (Compact.averageMap_commute ρ ρ hρ hρ L hL f) v
  have hB : CompactSplitting.isotypicPart τ κ ≤ B.comap avg := by
    refine iSup_le fun f => ?_
    rintro _ ⟨u, rfl⟩
    have hf : avg.comp f.toLinearMap ∈ H := by
      refine ⟨fun w => Compact.averageMap_mem_fixedVectors ρ hρ L hL (f w), fun k w => ?_⟩
      change avg (f (τ k w)) = κ k (avg (f w))
      rw [Representation.IntertwiningMap.isIntertwining]
      exact (havg k (f w)).symm
    exact KFiniteDual.apply_mem_range_evalSum H hf u
  apply Submodule.finiteDimensional_of_le (S₂ := B)
  rintro _ ⟨v, rfl⟩
  change avg (intertwiner τ κ v) ∈ B
  apply hB
  rw [← intertwiner_range]
  exact ⟨v, rfl⟩

variable {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ G W) (ν : Representation ℂ K W)
  [IsSemisimpleModule (MonoidAlgebra ℂ K) ν.asModule]
  (hσ : Langlands.IsSmooth σ)

/-- A map intertwining both compact actions commutes with the joint projection. -/
theorem jointCompactProjection_natural (f : V →ₗ[ℂ] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (hk : ∀ k v, f (κ k v) = ν k (f v)) (v : V) :
    f (jointCompactProjection τ ρ κ hρ L hL v) = jointCompactProjection τ σ ν hσ L hL (f v) := by
  let finiteIntertwiner : ρ.IntertwiningMap σ := ⟨f, fun g => LinearMap.ext (hf g)⟩
  let compactIntertwiner : κ.IntertwiningMap ν := ⟨f, fun k => LinearMap.ext (hk k)⟩
  have hfin := LinearMap.congr_fun (Compact.averageMap_commute ρ σ hρ hσ L hL finiteIntertwiner)
    (intertwiner τ κ v)
  have hinf := intertwiner_natural τ compactIntertwiner v
  change f (Compact.averageMap ρ hρ L hL (intertwiner τ κ v)) =
    Compact.averageMap σ hσ L hL (intertwiner τ ν (f v))
  exact hfin.trans (congrArg (Compact.averageMap σ hσ L hL) hinf)

private def tupleAction {H I : Type*} [Monoid H] (a : Representation ℂ H V) :
    Representation ℂ H (I → V) where
  toFun g := LinearMap.pi fun i => (a g).comp (LinearMap.proj i)
  map_one' := LinearMap.ext fun v => funext fun i => by
    change a 1 (v i) = v i
    rw [map_one, Module.End.one_apply]
  map_mul' g h := LinearMap.ext fun v => funext fun i => by
    change a (g * h) (v i) = a g (a h (v i))
    rw [map_mul, Module.End.mul_apply]

private theorem exists_averageCombination {I : Type*} [Finite I] (v : I → V) :
    ∃ c : L →₀ ℂ, ∀ i, c.sum (fun g a => a • ρ g.val (v i)) =
      Compact.averageMap ρ hρ L hL (v i) := by
  classical
  let a := ρ.comp L.toSubgroup.subtype
  let b : Representation ℂ L (I → V) := tupleAction a
  let _ (i : I) : Finite (Compact.orbit a (v i)) := Compact.finite_orbit_of_smooth ρ hρ L hL (v i)
  let coords (x : Compact.orbit b v) (i : I) : Compact.orbit a (v i) :=
    ⟨x.val i, by
      obtain ⟨g, hg⟩ := x.property
      exact ⟨g, congrFun hg i⟩⟩
  let _ : Finite (Compact.orbit b v) :=
    Finite.of_injective coords fun x y he =>
      Subtype.ext (funext fun i => congrArg Subtype.val (congrFun he i))
  let _ := Fintype.ofFinite (Compact.orbit b v)
  have hm : Compact.orbitMean b v ∈ Submodule.span ℂ (Set.range fun g : L => b g v) := by
    rw [Compact.orbitMean_eq_finiteMean, Compact.finiteMean]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun x _ => ?_)
    exact Submodule.subset_span x.property
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hm
  refine ⟨c, fun i => ?_⟩
  let p : (I → V) →ₗ[ℂ] V := LinearMap.proj i
  let _ : Finite (Compact.orbit a (p v)) :=
    Compact.finite_orbit_of_smooth ρ hρ L hL (v i)
  have h := Compact.orbitMean_map b a p (fun _ _ => rfl) v
  have hsum : c.sum (fun g a => a • ρ g.val (v i)) = Compact.orbitMean b v i := by
    rw [← hc, Finsupp.sum, Finsupp.sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun _ _ => rfl
  exact hsum.trans h

private theorem exists_typeCombination {I : Type*} [Finite I] (v : I → V) :
    ∃ c : MonoidAlgebra ℂ K, ∀ i, κ.asAlgebraHom c (v i) = intertwiner τ κ (v i) := by
  let R := MonoidAlgebra ℂ K
  let w : I → κ.asModule := fun i => κ.asModuleEquiv.symm (v i)
  let span := Submodule.span R {w}
  have hw : w ∈ span := Submodule.mem_span_singleton_self w
  have hp := projection_mem_of_mem (S := τ.asModule) span hw
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hp
  refine ⟨c, fun i => ?_⟩
  have heq := projection_natural (S := τ.asModule) (LinearMap.proj (R := R) i) w
  change κ.asModuleEquiv ((c • w) i) =
    κ.asModuleEquiv (projection R κ.asModule τ.asModule (w i))
  rw [hc]
  exact congrArg κ.asModuleEquiv heq

/-- If the compact generators act independently of the parameter, on any
finite-dimensional subspace one algebra element implements the joint
projection at every parameter. -/
theorem exists_jointCompactProjection_operator {A T : Type*} [Ring A] [Algebra ℂ A]
    (a : T → A →ₐ[ℂ] Module.End ℂ V)
    (fin : L → A) (inf : K → A)
    (hfin : ∀ t g, a t (fin g) = ρ g.val) (hinf : ∀ t k, a t (inf k) = κ k)
    (S : Submodule ℂ V) [FiniteDimensional ℂ S] :
    ∃ b : A, ∀ t v, v ∈ S → a t b v = jointCompactProjection τ ρ κ hρ L hL v := by
  classical
  let e := Module.finBasis ℂ S
  let v (i : Fin (Module.finrank ℂ S)) := (e i).val
  obtain ⟨cK, hcK⟩ := exists_typeCombination τ κ v
  obtain ⟨cL, hcL⟩ := exists_averageCombination ρ hρ L hL fun i => intertwiner τ κ (v i)
  let B := Finsupp.linearCombination ℂ inf
  let bK := B cK.coeff
  let bL := Finsupp.linearCombination ℂ fin cL
  have hK (t : T) (c : MonoidAlgebra ℂ K) : a t (B c.coeff) = κ.asAlgebraHom c := by
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq => simp [hp, hq]
    | single k z => simp [B, hinf]
  have hLword (t : T) (x : V) : a t bL x = cL.sum fun g z => z • ρ g.val x := by
    simp only [bL, Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
      LinearMap.sum_apply, map_smul, LinearMap.smul_apply, hfin]
  refine ⟨bL * bK, fun t x hx => ?_⟩
  have heq : (a t (bL * bK)).comp S.subtype =
      (jointCompactProjection τ ρ κ hρ L hL).comp S.subtype := by
    apply e.ext
    intro i
    change a t (bL * bK) (v i) = Compact.averageMap ρ hρ L hL (intertwiner τ κ (v i))
    rw [map_mul, Module.End.mul_apply, show a t bK = κ.asAlgebraHom cK from hK t cK,
      hcK, hLword, hcL]
  exact LinearMap.congr_fun heq (⟨x, hx⟩ : S)

end Langlands.Automorphic
