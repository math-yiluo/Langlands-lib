import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Smooth postcomposition actions on alternating maps -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 40000

universe uk ug um uv uw

namespace Langlands.AlternatingCoefficients

variable {k : Type uk} [Field k] {G : Type ug} [Group G]
  {M : Type um} [AddCommGroup M] [Module k M]
  {V : Type uv} [AddCommGroup V] [Module k V]
  {W : Type uw} [AddCommGroup W] [Module k W]

/-- The group acts on alternating maps by postcomposition on their values. -/
def action (ρ : Representation k G V) (q : ℕ) :
    Representation k G (M [⋀^Fin q]→ₗ[k] V) where
  toFun g :=
    { toFun := (ρ g).compAlternatingMap
      map_add' := (ρ g).compAlternatingMap_add
      map_smul' := (ρ g).compAlternatingMap_smul }
  map_one' := by
    apply LinearMap.ext
    intro f
    apply AlternatingMap.ext
    intro x
    exact LinearMap.congr_fun ρ.map_one (f x)
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    apply AlternatingMap.ext
    intro x
    exact LinearMap.congr_fun (ρ.map_mul g h) (f x)

@[simp] theorem action_apply (ρ : Representation k G V) (q : ℕ) (g : G)
    (f : M [⋀^Fin q]→ₗ[k] V) (x : Fin q → M) :
    action ρ q g f x = ρ g (f x) := rfl

/-- A coefficient intertwiner acts on alternating maps by the same postcomposition. -/
def map {ρ : Representation k G V} {σ : Representation k G W}
    (A : ρ.IntertwiningMap σ) (q : ℕ) :
    (action (M := M) ρ q).IntertwiningMap (action (M := M) σ q) where
  toLinearMap :=
    { toFun := A.toLinearMap.compAlternatingMap
      map_add' := A.toLinearMap.compAlternatingMap_add
      map_smul' := A.toLinearMap.compAlternatingMap_smul }
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply AlternatingMap.ext
    intro x
    exact LinearMap.congr_fun (A.isIntertwining' g) (f x)

@[simp] theorem map_apply {ρ : Representation k G V} {σ : Representation k G W}
    (A : ρ.IntertwiningMap σ) (q : ℕ) (f : M [⋀^Fin q]→ₗ[k] V)
    (x : Fin q → M) :
    map A q f x = A (f x) := rfl

variable [TopologicalSpace G] [FiniteDimensional k M]

/-- Finitely many basis-tuple values give a common open stabilizer of each map. -/
theorem isSmooth {ρ : Representation k G V} (hρ : Langlands.IsSmooth ρ) (q : ℕ) :
    Langlands.IsSmooth (action (M := M) ρ q) := by
  classical
  intro f
  let b := Module.finBasis k M
  choose U hU using fun v : Fin q → Fin (Module.finrank k M) =>
    hρ (f (fun i => b (v i)))
  let K : OpenSubgroup G := Finset.univ.inf U
  refine ⟨K, ?_⟩
  intro g
  apply b.ext_alternating
  intro v _
  exact hU v ⟨g, (Finset.inf_le (Finset.mem_univ v) : K ≤ U v) g.property⟩

end Langlands.AlternatingCoefficients
