import Langlands.Automorphic.AlgebraOperatorSubquotient
import Langlands.Automorphic.CompactSpecializationTypeChoice

/-! # Compact lifts of a simple operator specialization -/

noncomputable section

open scoped MonoidAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1050000

namespace Langlands.Automorphic

variable {R : Type*} [Ring R] [Algebra ℂ R]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {aV : R →ₐ[ℂ] Module.End ℂ V} {aW : R →ₐ[ℂ] Module.End ℂ W}
  (S : Subrepresentation aV.toMonoidHom) (q : S.toRepresentation.IntertwiningMap aW.toMonoidHom)

/-- The equivariant quotient of an invariant complex subspace, viewed as a
linear map for the acting algebra. -/
def operatorNumeratorQuotient :
    letI := moduleOfAlgebraAction aV
    letI := moduleOfAlgebraAction aW
    (submoduleOrderIsoOfAlgebraAction aV).symm S →ₗ[R] W := by
  letI := moduleOfAlgebraAction aV
  letI := moduleOfAlgebraAction aW
  exact
    { toFun := fun x => q x
      map_add' := fun x y => q.map_add x y
      map_smul' := fun r x => Representation.IntertwiningMap.isIntertwining _ _ q r x }

variable {H : Type*} [Monoid H]
  {ρ : Representation ℂ H V} {σ : Representation ℂ H W}
  (ops : H → R) (hρ : ∀ g, aV (ops g) = ρ g)

private def operatorNumeratorAction : Subrepresentation ρ where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule g v hv := by
    rw [← hρ g]
    exact S.apply_mem_toSubmodule (ops g) hv

private def operatorNumeratorInclusion : (operatorNumeratorAction S ops hρ).toRepresentation.IntertwiningMap ρ :=
  ⟨S.toSubmodule.subtype, fun _ => rfl⟩

private def operatorNumeratorProjection (hσ : ∀ g, aW (ops g) = σ g) :
    (operatorNumeratorAction S ops hρ).toRepresentation.IntertwiningMap σ :=
  ⟨q.toLinearMap, fun g => LinearMap.ext fun x => by
    rw [← hσ g]
    have hg : (operatorNumeratorAction S ops hρ).toRepresentation g x =
        S.toRepresentation (ops g) x := Subtype.ext (LinearMap.congr_fun (hρ g).symm x.val)
    change q ((operatorNumeratorAction S ops hρ).toRepresentation g x) = aW (ops g) (q x)
    rw [hg]
    exact Representation.IntertwiningMap.isIntertwining _ _ q (ops g) x⟩

/-- A simple specialization has a nonzero compact-type fiber preserved by a
finite-rank projection. Its action on any finite-dimensional space is given
by one algebra element at all parameters, using the parameter-independent
compact generators. -/
theorem exists_jointCompactProjection_of_operatorSpecialization
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K : Type*} [Group K] {E : Type*}
    (a : E → R →ₐ[ℂ] Module.End ℂ V) (z : E)
    (ρ : Representation ℂ G V) (κ : Representation ℂ K V)
    (σ : Representation ℂ G W) (ν : Representation ℂ K W)
    (fin : G → R) (inf : K → R)
    (hfin : ∀ g, a z (fin g) = ρ g) (hinf : ∀ t k, a t (inf k) = κ k)
    (hσ : ∀ g, aW (fin g) = σ g) (hν : ∀ k, aW (inf k) = ν k)
    (hsmooth : Langlands.IsSmooth ρ) (hfinite : ∀ v, Langlands.FiniteVectors.IsFiniteVector κ v)
    [IsSemisimpleModule ℂ[K] κ.asModule]
    (hcomm : ∀ g k v, ρ g (κ k v) = κ k (ρ g v)) (hadm : Langlands.IsJointlyAdmissible ρ κ)
    (L₀ : OpenSubgroup G) (hL₀ : IsCompact (L₀ : Set G))
    (hLgen : ∀ t (g : L₀), a t (fin g.val) = ρ g.val)
    (ha : Representation.IsIrreducible aW.toMonoidHom)
    (S : Subrepresentation (a z).toMonoidHom) (q : S.toRepresentation.IntertwiningMap aW.toMonoidHom)
    (hq : Function.Surjective q) :
    ∃ π : Module.End ℂ V, FiniteDimensional ℂ π.range ∧
      (∀ M : Submodule ℂ V, FiniteDimensional ℂ M → ∃ b : R, ∀ t v, v ∈ M → a t b v = π v) ∧
      ∃ y : W, y ≠ 0 ∧ (∀ x : S.toSubmodule, q x = y →
        ∃ x' : S.toSubmodule, x'.val = π x.val ∧ q x' = y) := by
  let finS : Representation ℂ G S.toSubmodule := (operatorNumeratorAction S fin hfin).toRepresentation
  let infS : Representation ℂ K S.toSubmodule := (operatorNumeratorAction S inf (hinf z)).toRepresentation
  let iFin : finS.IntertwiningMap ρ := operatorNumeratorInclusion S fin hfin
  let iInf : infS.IntertwiningMap κ := operatorNumeratorInclusion S inf (hinf z)
  let qFin : finS.IntertwiningMap σ := operatorNumeratorProjection S q fin hfin hσ
  let qInf : infS.IntertwiningMap ν := operatorNumeratorProjection S q inf (hinf z) hν
  have hiFin : Function.Injective iFin := Subtype.val_injective
  have hiInf : Function.Injective iInf := Subtype.val_injective
  have hfinS := Langlands.isSmooth_of_injective iFin hiFin hsmooth
  have hfinW := Langlands.isSmooth_of_surjective qFin hq hfinS
  let : IsSemisimpleModule ℂ[K] infS.asModule :=
    IsSemisimpleModule.of_injective (Representation.IntertwiningMap.equivLinearMapAsModule _ _ iInf) hiInf
  let : IsSemisimpleModule ℂ[K] ν.asModule :=
    IsSemisimpleModule.of_surjective (Representation.IntertwiningMap.equivLinearMapAsModule _ _ qInf) hq
  have hinfW (y : W) : Langlands.FiniteVectors.IsFiniteVector ν y := by
    obtain ⟨x, rfl⟩ := (show Function.Surjective qInf from hq) y
    exact ((Langlands.FiniteVectors.isFiniteVector_map_iff iInf hiInf x).mp (hfinite (iInf x))).map qInf
  let := moduleOfAlgebraAction aW
  let := (isSimpleModule_iff_irreducible_algebraAction aW).mpr ha
  let : Nontrivial W := IsSimpleModule.nontrivial R W
  obtain ⟨L, hLle, hL, d, τ, hτ, y, hy, hyF, hyK⟩ :=
    exists_nonzero_jointCompactType σ ν hfinW hinfW L₀ hL₀
  let := hτ
  let π := jointCompactProjection τ ρ κ hsmooth L hL
  refine ⟨π, finiteDimensional_range_jointCompactProjection τ ρ κ hsmooth L hL hcomm hadm,
    ?_, y, hy, ?_⟩
  · intro M hM
    let := hM
    exact exists_jointCompactProjection_operator τ ρ κ hsmooth L hL a
      (fun g => fin g.val) inf (fun t g => hLgen t ⟨g.val, hLle g.property⟩) hinf M
  · intro x hx
    refine ⟨jointCompactQuotientLift τ finS infS hfinS L hL x, ?_⟩
    exact jointCompactQuotientLift_spec τ finS infS hfinS L hL ρ κ hsmooth σ ν hfinW
      iFin.toLinearMap qFin.toLinearMap
      (Representation.IntertwiningMap.isIntertwining _ _ iFin)
      (Representation.IntertwiningMap.isIntertwining _ _ iInf)
      (Representation.IntertwiningMap.isIntertwining _ _ qFin)
      (Representation.IntertwiningMap.isIntertwining _ _ qInf) x hx hyF hyK

end Langlands.Automorphic
