import Langlands.Representation.Jacquet.AlgebraStatement

namespace Langlands.Jacquet

open Representation

universe uG uV

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

section Tower

variable (rho : Representation ℂ G V) (N P : Subgroup G)

/-- For `N ≤ P`, the single `P`-quotient map kills the `N`-relations, so it
factors through the `N`-coinvariants. -/
noncomputable def coinvariantTowerStep (hNP : N ≤ P) :
    Coinvariants (rho.comp N.subtype) →ₗ[ℂ] Coinvariants (rho.comp P.subtype) :=
  Coinvariants.lift (rho.comp N.subtype) (Coinvariants.mk (rho.comp P.subtype)) fun n =>
    LinearMap.ext fun v =>
      Coinvariants.mk_self_apply (rho.comp P.subtype) ⟨(n : G), hNP n.2⟩ v

@[simp]
theorem coinvariantTowerStep_mk (hNP : N ≤ P) (v : V) :
    coinvariantTowerStep rho N P hNP (Coinvariants.mk (rho.comp N.subtype) v) =
      Coinvariants.mk (rho.comp P.subtype) v :=
  rfl

variable [N.Normal]

/-- The forward map `(V_N)_P → V_P`: `coinvariantTowerStep` kills the
`P`-relations on `V_N`, so it factors through the second quotient. -/
noncomputable def coinvariantTowerForward (hNP : N ≤ P) :
    Coinvariants ((rho.toCoinvariants N).comp P.subtype) →ₗ[ℂ]
      Coinvariants (rho.comp P.subtype) :=
  Coinvariants.lift ((rho.toCoinvariants N).comp P.subtype)
    (coinvariantTowerStep rho N P hNP) fun p =>
      Coinvariants.hom_ext <| LinearMap.ext fun v =>
        Coinvariants.mk_self_apply (rho.comp P.subtype) p v

@[simp]
theorem coinvariantTowerForward_mk_mk (hNP : N ≤ P) (v : V) :
    coinvariantTowerForward rho N P hNP
        (Coinvariants.mk ((rho.toCoinvariants N).comp P.subtype)
          (Coinvariants.mk (rho.comp N.subtype) v)) =
      Coinvariants.mk (rho.comp P.subtype) v :=
  rfl

/-- The backward map `V_P → (V_N)_P`: the composite of the two quotient maps
kills the `P`-relations on `V`. -/
noncomputable def coinvariantTowerBackward :
    Coinvariants (rho.comp P.subtype) →ₗ[ℂ]
      Coinvariants ((rho.toCoinvariants N).comp P.subtype) :=
  Coinvariants.lift (rho.comp P.subtype)
    (Coinvariants.mk ((rho.toCoinvariants N).comp P.subtype) ∘ₗ
      Coinvariants.mk (rho.comp N.subtype)) fun p =>
    LinearMap.ext fun v =>
      Coinvariants.mk_self_apply ((rho.toCoinvariants N).comp P.subtype) p
        (Coinvariants.mk (rho.comp N.subtype) v)

@[simp]
theorem coinvariantTowerBackward_mk (v : V) :
    coinvariantTowerBackward rho N P (Coinvariants.mk (rho.comp P.subtype) v) =
      Coinvariants.mk ((rho.toCoinvariants N).comp P.subtype)
        (Coinvariants.mk (rho.comp N.subtype) v) :=
  rfl

theorem coinvariantTowerBackward_forward (hNP : N ≤ P)
    (x : Coinvariants ((rho.toCoinvariants N).comp P.subtype)) :
    coinvariantTowerBackward rho N P (coinvariantTowerForward rho N P hNP x) = x := by
  induction x using Coinvariants.induction_on with
  | h y =>
    induction y using Coinvariants.induction_on with
    | h v => rfl

theorem coinvariantTowerForward_backward (hNP : N ≤ P)
    (x : Coinvariants (rho.comp P.subtype)) :
    coinvariantTowerForward rho N P hNP (coinvariantTowerBackward rho N P x) = x := by
  induction x using Coinvariants.induction_on with
  | h v => rfl

variable [P.Normal]

/-- The forward map intertwines the descended actions of the ambient group. -/
theorem coinvariantTowerForward_comp (hNP : N ≤ P) (g : G) :
    coinvariantTowerForward rho N P hNP ∘ₗ (rho.toCoinvariants N).toCoinvariants P g =
      rho.toCoinvariants P g ∘ₗ coinvariantTowerForward rho N P hNP := by
  refine LinearMap.ext fun x => ?_
  induction x using Coinvariants.induction_on with
  | h y =>
    induction y using Coinvariants.induction_on with
    | h v => rfl

/-- The actual equivalence of `G`-representations `(V_N)_P ≃ V_P`. -/
noncomputable def coinvariantTowerEquiv (hNP : N ≤ P) :
    ((rho.toCoinvariants N).toCoinvariants P).Equiv (rho.toCoinvariants P) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinearMap (coinvariantTowerForward rho N P hNP)
      (coinvariantTowerBackward rho N P)
      (LinearMap.ext fun x => coinvariantTowerForward_backward rho N P hNP x)
      (LinearMap.ext fun x => coinvariantTowerBackward_forward rho N P hNP x))
    (coinvariantTowerForward_comp rho N P hNP)

@[simp]
theorem coinvariantTowerEquiv_mk_mk (hNP : N ≤ P) (v : V) :
    coinvariantTowerEquiv rho N P hNP
        (Coinvariants.mk ((rho.toCoinvariants N).comp P.subtype)
          (Coinvariants.mk (rho.comp N.subtype) v)) =
      Coinvariants.mk (rho.comp P.subtype) v :=
  rfl

@[simp]
theorem coinvariantTowerEquiv_symm_mk (hNP : N ≤ P) (v : V) :
    (coinvariantTowerEquiv rho N P hNP).symm (Coinvariants.mk (rho.comp P.subtype) v) =
      Coinvariants.mk ((rho.toCoinvariants N).comp P.subtype)
        (Coinvariants.mk (rho.comp N.subtype) v) :=
  rfl

end Tower

/-- Algebraic transitivity of normal-subgroup coinvariants, with exactly the
published target. -/
theorem coinvariantTower : CoinvariantTowerStatement (G := G) (V := V) := by
  intro rho N P _ _ hNP
  exact ⟨coinvariantTowerEquiv rho N P hNP, coinvariantTowerEquiv_mk_mk rho N P hNP⟩

end Langlands.Jacquet
