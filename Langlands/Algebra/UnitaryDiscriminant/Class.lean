import Langlands.Algebra.UnitaryDiscriminant.Cocycle
import Langlands.Algebra.BrauerComparison.AbsoluteComparison

/-! # The discriminant Brauer class of an algebra with unitary involution -/

noncomputable section

universe u v

open Matrix
open scoped TensorProduct

namespace Langlands.UnitaryDiscriminant

open ClassFieldTheory.Local (relativeCohomology)
open ScalarTwoCocycle (IsTwoCocycle coboundary)
open BrauerComparison LinearAlgebra.UnitaryTwistedDescent

attribute [local instance] Classical.decEq

variable {F L M : Type u} [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]
  [Algebra L M] [IsScalarTower F L M] [Algebra.IsQuadraticExtension F L]
  {B : Type v} [Ring B] [Algebra L B] {m : ℕ}
  {ι : L ≃ₐ[F] L} (hι : ι ≠ 1) {τ : B → B} (hτ : IsUnitaryInvolution ι τ)
  (e : M ⊗[L] B ≃ₐ[M] Matrix (Fin (2 * m)) (Fin (2 * m)) M)

/-- The discriminant factor set of `(B, τ)` computed in the chart `e`:
`μ(g, h) = λ(g, h)^m · g(det P_h)^{ε(g)} · (-1)^{m ε(g) ε(h)}`, where `P = chartLift hι hτ e`,
`λ = chartFactor hι hτ e`, and `ε(g) = 1` exactly when `g` acts nontrivially on `L`. -/
def discriminantCocycle (g h : Gal(M/F)) : Mˣ :=
  detCocycle (centerFixing F L M) (chartLift hι hτ e) (chartFactor hι hτ e) m g h

/-- The discriminant factor set is a two-cocycle of `Gal(M/F)` with values in `Mˣ`. -/
theorem discriminantCocycle_isTwoCocycle : IsTwoCocycle (discriminantCocycle hι hτ e) :=
  detCocycle_isTwoCocycle_of_lifts (mul_mem_centerFixing_iff hι) _ _ (chartLift_mul hι hτ e) m
    (Fintype.card_fin _)

/-- On automorphisms fixing `L` the discriminant factor set is `λ(g, h)^m`. -/
theorem discriminantCocycle_of_mem {g : Gal(M/F)} (hg : g ∈ centerFixing F L M)
    (h : Gal(M/F)) :
    discriminantCocycle hι hτ e g h = chartFactor hι hτ e g h ^ m :=
  detCocycle_of_mem _ _ m hg h

/-- The square of the discriminant factor set is the coboundary of the determinants of the
chosen lifts. -/
theorem discriminantCocycle_mul_self (g h : Gal(M/F)) :
    discriminantCocycle hι hτ e g h * discriminantCocycle hι hτ e g h =
      coboundary (fun t => GeneralLinearGroup.det (chartLift hι hτ e t)) g h :=
  detCocycle_mul_self _ _ m
    (fun g h => by
      have h' := det_mul_twistUnit _ _ (chartLift_mul hι hτ e) g h
      rwa [Fintype.card_fin] at h') g h

/-- The discriminant class of `(B, τ)` in the relative cohomology `H²(Gal(M/F), Mˣ)`. -/
def relativeDiscriminantClass : relativeCohomology F M 2 :=
  unitClass (discriminantCocycle hι hτ e) (discriminantCocycle_isTwoCocycle hι hτ e)

/-- The relative discriminant class is killed by two. -/
theorem two_nsmul_relativeDiscriminantClass : 2 • relativeDiscriminantClass hι hτ e = 0 := by
  have hc := discriminantCocycle_isTwoCocycle hι hτ e
  have hcc : IsTwoCocycle (fun s t => discriminantCocycle hι hτ e s t *
      discriminantCocycle hι hτ e s t) := by
    intro g h k
    simp only [smul_mul']
    rw [mul_mul_mul_comm, hc g h k, mul_mul_mul_comm]
  rw [two_nsmul, relativeDiscriminantClass, ← unitClass_mul hc hc hcc, unitClass_eq_zero_iff]
  exact ⟨_, discriminantCocycle_mul_self hι hτ e⟩

/-- The relative discriminant class may be computed with any family of lifts with the defining
property of `chartLift` and any factor set for it: the class does not depend on the choices made
in `chartLift` and `chartFactor`. -/
theorem relativeDiscriminantClass_eq_of_lifts (P : Gal(M/F) → GL (Fin (2 * m)) M)
    (c : Gal(M/F) → Gal(M/F) → Mˣ)
    (hin : ∀ g ∈ centerFixing F L M, ∀ b : B,
      twistedAct (centerFixing F L M) P g (chartMap e b) = chartMap e b)
    (hout : ∀ g ∉ centerFixing F L M, ∀ b : B,
      twistedAct (centerFixing F L M) P g (chartMap e b) = chartMap e (τ b))
    (hc : ∀ g h, P g * twistGL (centerFixing F L M) g (P h) =
      GeneralLinearGroup.scalar (Fin (2 * m)) (c g h) * P (g * h)) :
    unitClass (detCocycle (centerFixing F L M) P c m)
        (detCocycle_isTwoCocycle_of_lifts (mul_mem_centerFixing_iff hι) P c hc m
          (Fintype.card_fin _)) =
      relativeDiscriminantClass hι hτ e := by
  have hb (g : Gal(M/F)) : ∃ b : Mˣ,
      P g = GeneralLinearGroup.scalar (Fin (2 * m)) b * chartLift hι hτ e g := by
    apply exists_scalar_of_twistedAct_eq
    apply twistedAct_eq_of_chartMap e
    intro b
    by_cases hg : g ∈ centerFixing F L M
    · rw [hin g hg, twistedAct_chartLift_of_mem hι hτ e hg]
    · rw [hout g hg, twistedAct_chartLift_of_not_mem hι hτ e hg]
  choose b hb using hb
  exact unitClass_eq_of_coboundary_mul _ _ (fun t => b t ^ m)
    (detCocycle_eq_coboundary_mul _ _ (chartLift_mul hι hτ e) P c hc m (Fintype.card_fin _) b hb)

variable [FiniteDimensional F M] [IsGalois F M]

/-- An actual central simple `F`-algebra representing the discriminant class: the fixed
algebra of the regular matrix representation twisted by the discriminant factor set. -/
def discriminantCSA : CSA.{u, u} F :=
  regularCSA (discriminantCocycle hι hτ e) (discriminantCocycle_isTwoCocycle hι hτ e)

/-- The splitting chart of `discriminantCSA` over `M`. -/
def discriminantSplittingChart :
    M ⊗[F] discriminantCSA hι hτ e ≃ₐ[M] Matrix (Gal(M/F)) (Gal(M/F)) M :=
  regularSplittingChart (discriminantCocycle hι hτ e) (discriminantCocycle_isTwoCocycle hι hτ e)

/-- The relative class of `discriminantCSA` in its splitting chart is the class of the
discriminant factor set. -/
theorem relativeClass_discriminantSplittingChart :
    relativeClass (discriminantSplittingChart hι hτ e) = relativeDiscriminantClass hι hτ e :=
  relativeClass_regularSplittingChart _ _

/-- The discriminant Brauer class of the algebra with unitary involution `(B, τ)` over `F`,
computed through the splitting chart `e`. -/
def discriminantClass : BrauerGroup.{u, u} F :=
  Brauer.classOf (discriminantCSA hι hτ e)

/-- Under the comparison of the Brauer group with continuous Galois cohomology, the
discriminant class is the inflation of the relative discriminant class. -/
theorem brauerContinuousEquiv_discriminantClass (S : Type u) [Field S] [Algebra F S]
    [IsSepClosure F S] [Algebra M S] [IsScalarTower F M S] :
    brauerContinuousEquiv F S (discriminantClass hι hτ e) =
      relativeToContinuous F M S 2 (relativeDiscriminantClass hι hτ e) := by
  rw [discriminantClass,
    brauerContinuousEquiv_at_chart F S _ M (discriminantSplittingChart hι hτ e),
    relativeClass_discriminantSplittingChart]

/-- The discriminant Brauer class is killed by two. -/
theorem two_nsmul_discriminantClass : 2 • discriminantClass hι hτ e = 0 := by
  let j : M →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let : Algebra M (SeparableClosure F) := j.toRingHom.toAlgebra
  let : IsScalarTower F M (SeparableClosure F) := IsScalarTower.of_algHom j
  apply (brauerEquiv F).injective
  rw [map_nsmul, map_zero, brauerContinuousEquiv_discriminantClass, ← map_nsmul,
    two_nsmul_relativeDiscriminantClass, map_zero]

end Langlands.UnitaryDiscriminant
