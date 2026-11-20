import Langlands.Global.AdelicEisensteinConstantTermStatement
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! # Injectivity from distinct characters in an Eisenstein constant term -/

noncomputable section

set_option autoImplicit false

open CategoryTheory _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.Global.EisensteinJet

variable {I H X V : Type*} [Fintype I] [MulOneClass H] [AddCommGroup V] [Module ℂ V]

/-- The sum of the supplied constant-term components. -/
def constantTermSum (C : I → V →ₗ[ℂ] (X → ℂ)) : V →ₗ[ℂ] (X → ℂ) :=
  ∑ i, C i

/-- Distinct characters allow a nonzero input to be detected by any injective
component of the constant term. -/
theorem constantTermSum_injective (C : I → V →ₗ[ℂ] (X → ℂ))
    (move : H → X → X) (χ : I → H →* ℂ) (hχ : Function.Injective χ)
    (hc : ∀ i v a x, C i v (move a x) = χ i a * C i v x)
    (e : I) (he : Function.Injective (C e)) :
    Function.Injective (constantTermSum C) := by
  have hli := (linearIndependent_monoidHom H ℂ).comp χ hχ
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  apply he
  rw [map_zero]
  funext x
  have hcomb : ∑ i, C i v x • (fun a => χ i a) = (0 : H → ℂ) := by
    funext a
    have hz := congrFun hv (move a x)
    simp only [constantTermSum, LinearMap.sum_apply, Finset.sum_apply, hc, Pi.zero_apply] at hz
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_comm] using hz
  exact (Fintype.linearIndependent_iff.mp hli (fun i => C i v x) hcomb) e

open AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P N : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine N.X.left]
  [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {K : Subgroup (AdelicGroupPoints F G)}

/-- An actual Eisenstein series is injective on a section subspace once its
constant term has a distinct-character expansion with the twisted input as
one component. -/
theorem eisensteinSeries_injective_of_constantTerm (hK : IsIwasawaCompact p K)
    (j : N ⟶ G) [IsClosedImmersion j.hom.hom.left] (lam : ComplexCharacterParameter F P)
    (D : Submodule ℂ (AdelicGroupPoints F G → ℂ))
    (C : I → D →ₗ[ℂ] (AdelicGroupPoints F G → ℂ))
    (move : H → AdelicGroupPoints F G → AdelicGroupPoints F G)
    (χ : I → H →* ℂ) (hχ : Function.Injective χ)
    (hc : ∀ i v a x, C i v (move a x) = χ i a * C i v x)
    (e : I) (he : ∀ v : D, C e v = hK.parameterTwist v.val lam)
    (hCT : ∀ v : D, subgroupConstantTerm F j (hK.eisensteinSeries v.val lam) =
      constantTermSum C v) :
    Function.Injective (fun v : D => hK.eisensteinSeries v.val lam) := by
  have hi : Function.Injective (C e) := by
    intro x y hxy
    apply Subtype.ext
    funext g
    rw [he, he] at hxy
    exact mul_right_cancel₀ (Complex.exp_ne_zero _) (congrFun hxy g)
  intro x y hxy
  apply constantTermSum_injective C move χ hχ hc e hi
  rw [← hCT x, ← hCT y]
  exact congrArg (subgroupConstantTerm F j) hxy

end Langlands.Global.EisensteinJet
