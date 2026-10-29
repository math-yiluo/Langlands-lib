import Langlands.Algebra.UnitizationIdealNoetherianStatements
import Langlands.Algebra.UnitizationRegularKernel
import Langlands.Algebra.UnitizationNoetherianProof
import Langlands.Algebra.UnitizationStableGenerationProof
import Langlands.Algebra.AdditiveUnitizationGenerationProof
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain

set_option autoImplicit false

namespace Langlands.Algebra.UnitizationIdealNoetherian

universe uR uA

theorem noetherian_iff_scalar_and_regular
    (R : Type uR) (A : Type uA)
    [CommRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    [Module (Unitization R A) A]
    (hsmul : ∀ (u : Unitization R A) (a : A),
      u • a = u.fst • a + u.snd * a) :
    IsNoetherianRing (Unitization R A) ↔
      IsNoetherianRing R ∧ IsNoetherian (Unitization R A) A := by
  rw [UnitizationNoetherian.noetherian_iff_kernel R A]
  exact and_congr_right fun _ =>
    (UnitizationRegularKernel.regularKernelEquiv R A hsmul).isNoetherian_iff.symm

theorem noetherian_iff_regular
    (R : Type uR) (A : Type uA)
    [CommRing R] [IsNoetherianRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    [Module (Unitization R A) A]
    (hsmul : ∀ (u : Unitization R A) (a : A),
      u • a = u.fst • a + u.snd * a) :
    IsNoetherianRing (Unitization R A) ↔ IsNoetherian (Unitization R A) A := by
  rw [noetherian_iff_scalar_and_regular R A hsmul]
  constructor
  · exact And.right
  · intro h
    exact ⟨inferInstance, h⟩

theorem noetherian_iff_scalar_stable_ideals
    (R : Type uR) (A : Type uA)
    [CommRing R] [IsNoetherianRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    [Module (Unitization R A) A] [IsScalarTower R (Unitization R A) A]
    (hsmul : ∀ (u : Unitization R A) (a : A),
      u • a = u.fst • a + u.snd * a) :
    IsNoetherianRing (Unitization R A) ↔
      ∀ P : Submodule R A,
        (∀ (a x : A), x ∈ P → a * x ∈ P) →
        ∃ S : Finset A, (↑S : Set A) ⊆ P ∧
          ∀ Q : Submodule R A,
            (∀ (a x : A), x ∈ Q → a * x ∈ Q) →
            (↑S : Set A) ⊆ Q → P ≤ Q := by
  exact (noetherian_iff_regular R A hsmul).trans
    (UnitizationStableGeneration.noetherian_iff_stable_generators
      R A A (NonUnitalAlgHom.lmul R A) hsmul)

theorem noetherian_iff_additive_stable_ideals
    (A : Type uA) [NonUnitalRing A] [Module (Unitization ℤ A) A]
    (hsmul : ∀ (u : Unitization ℤ A) (a : A),
      u • a = u.fst • a + u.snd * a) :
    IsNoetherianRing (Unitization ℤ A) ↔
      ∀ P : AddSubgroup A,
        (∀ (a x : A), x ∈ P → a * x ∈ P) →
        ∃ S : Finset A, (↑S : Set A) ⊆ P ∧
          ∀ Q : AddSubgroup A,
            (∀ (a x : A), x ∈ Q → a * x ∈ Q) →
            (↑S : Set A) ⊆ Q → P ≤ Q := by
  let ρ : A →ₙ+* AddMonoid.End A :=
    { toFun := AddMonoidHom.mulLeft
      map_zero' := by ext x; exact zero_mul x
      map_add' := by intro a b; ext x; exact add_mul a b x
      map_mul' := by intro a b; ext x; exact mul_assoc a b x }
  exact (noetherian_iff_regular ℤ A hsmul).trans
    (AdditiveUnitizationGeneration.noetherian_iff_additive_stable_generators
      A A ρ hsmul)

theorem regularCriterion : RegularCriterionStatement.{uR, uA} :=
  noetherian_iff_scalar_and_regular

theorem scalarIdealCriterion : ScalarIdealCriterionStatement.{uR, uA} :=
  noetherian_iff_scalar_stable_ideals

theorem additiveIdealCriterion : AdditiveIdealCriterionStatement.{uA} :=
  noetherian_iff_additive_stable_ideals

theorem unitizationIdealNoetherian : UnitizationIdealNoetherianStatement.{uR, uA} :=
  ⟨regularCriterion, scalarIdealCriterion, additiveIdealCriterion⟩

end Langlands.Algebra.UnitizationIdealNoetherian
