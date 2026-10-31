import Langlands.AbelianScheme.Tate.WeilPrimeRationalPolarizationNondegeneracyReductionStatement
import Langlands.AbelianScheme.AlgClosedIsogenyPoints
import Langlands.AbelianScheme.Tate.PrimeAdicSeparation

/-! # Rational prime-adic polarization nondegeneracy from finite levels -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (T : Over S) (p : ℕ) [Fact p.Prime]

local notation "GA" => dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
  stability composition unitCoherence associativity comparison symmetry
local notation "GD" => Langlands.CommGroupScheme.toGrp GA
local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "levelPair" => finiteWeilLevelBilinearMap preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA
local notation "primePair" => primeWeilBilinearMap preservation composition unitCoherence
  associativity comparison symmetry stability hA MA evaluationA compatibility T p
local notation "primeIntegralAlong" => primeWeilAlongHomBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility T p
local notation "primeAlong" => primeRationalWeilAlongHomBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility T p

/-- Left separation at every prime-power level, together with surjective coordinate
projections of the dual Tate module, gives left separation of the prime-adic pairing. -/
theorem primeWeilBilinearMap_separatingLeft
    (hlevel : ∀ (n : ℕ) x, (∀ y, levelPair (p ^ n) T x y = 0) → x = 0)
    (hsurj : ∀ n, Function.Surjective (GroupScheme.Tate.PrimeAdic.evaluation GD T p n)) :
    (primePair).SeparatingLeft := by
  intro x hx
  apply Subtype.ext
  funext n
  apply hlevel n (x.val n)
  intro w
  obtain ⟨z, rfl⟩ := hsurj n w
  have h := congrArg (TateTwist.evaluation Γ(T.left, ⊤) p n) (hx z)
  rw [map_zero] at h
  exact h

/-- Right separation at every prime-power level, together with surjective coordinate
projections of the Tate module of `A`, gives right separation of the prime-adic pairing. -/
theorem primeWeilBilinearMap_separatingRight
    (hlevel : ∀ (n : ℕ) y, (∀ x, levelPair (p ^ n) T x y = 0) → y = 0)
    (hsurj : ∀ n, Function.Surjective (GroupScheme.Tate.PrimeAdic.evaluation A.toGrp T p n)) :
    (primePair).SeparatingRight := by
  intro z hz
  apply Subtype.ext
  funext n
  apply hlevel n (z.val n)
  intro w
  obtain ⟨x, rfl⟩ := hsurj n w
  have h := congrArg (TateTwist.evaluation Γ(T.left, ⊤) p n) (hz x)
  rw [map_zero] at h
  exact h

/-- Pulling back a nondegenerate prime-adic pairing along a homomorphism with a
quasi-inverse on points gives a nondegenerate integral pairing. -/
theorem primeWeilAlongHomBilinearMap_nondegenerate (lam : A ⟶ DA)
    (hL : (primePair).SeparatingLeft) (hR : (primePair).SeparatingRight)
    {N : ℕ} (hN : 0 < N)
    (hker : ∀ x : T ⟶ A.toGrp.X, x ≫ (groupHom lam).hom.hom = 1 → x ^ N = 1)
    (ψ : (T ⟶ (DA).toGrp.X) →* (T ⟶ A.toGrp.X))
    (hψ : ∀ y, ψ y ≫ (groupHom lam).hom.hom = y ^ N) :
    (primeIntegralAlong lam).Nondegenerate := by
  constructor
  · intro x hx
    apply hL x
    intro z
    obtain ⟨y, hy⟩ :=
      GroupScheme.Tate.PrimeAdic.exists_map_eq_natCast_smul T p (groupHom lam) N ψ hψ z
    apply PrimeAdicSeparation.eq_zero_of_smul_eq_zero
      (TateTwist.eq_zero_of_prime_smul_eq_zero Γ(T.left, ⊤) p)
      (Nat.cast_ne_zero.mpr hN.ne' : (N : ℤ_[p]) ≠ 0)
    rw [← map_smul, ← hy]
    exact hx y
  · intro y hy
    apply GroupScheme.Tate.PrimeAdic.eq_zero_of_map_eq_zero T p (groupHom lam) hN hker y
    exact hR _ hy

/-- A nondegenerate integral pullback pairing has nondegenerate rationalization. -/
theorem primeRationalWeilAlongHomBilinearMap_nondegenerate (lam : A ⟶ DA)
    (h : (primeIntegralAlong lam).Nondegenerate) : (primeAlong lam).Nondegenerate :=
  ⟨PrimeAdicSeparation.separatingLeft_of_tmul
      (TateTwist.eq_zero_of_prime_smul_eq_zero Γ(T.left, ⊤) p)
      (fun x y => primeIntegralAlong lam x y) (primeAlong lam)
      (primeRationalWeilAlongHomBilinearMap_tmul preservation composition unitCoherence
        associativity comparison symmetry stability hA geometryA MA evaluationA
        compatibility T p lam) h.1,
    PrimeAdicSeparation.separatingRight_of_tmul
      (TateTwist.eq_zero_of_prime_smul_eq_zero Γ(T.left, ⊤) p)
      (fun x y => primeIntegralAlong lam x y) (primeAlong lam)
      (primeRationalWeilAlongHomBilinearMap_tmul preservation composition unitCoherence
        associativity comparison symmetry stability hA geometryA MA evaluationA
        compatibility T p lam) h.2⟩

/-- Finite-level nondegeneracy at geometric points and divisibility of geometric points
imply nondegeneracy of the rational prime-adic polarization pairing. -/
theorem primeRationalPolarizationWeilNondegeneracyReduction :
    PrimeRationalPolarizationWeilNondegeneracyReductionStatement.{u} := by
  intro finiteLevel divisibility preservation square universality composition unitCoherence associativity comparison
    symmetry stability compatibility S _ A hA geometryA MA evaluationA lam hlam K _ _ s p _ hp
  have hpn : ∀ n : ℕ, ((p ^ n : ℕ) : K) ≠ 0 := fun n => by
    rw [Nat.cast_pow]
    exact pow_ne_zero n hp
  have hlevel := fun n => finiteLevel preservation square universality composition
    unitCoherence associativity comparison symmetry stability compatibility S A hA geometryA
    MA evaluationA K s (p ^ n) (hpn n)
  obtain ⟨N, hN, hker, ψ, hψ⟩ := GroupScheme.IsIsogeny.exists_points_quasiInverse s hlam.1
  apply primeRationalWeilAlongHomBilinearMap_nondegenerate
  apply primeWeilAlongHomBilinearMap_nondegenerate _ _ _ _ _ _ _ hA geometryA MA evaluationA
    compatibility (Over.mk s) p lam _ _ hN hker ψ hψ
  · exact primeWeilBilinearMap_separatingLeft _ _ _ _ _ _ _ hA MA evaluationA compatibility
      (Over.mk s) p (fun n => (hlevel n).1)
      (GroupScheme.Tate.PrimeAdic.evaluation_surjective_of_pow _ _ p
        (divisibility S (dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
          evaluationA stability composition unitCoherence associativity comparison symmetry)
          K s p hp))
  · exact primeWeilBilinearMap_separatingRight _ _ _ _ _ _ _ hA MA evaluationA compatibility
      (Over.mk s) p (fun n => (hlevel n).2)
      (GroupScheme.Tate.PrimeAdic.evaluation_surjective_of_pow _ _ p
        (divisibility S A K s p hp))

end Langlands.AbelianScheme
