import Langlands.AbelianScheme.Tate.WeilRationalPolarizationNondegeneracyStatement
import Langlands.AbelianScheme.Tate.WeilPrimeRationalPolarizationNondegeneracyProof
import Langlands.AbelianScheme.Tate.RestrictedProductProof

/-! # Nondegeneracy through the actual rational prime coordinates -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.GroupScheme.Tate.PrimeComparison

open Langlands.TateTwist.Divisibility (AwayPrime)
attribute [local instance] primeFact

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

private lemma full_eq_zero_of_coordinates (x : RationalFull G T)
    (hx : ∀ p : Nat.Primes, rationalFullToPrime G T (p : ℕ) x = 0) : x = 0 := by
  obtain ⟨e, he⟩ := rationalRestrictedProductComparison G T
  apply e.injective
  apply RestrictedProduct.ext
  intro p
  rw [he, he, hx p, map_zero]

private lemma away_eq_zero_of_coordinates (m : ℕ) (x : RationalAway G T m)
    (hx : ∀ p : AwayPrime m,
      rationalAwayToPrime G T (p.val : ℕ) m p.property x = 0) : x = 0 := by
  obtain ⟨e, he⟩ := rationalAwayRestrictedProductComparison G T m
  apply e.injective
  apply RestrictedProduct.ext
  intro p
  rw [he, he, hx p, map_zero]

private lemma full_coordinate_surjective (p : ℕ) [Fact p.Prime] :
    Function.Surjective (rationalFullToPrime G T p) := by
  classical
  obtain ⟨e, he⟩ := rationalRestrictedProductComparison G T
  intro y
  let pi : Nat.Primes := ⟨p, Fact.out⟩
  let z : RationalRestrictedProduct G T :=
    RestrictedProduct.single
      (fun q : Nat.Primes => (PrimeAdic.integralImage G T (q : ℕ)).toAddSubgroup) pi y
  refine ⟨e.symm z, ?_⟩
  rw [← he _ pi, e.apply_symm_apply]
  exact RestrictedProduct.single_eq_same _ _ _

private lemma away_coordinate_surjective (p : ℕ) [Fact p.Prime]
    (m : ℕ) (hp : Nat.Coprime p m) :
    Function.Surjective (rationalAwayToPrime G T p m hp) := by
  classical
  obtain ⟨e, he⟩ := rationalAwayRestrictedProductComparison G T m
  intro y
  let pi : AwayPrime m := ⟨⟨p, Fact.out⟩, hp⟩
  let z : RationalAwayRestrictedProduct G T m :=
    RestrictedProduct.single
      (fun q : AwayPrime m =>
        (PrimeAdic.integralImage G T (q.val : ℕ)).toAddSubgroup) pi y
  refine ⟨e.symm z, ?_⟩
  rw [← he _ pi, e.apply_symm_apply]
  exact RestrictedProduct.single_eq_same _ _ _

end Langlands.GroupScheme.Tate.PrimeComparison

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
  (compatibility : RelativeFiniteWeilTransitionStatement.{u}) (T : Over S)

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "primeAlong" => primeRationalWeilAlongHomBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility T
local notation "rationalAlong" => rationalWeilAlongHomBilinearMap preservation composition
  unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
  compatibility T

private lemma rationalFullWeil_nondegenerate_of_prime (lam : A ⟶ DA)
    (hPrime : ∀ (p : ℕ) [Fact p.Prime], (primeAlong p lam).Nondegenerate) :
    (rationalAlong lam (fun _ => True)).Nondegenerate := by
  constructor
  · intro x hx
    apply GroupScheme.Tate.PrimeComparison.full_eq_zero_of_coordinates A.toGrp T x
    intro p
    let : Fact (p : ℕ).Prime := ⟨p.property⟩
    apply (hPrime (p : ℕ)).1
    intro y
    obtain ⟨z, rfl⟩ :=
      GroupScheme.Tate.PrimeComparison.full_coordinate_surjective A.toGrp T (p : ℕ) y
    rw [← rationalFullToPrime_rationalWeilAlongHomBilinearMap preservation composition
      unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
      compatibility T (p : ℕ) lam, hx z, map_zero]
  · intro y hy
    apply GroupScheme.Tate.PrimeComparison.full_eq_zero_of_coordinates A.toGrp T y
    intro p
    let : Fact (p : ℕ).Prime := ⟨p.property⟩
    apply (hPrime (p : ℕ)).2
    intro x
    obtain ⟨z, rfl⟩ :=
      GroupScheme.Tate.PrimeComparison.full_coordinate_surjective A.toGrp T (p : ℕ) x
    rw [← rationalFullToPrime_rationalWeilAlongHomBilinearMap preservation composition
      unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
      compatibility T (p : ℕ) lam, hy z, map_zero]

private lemma rationalAwayWeil_nondegenerate_of_prime (lam : A ⟶ DA)
    (hPrime : ∀ (p : ℕ) [Fact p.Prime], (primeAlong p lam).Nondegenerate) (m : ℕ) :
    (rationalAlong lam (fun n => Nat.Coprime n m)).Nondegenerate := by
  constructor
  · intro x hx
    apply GroupScheme.Tate.PrimeComparison.away_eq_zero_of_coordinates A.toGrp T m x
    intro p
    let : Fact (p.val : ℕ).Prime := ⟨p.val.property⟩
    apply (hPrime (p.val : ℕ)).1
    intro y
    obtain ⟨z, rfl⟩ :=
      GroupScheme.Tate.PrimeComparison.away_coordinate_surjective A.toGrp T
        (p.val : ℕ) m p.property y
    rw [← rationalAwayToPrime_rationalWeilAlongHomBilinearMap preservation composition
      unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
      compatibility T (p.val : ℕ) lam m p.property, hx z, map_zero]
  · intro y hy
    apply GroupScheme.Tate.PrimeComparison.away_eq_zero_of_coordinates A.toGrp T m y
    intro p
    let : Fact (p.val : ℕ).Prime := ⟨p.val.property⟩
    apply (hPrime (p.val : ℕ)).2
    intro x
    obtain ⟨z, rfl⟩ :=
      GroupScheme.Tate.PrimeComparison.away_coordinate_surjective A.toGrp T
        (p.val : ℕ) m p.property x
    rw [← rationalAwayToPrime_rationalWeilAlongHomBilinearMap preservation composition
      unitCoherence associativity comparison symmetry stability hA geometryA MA evaluationA
      compatibility T (p.val : ℕ) lam m p.property, hy z, map_zero]

/-- Nondegeneracy of the actual prime pairings implies all four full and away clauses. -/
theorem rationalPolarizationWeilNondegeneracy_of_prime
    (primeNondegeneracy : PrimeRationalPolarizationWeilNondegeneracyStatement.{u}) :
    RationalPolarizationWeilNondegeneracyStatement.{u} := by
  intro preservation square universality composition unitCoherence associativity comparison
    symmetry stability compatibility S _ A hA geometryA MA evaluationA lam hLam K _ _ _ s
  have hPrime : ∀ (p : ℕ) [Fact p.Prime],
      (primeRationalWeilAlongHomBilinearMap preservation composition unitCoherence
        associativity comparison symmetry stability hA geometryA MA evaluationA
        compatibility (Over.mk s) p lam).Nondegenerate := by
    intro p hp
    exact primeNondegeneracy preservation square universality composition unitCoherence
      associativity comparison symmetry stability compatibility S A hA geometryA MA evaluationA
      lam hLam K s p (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hFull := rationalFullWeil_nondegenerate_of_prime preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
    (Over.mk s) lam hPrime
  have hAway := rationalAwayWeil_nondegenerate_of_prime preservation composition unitCoherence
    associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
    (Over.mk s) lam hPrime
  refine ⟨hFull, hAway, ?_, ?_⟩
  · intro h
    let := GroupScheme.Tate.finiteAdeleModule A.toGrp (Over.mk s) (fun _ => True) h
    let := TateTwist.Divisibility.finiteAdeleModule
      Γ((Over.mk s).left, ⊤) (fun _ => True) h
    simpa only [LinearMap.Nondegenerate, LinearMap.SeparatingLeft, LinearMap.SeparatingRight,
      adelicWeilAlongHomBilinearMap_apply] using hFull
  · intro h m hAwayComparison
    let := GroupScheme.Tate.primeToFiniteAdeleModule A.toGrp (Over.mk s) hAwayComparison
    let := TateTwist.Divisibility.primeToFiniteAdeleModule
      Γ((Over.mk s).left, ⊤) hAwayComparison
    simpa only [LinearMap.Nondegenerate, LinearMap.SeparatingLeft, LinearMap.SeparatingRight,
      awayAdelicWeilAlongHomBilinearMap_apply] using hAway m

/-- Full and away rational and adelic polarization Weil pairings are nondegenerate
at every algebraically closed characteristic-zero geometric point. -/
theorem rationalPolarizationWeilNondegeneracy :
    RationalPolarizationWeilNondegeneracyStatement.{u} :=
  rationalPolarizationWeilNondegeneracy_of_prime primeRationalPolarizationWeilNondegeneracy

end Langlands.AbelianScheme
