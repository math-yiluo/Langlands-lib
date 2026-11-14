import Langlands.GroupScheme.Torus.ExponentCocharacters
import Langlands.GroupScheme.Reductive.RootDatum
import Mathlib.LinearAlgebra.RootSystem.Hom

/-! # Actual fixed-exponent transport through coordinate torus homomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.splitTorus

variable {I I' : Type u} [Fintype I] [Fintype I']

open Classical in
/-- The integer coordinate transpose of a supplied character-lattice map. -/
def exponentPushforward (f : (I' → ℤ) →ₗ[ℤ] (I → ℤ)) (n : I → ℤ) : I' → ℤ :=
  fun j => ∑ i, f (Pi.single j 1) i * n i

private theorem prod_zpow_eq_zpow_sum {A : Type*} [CommGroup A]
    (z : A) (v : I → ℤ) :
    (∏ j, z ^ v j) = z ^ (∑ j, v j) := by
  classical
  have h (s : Finset I) : (∏ j ∈ s, z ^ v j) = z ^ (∑ j ∈ s, v j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp only [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  exact h Finset.univ

/-- An all-test character formula determines the actual transport of every
fixed-exponent cocharacter over an arbitrary base scheme. -/
theorem groupHom_exponentCocharacter_comp
    {S : Scheme.{u}} (τ : splitTorus S I ⟶ splitTorus S I')
    (f : (I' → ℤ) →ₗ[ℤ] (I → ℤ))
    (hτ : ∀ (U : Over S) (x : U ⟶ (splitTorus S I).X) (m : I' → ℤ),
      ∏ j, pointsEquiv I' U (x ≫ τ.hom.hom) j ^ m j =
        ∏ i, pointsEquiv I U x i ^ f m i)
    (n : I → ℤ) :
    CommGroupScheme.groupHom (exponentCocharacter S I n) ≫ τ =
      CommGroupScheme.groupHom (exponentCocharacter S I' (exponentPushforward f n)) := by
  classical
  apply Langlands.GroupScheme.hom_ext_points
  intro U x
  apply (pointsEquiv I' U).injective
  funext j
  have h := hτ U (x ≫ (CommGroupScheme.groupHom (exponentCocharacter S I n)).hom.hom)
    (Pi.single j 1)
  simp only [pointsEquiv_exponentCocharacter, ← zpow_mul] at h
  rw [prod_zpow_eq_zpow_sum] at h
  change pointsEquiv I' U
      ((x ≫ (CommGroupScheme.groupHom (exponentCocharacter S I n)).hom.hom) ≫
        τ.hom.hom) j =
    pointsEquiv I' U
      (x ≫ (CommGroupScheme.groupHom
        (exponentCocharacter S I' (exponentPushforward f n))).hom.hom) j
  rw [pointsEquiv_exponentCocharacter]
  simpa [Pi.single_apply, exponentPushforward, mul_comm] using h

section RootDatum

variable {J J' : Type u}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}

/-- With standard coordinate pairings, the actual exponent pushforward is
the root-datum equivalence's contravariant coweight map. -/
theorem exponentPushforward_eq_coweightMap (e : RootPairing.Equiv Q P)
    (hP : ∀ m n, P.toLinearMap m n = ∑ i, m i * n i)
    (hQ : ∀ m n, Q.toLinearMap m n = ∑ j, m j * n j)
    (n : I → ℤ) : exponentPushforward e.weightMap n = e.coweightMap n := by
  classical
  funext j
  have h := e.toLinearMap_weightEquiv (Pi.single j 1) n
  rw [RootPairing.Equiv.weightEquiv_apply, RootPairing.Equiv.coweightEquiv_apply,
    hP, hQ] at h
  simpa [exponentPushforward, Pi.single_apply] using h

end RootDatum

end Langlands.GroupScheme.splitTorus
