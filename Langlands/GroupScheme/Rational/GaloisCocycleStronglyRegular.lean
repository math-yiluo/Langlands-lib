import Langlands.GroupScheme.GaloisCocycle
import Langlands.GroupScheme.Rational.FiniteGaloisCocycleFactorization
import Langlands.GroupScheme.Rational.GaloisToralPointDescent
import Langlands.GroupScheme.Rational.QuadraticToralRepresentatives
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # Quadratic cocycles with a strongly regular Galois value -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A cocycle can be twisted so its value at a given nonidentity automorphism
has a maximal torus as its all-test centralizer over the coefficient field. -/
def GaloisCocycleStronglyRegularValueStatement : Prop :=
  ∀ (K M : Type u) [Field K] [CharZero K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M] [IsAlgClosed M]
    (G : GroupScheme (Spec (CommRingCat.of K))), IsConnectedReductive G →
    ∀ (ξ : Cocycle G (ringTest K M)) (σ : M ≃ₐ[K] M), σ ≠ 1 →
      ∃ (f : ringTest K M ⟶ G.X)
        (T : CommGroupScheme (Spec (CommRingCat.of M)))
        (j : T.toGrp ⟶ (baseChange (algebraBaseMap K M)).obj G),
        IsMaximalTorus j ∧
          SubgroupFunctor.range j =
            ((baseChange (algebraBaseMap K M)).obj G).pointCentralizer
              ((baseChangeBasePointsEquiv (algebraBaseMap K M) G).symm
                (GaloisCocycle.value (ξ.twist f) σ))

set_option backward.isDefEq.respectTransparency false in
/-- A strongly regular nontrivial Galois value yields a toral representative
on a quadratic cover. -/
theorem quadraticToralRepresentatives_of_stronglyRegularValue
    (hreg : GaloisCocycleStronglyRegularValueStatement.{u}) :
    QuadraticToralRepresentativesStatement.{u} := by
  intro K M _ _ _ _ _ _ G hG ξ
  classical
  have hdim := Algebra.IsQuadraticExtension.finrank_eq_two K M
  let : FiniteDimensional K M :=
    FiniteDimensional.of_finrank_pos (by rw [hdim]; decide)
  let : IsGalois K M := inferInstance
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hcard : Nat.card (M ≃ₐ[K] M) = 2 :=
    (IsGalois.card_aut_eq_finrank K M).trans hdim
  obtain ⟨σ, hσ, huniq⟩ := (Nat.card_eq_two_iff' (1 : M ≃ₐ[K] M)).mp hcard
  have hcases (τ : M ≃ₐ[K] M) : τ = 1 ∨ τ = σ := by
    by_cases hτ : τ = 1
    · exact Or.inl hτ
    · exact Or.inr (huniq τ hτ)
  have hσ₂ : σ * σ = 1 := by
    simpa only [hcard, pow_two] using (pow_card_eq_one' (x := σ))
  obtain ⟨f, S, j, hj, hc⟩ := hreg K M G hG ξ σ hσ
  let ξ' := ξ.twist f
  let y := GaloisCocycle.value ξ' σ
  have hval : GaloisCocycle.value ξ' 1 = 1 := by
    rw [GaloisCocycle.value, GaloisCocycle.arrow_one, Cocycle.toFun_self]
  have hnorm := GaloisCocycle.value_mul ξ' σ σ
  rw [hσ₂, hval] at hnorm
  have hy_inv : ringTestMap K σ.toAlgHom ≫ y = y⁻¹ := by
    exact eq_inv_of_mul_eq_one_right hnorm.symm
  obtain ⟨T, i, hi, t, ht⟩ := exists_maximalTorus_factor_of_galois_centralizer y j hj hc
    (fun τ => by
      rcases hcases τ with rfl | rfl
      · exact Or.inl (by rw [show ringTestMap K (1 : M ≃ₐ[K] M).toAlgHom = 𝟙 _
            from ringTestMap_id K M, Category.id_comp])
      · exact Or.inr hy_inv)
  let : Mono i.hom.hom := hi.2.1.mono_overHom
  have hfactor : ∀ τ : M ≃ₐ[K] M, ∃ q : ringTest K M ⟶ T.X,
      q ≫ i.hom.hom = ξ'.toFun (𝟙 _) (ringTestMap K τ.toAlgHom) := by
    intro τ
    rcases hcases τ with rfl | rfl
    · refine ⟨1, ?_⟩
      rw [show ringTestMap K (1 : M ≃ₐ[K] M).toAlgHom = 𝟙 _
        from ringTestMap_id K M, Cocycle.toFun_self, MonObj.one_comp]
    · exact ⟨t, ht⟩
  let htest := fun {Z} a b => Cocycle.factors_of_galois ξ' i hfactor (Z := Z) a b
  let d := ξ'.lift i htest
  refine ⟨T, i, hi, d, Cocycle.Cohomologous.symm ?_⟩
  refine ⟨f, fun a b => ?_⟩
  exact ξ'.lift_toFun i htest a b

end Langlands.GroupScheme
