import Langlands.GroupScheme.Torus.HomFamilyFieldRigidity
import Langlands.GroupScheme.Torus.MultiplicativeTypeCommonSplitting

/-! # Rigidity of multiplicative-type families over a connected algebraic group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomFamily

section Morphism

variable {S : Scheme.{u}} {G Q N : GroupScheme S}

/-- The family of points obtained by evaluating a morphism from the product. -/
def ofMorphism (ψ : G.X ⊗ Q.X ⟶ N.X) (T : Over S)
    (g : T ⟶ G.X) (q : T ⟶ Q.X) : T ⟶ N.X :=
  lift g q ≫ ψ

/-- A product morphism multiplicative in the second point gives a natural homomorphism
family on all scheme tests. -/
theorem isHomFamily_ofMorphism (ψ : G.X ⊗ Q.X ⟶ N.X)
    (hmul : ∀ (T : Over S) (g : T ⟶ G.X) (q q' : T ⟶ Q.X),
      lift g (q * q') ≫ ψ = (lift g q ≫ ψ) * (lift g q' ≫ ψ)) :
    IsHomFamily (ofMorphism ψ) where
  map_mul := hmul
  naturality f g q := by simp only [ofMorphism, ← Category.assoc, comp_lift]

end Morphism

variable {k : Type u} [Field k] {G Q N : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left]

/-- Diagonalizable rigidity implies constancy of natural homomorphism families between
any two groups of multiplicative type, parametrized by a connected algebraic group. -/
theorem eq_one_of_multiplicativeType (hRig : DiagonalizableRigidityStatement.{u})
    (hQ : IsMultiplicativeType Q) (hN : IsMultiplicativeType N)
    {F : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ G.X) → (T ⟶ Q.X) → (T ⟶ N.X)}
    (hF : IsHomFamily F) {T : Over (Spec (CommRingCat.of k))}
    (g : T ⟶ G.X) (q : T ⟶ Q.X) : F T g q = F T 1 q := by
  obtain ⟨K, hK, aK, Λ, Λ', hΛ, hΛ', hFG, hFG', eQ, eN⟩ :=
    hQ.exists_common_splitting hN
  exact eq_one_of_commonSplitting hRig K Λ Λ' eQ eN hF g q

/-- The scheme-morphism formulation: a multiplicative family `G × Q → N` agrees with
its restriction to the identity of the connected algebraic parameter group. -/
theorem lift_eq_one_of_multiplicativeType (hRig : DiagonalizableRigidityStatement.{u})
    (hQ : IsMultiplicativeType Q) (hN : IsMultiplicativeType N)
    (ψ : G.X ⊗ Q.X ⟶ N.X)
    (hmul : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (q q' : T ⟶ Q.X),
      lift g (q * q') ≫ ψ = (lift g q ≫ ψ) * (lift g q' ≫ ψ))
    {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ G.X) (q : T ⟶ Q.X) :
    lift g q ≫ ψ = lift (1 : T ⟶ G.X) q ≫ ψ := by
  exact eq_one_of_multiplicativeType hRig hQ hN (isHomFamily_ofMorphism ψ hmul) g q

end Langlands.GroupScheme.HomFamily
