import Langlands.Algebra.NumberFieldBrauerTwoTorsion
import Langlands.GroupScheme.Rational.NumberFieldTypeDVectorVertexHasse

/-! # The quaternionic Hasse kernel suffices for classical type D -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace Langlands.GroupScheme

open Quaternionic

/-- The Hasse kernel for the spin cover of a nondegenerate quaternionic quadratic
  form of rank at least four with respect to an orthogonal involution. -/
def NumberFieldQuaternionicSpinHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (D : Type u) [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D] [FiniteDimensional F D],
    Module.finrank F D = 4 → ∀ (σ : FirstKindInvolution F D),
    Module.finrank F σ.symmetricSubspace = 3 →
    ∀ (n : ℕ), 4 ≤ n → ∀ (q : σ.QuadraticForms (Fin n)), σ.IsNondegenerateQuadratic q →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) (π : G ⟶ σ.isometryGroup q),
    σ.IsSpinCover q π →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- The Hasse kernel for a numbered simply connected absolutely almost-simple
  type D group whose star action fixes the nonfork vertices. -/
def NumberFieldClassicalTypeDHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ) (e : d.Vertex ≃ Fin n),
    4 ≤ n → IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b)) →
    (∀ (γ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex),
      (e a).val + 2 < n → d.star γ a = a) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- The involution of the aligned spin presentation forces the division degree to
  be one or two. The scalar spin theorem handles degree one. -/
theorem numberFieldClassicalTypeDHasse_of_quaternionic
    (hquat : NumberFieldQuaternionicSpinHasseStatement.{u}) :
    NumberFieldClassicalTypeDHasseStatement.{u} := by
  intro F _ _ G _ _ d n e hn hsc habs hcart hstar L _ _ _ _ ξ hξ
  obtain ⟨D, _, _, _, _, deg, m, _, hD, hm, σ, hσ, q, hq, _, _, π, hπ⟩ :=
    classicalTypeDSpinPresentation F G d n e hn hsc habs hcart hstar
  let j : D ≃ₐ[F] Dᵐᵒᵖ :=
    { toFun := fun x => MulOpposite.op (σ x)
      invFun := fun x => σ x.unop
      left_inv := σ.apply_apply
      right_inv := fun x => congrArg MulOpposite.op (σ.apply_apply x.unop)
      map_mul' := fun x y => congrArg MulOpposite.op (σ.map_mul x y)
      map_add' := fun x y => congrArg MulOpposite.op (σ.map_add x y)
      commutes' := fun c => congrArg MulOpposite.op (σ.map_algebraMap c) }
  have he : Langlands.CentralSimple.reducedDegree F D = deg := by
    rw [Langlands.CentralSimple.reducedDegree, hD, pow_two, Nat.sqrt_eq]
  have hd := Langlands.Brauer.numberField_division_reducedDegree_eq_one_or_two_of_equiv_opposite F D j
  rw [he] at hd
  rcases hd with rfl | rfl
  · simp only [mul_one] at hm
    subst m
    exact numberFieldSpinCoverHasse_of_finrank_one n (by omega) (by simpa using hD) σ q hq π hπ ξ hξ
  · have hmn : m = n := by omega
    subst m
    exact hquat F D (by simpa using hD) σ (by simpa using hσ) n hn q hq G π hπ L ξ hξ

end Langlands.GroupScheme
