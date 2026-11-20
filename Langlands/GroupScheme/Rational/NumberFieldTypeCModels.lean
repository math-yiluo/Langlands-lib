import Langlands.Algebra.NumberFieldBrauerTwoTorsion
import Langlands.GroupScheme.Quaternionic.DegreeSplittingIso
import Langlands.GroupScheme.SimplyConnected.TypeCDivisionFormProof

/-! # Split and quaternionic models of simply connected type C over number fields -/

noncomputable section

open AlgebraicGeometry CategoryTheory Matrix
open scoped TensorProduct

universe u

namespace Langlands.GroupScheme

open Quaternionic

private def involutionOppositeEquiv {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
    (σ : FirstKindInvolution F D) : D ≃ₐ[F] Dᵐᵒᵖ where
  toFun x := MulOpposite.op (σ x)
  invFun x := σ x.unop
  left_inv x := σ.apply_apply x
  right_inv x := congrArg MulOpposite.op (σ.apply_apply x.unop)
  map_mul' x y := congrArg MulOpposite.op (σ.map_mul x y)
  map_add' x y := congrArg MulOpposite.op (σ.map_add x y)
  commutes' c := congrArg MulOpposite.op (σ.map_algebraMap c)

private theorem symplecticGroup_finrank_one {F D : Type u} [Field F] [DivisionRing D]
    [Algebra F D] [Algebra.IsCentral F D] [FiniteDimensional F D]
    {r : ℕ} [NeZero (2 * r)] (σ : FirstKindInvolution F D)
    (H : Matrix (Fin (2 * r)) (Fin (2 * r)) D) (hH : σ.IsAntihermitian H) (hunit : IsUnit H)
    (hD : Module.finrank F D = 1) (hσ : Module.finrank F σ.symmetricSubspace = 1) :
    Nonempty (σ.symplecticGroup H ≅ SymplecticMatrix.groupScheme (Fin r) (CommRingCat.of F)) := by
  let e₀ := AlgEquiv.ofBijective (Algebra.ofId F D)
    ((Algebra.finrank_eq_one_iff_bijective_algebraMap (F := F) (E := D)).mp hD)
  let e : F ⊗[F] D ≃ₐ[F] Matrix (Fin 1) (Fin 1) F :=
    (Algebra.TensorProduct.lid F D).trans (e₀.symm.trans (Langlands.Brauer.matrixOneEquiv F).symm)
  have hs : Module.finrank F σ.symmetricSubspace =
      Fintype.card (Fin 1) * (Fintype.card (Fin 1) + 1) / 2 := by simpa using hσ
  obtain ⟨k, P, Q, hPQ, hQP, hJ⟩ := SymplecticMatrix.exists_mul_mul_transpose_eq_J
    (DegreeSplitting.splitGram e σ H) (DegreeSplitting.transpose_splitGram e σ hs hH)
    (DegreeSplitting.splitGram_diag e σ hs hH) (DegreeSplitting.det_splitGram_ne_zero e σ hunit)
  have hkr : k = r := by
    have hc := Quaternionic.card_eq_of_mul_eq_one hPQ hQP
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, mul_one] at hc
    omega
  subst k
  have hbase : scalarBaseMap F F = 𝟙 (Spec (CommRingCat.of F)) := by
    have hring : CommRingCat.ofHom (algebraMap F F) = 𝟙 (CommRingCat.of F) := by
      ext x
      exact Algebra.algebraMap_self_apply x
    exact (congrArg Spec.map hring).trans (Spec.map_id _)
  let ebase : σ.baseChangeSymplecticGroup H (L := F) ≅ σ.symplecticGroup H :=
    eqToIso (congrArg (fun f => (GroupScheme.baseChange f).obj (σ.symplecticGroup H)) hbase) ≪≫
      baseChangeIdIso _
  exact ⟨ebase.symm ≪≫ DegreeSplitting.splittingIso e σ H P Q hPQ hQP hJ⟩

/-- The type `C_r` models over a number field have either a split matrix presentation
or a presentation by an orthogonal involution on a division algebra of dimension four. -/
def NumberFieldTypeCModelsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (r : ℕ)
    (e : d.Vertex ≃ Fin r),
    2 ≤ r → IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.C r (e a) (e b)) →
      Nonempty (G ≅ SymplecticMatrix.groupScheme (Fin r) (CommRingCat.of F)) ∨
        ∃ (_ : NeZero r) (D : Type u) (_ : DivisionRing D) (_ : Algebra F D)
          (_ : Algebra.IsCentral F D) (_ : FiniteDimensional F D),
          Module.finrank F D = 4 ∧
            ∃ σ : FirstKindInvolution F D, Module.finrank F σ.symmetricSubspace = 3 ∧
              ∃ H : Matrix (Fin r) (Fin r) D, σ.IsAntihermitian H ∧ IsUnit H ∧
                Nonempty (G ≅ σ.symplecticGroup H)

/-- An involution implies Brauer two-torsion, so the division degree is one or two.
In degree one the Darboux basis gives the split group over the original field. -/
theorem numberFieldTypeCModels : NumberFieldTypeCModelsStatement.{u} := by
  intro F _ _ G _ _ d r e hr hsc habs hC
  obtain ⟨degree, m, hne, D, _, _, _, _, _, hsize, hdim, σ, hσ, H, hH, hunit, _, ⟨i⟩, _⟩ :=
    typeCDivisionForm F G d r e hr hsc habs hC
  have hdegree : Langlands.CentralSimple.reducedDegree F D = degree := by
    rw [Langlands.CentralSimple.reducedDegree, hdim, pow_two, Nat.sqrt_eq]
  have hsmall := Langlands.Brauer.numberField_division_reducedDegree_eq_one_or_two_of_equiv_opposite
    F D (involutionOppositeEquiv σ)
  rw [hdegree] at hsmall
  clear hdegree
  rcases hsmall with h | h
  · subst degree
    have hm : m = 2 * r := by simpa using hsize
    subst m
    obtain ⟨j⟩ := symplecticGroup_finrank_one σ H hH hunit (by simpa using hdim)
      (by simpa using hσ)
    exact Or.inl ⟨i ≪≫ j⟩
  · subst degree
    have hm : m = r := by omega
    subst m
    exact Or.inr ⟨hne, D, inferInstance, inferInstance, inferInstance, inferInstance,
      hdim, σ, hσ, H, hH, hunit, ⟨i⟩⟩

end Langlands.GroupScheme
