import Langlands.GroupScheme.Rational.TorusWeightPrimitive
import Langlands.GroupScheme.VectorGroupQuotient

/-! # Vector group quotients of cyclic weight subgroups -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.Corepresented

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)

/-- Polynomial evaluation stays bijective after lifting the index type of the second block of
variables to another universe. -/
theorem aeval_sum_elim_ulift_bijective {C : Type u} [CommRing C] [Algebra k C] {N : ℕ}
    {ι : Type} {y : Fin N → C} {z : ι → C}
    (h : Function.Bijective (MvPolynomial.aeval (Sum.elim y z) :
      MvPolynomial (Fin N ⊕ ι) k →ₐ[k] C)) :
    Function.Bijective (MvPolynomial.aeval (Sum.elim y (z ∘ ULift.down)) :
      MvPolynomial (Fin N ⊕ ULift.{u} ι) k →ₐ[k] C) := by
  let E : Fin N ⊕ ULift.{u} ι ≃ Fin N ⊕ ι := Equiv.sumCongr (Equiv.refl _) Equiv.ulift
  have hE : Sum.elim y (z ∘ ULift.down) = Sum.elim y z ∘ E := by
    funext j
    rcases j with j | j <;> rfl
  have : (MvPolynomial.aeval (Sum.elim y (z ∘ ULift.down)) :
      MvPolynomial (Fin N ⊕ ULift.{u} ι) k →ₐ[k] C) =
        (MvPolynomial.aeval (Sum.elim y z)).comp (MvPolynomial.renameEquiv k E).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.renameEquiv, hE]
  rw [this, AlgHom.coe_comp]
  exact h.comp (MvPolynomial.renameEquiv k E).bijective

/-- The `r`-th cyclic weight subgroup maps to a vector group by its primitive coordinates of
weight `r • a`, as a represented fppf quotient by the next cyclic weight subgroup. -/
theorem exists_isFppfQuotient_cyclicTail [Algebra.FormallySmooth k B] [Algebra.FiniteType k B]
    {a : I → ℤ} (ha : a ≠ 0) {r : ℕ} (hr : 0 < r) :
    ∃ (N : ℕ) (y : Fin N → B ⧸ weightIdeal e σ (cyclicTail a r))
      (hy : VectorGroup.IsPrimitiveFamily (weightCorep e σ (cyclicTail a r)) y),
      (∀ i, IsHomogeneous (weightCorep e σ (cyclicTail a r))
        (weightAction e σ (cyclicTail a r)) (r • a) (y i)) ∧
      ∀ M : SubgroupFunctor (cutGroupScheme (isCutOutBy_weightIdeal e σ (cyclicTail a r))),
        (∀ (T : Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
          (x : T ⟶ (cutGroupScheme (isCutOutBy_weightIdeal e σ (cyclicTail a r))).X),
          x ∈ M.carrier T ↔
            (pointsEquiv (cutFunctor (isCutOutBy_weightIdeal e σ (cyclicTail a r)))
              (weightCorep e σ (cyclicTail a r)) T x).1 ∈
                weightSubgroup e σ (cyclicTail a (r + 1)) _) →
        RelativeRoot.IsFppfQuotient M (VectorGroup.quotientMap hy) := by
  obtain ⟨N, y, ι, hι, z, hyh, hprim, hker, hbij⟩ := exists_primitive_coordinates e σ ha hr
  have hy : VectorGroup.IsPrimitiveFamily (weightCorep e σ (cyclicTail a r)) y :=
    fun A x x' i => hprim x x' i
  refine ⟨N, y, hy, hyh, fun M hM => ?_⟩
  have : Finite (ULift.{u} ι) := Finite.of_equiv ι Equiv.ulift.symm
  exact VectorGroup.isFppfQuotient_quotientMap hy (z := z ∘ ULift.down)
    (aeval_sum_elim_ulift_bijective hbij) M fun T x => (hM T x).trans (hker _).symm

end Langlands.GroupScheme.Corepresented
