import Langlands.GroupScheme.UnipotentMatrixCriterion.Coordinates
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Fixed vectors for the relative spectrum of a Hopf algebra -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.UnipotentMatrixCriterion

section Corepresentation

variable {R : CommRingCat.{u}} (A : CommHopfAlgCat.{u} R)

/-- The cogroup object of algebras attached to the Hopf algebra `A`. -/
abbrev hopfCogroup : Grp (CommAlgCat.{u} R)ᵒᵖ :=
  ((commHopfAlgCatEquivCogrpCommAlgCat R).functor.obj A).unop

/-- The group-valued functor of algebra points of `A`, with the convolution product. -/
abbrev hopfPointsFunctor : CommAlgCat.{u} R ⥤ GrpCat.{u} :=
  opOp (CommAlgCat.{u} R) ⋙ yonedaGrp.obj (hopfCogroup A)

/-- The point functor of `A` is corepresented by `A` itself. -/
def hopfCorepresentableBy :
    (hopfPointsFunctor A ⋙ forget GrpCat).CorepresentableBy (CommAlgCat.of R A) where
  homEquiv :=
    { toFun := fun f => f.op
      invFun := fun x => x.unop
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  homEquiv_comp _ _ := rfl

/-- The corepresented cogroup is the cogroup of `A`. -/
def hopfCogroupIso :
    Corepresented.cogroup (hopfPointsFunctor A) (hopfCorepresentableBy A) ≅ hopfCogroup A :=
  yonedaGrpFullyFaithful.preimageIso
    (Corepresented.pointsIso _ (hopfCorepresentableBy A) ≪≫
      NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))

/-- The corepresented group scheme is the spectrum of `A`. -/
def hopfGroupSchemeIso :
    Corepresented.groupScheme (hopfPointsFunctor A) (hopfCorepresentableBy A) ≅
      (hopfSpec R).obj (op A) :=
  (algSpec R).mapGrp.mapIso (hopfCogroupIso A)

/-- The comultiplication of the corepresentation is the comultiplication of `A`. -/
theorem comulL_hopf (a : A) :
    Corepresented.LinearEmbedding.comulL (hopfCorepresentableBy A) a =
      Coalgebra.comul (R := R) a := by
  have key : Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A)
      Algebra.TensorProduct.includeRight (fun _ _ => .all _ _) (Bialgebra.comulAlgHom R A a) =
        Coalgebra.comul (R := R) a := by
    rw [Algebra.TensorProduct.lift_includeLeft_includeRight]
    rfl
  exact key

/-- The counit of the corepresentation is the counit of `A`. -/
theorem counitL_hopf (a : A) :
    Corepresented.LinearEmbedding.counitL (hopfCorepresentableBy A) a =
      Coalgebra.counit (R := R) a := by
  rfl

end Corepresentation

section Field

variable {k : Type u} [Field k] (A : CommHopfAlgCat.{u} (CommRingCat.of k))

/-- Over a field, unipotence of `Spec A` gives a nonzero fixed vector for every square matrix of
coefficients `a` with `Δ(aᵢⱼ) = ∑ₗ aᵢₗ ⊗ aₗⱼ` and `ε(aᵢⱼ) = δᵢⱼ`. -/
theorem exists_fixedVector_of_isUnipotent
    (hU : IsUnipotent ((hopfSpec (CommRingCat.of k)).obj (op A)))
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (a : Matrix n n A)
    (hmul : ∀ i j, Coalgebra.comul (R := k) (a i j) = ∑ l, a i l ⊗ₜ[k] a l j)
    (hone : ∀ i j, Coalgebra.counit (R := k) (a i j) = (1 : Matrix n n k) i j) :
    ∃ v : n → k, v ≠ 0 ∧ ∀ i, ∑ j, v j • a i j = v i • (1 : A) := by
  have hU' : IsUnipotent
      (Corepresented.groupScheme (hopfPointsFunctor A) (hopfCorepresentableBy A)) :=
    IsUnipotent.of_iso (hopfGroupSchemeIso A) hU
  have hmul' : ∀ i j, Corepresented.LinearEmbedding.comulL (hopfCorepresentableBy A) (a i j) =
      ∑ l, a i l ⊗ₜ[CommRingCat.of k] a l j := fun i j => (comulL_hopf A _).trans (hmul i j)
  have hone' : ∀ i j, Corepresented.LinearEmbedding.counitL (hopfCorepresentableBy A) (a i j) =
      (1 : Matrix n n (CommRingCat.of k)) i j := fun i j => (counitL_hopf A _).trans (hone i j)
  obtain ⟨v, hv, hfix⟩ := hU' n (Corepresented.groupSchemeMap (hopfCorepresentableBy A)
    (GeneralLinear.corepresentableBy n (CommRingCat.of k))
    (Corepresented.LinearEmbedding.toGL (hopfCorepresentableBy A) a hmul' hone'))
  refine ⟨v, hv, ?_⟩
  have h := (isFixedVector_iff (hopfCorepresentableBy A) _ v).1 hfix
  rw [coefficientMatrix_toGL] at h
  exact h

end Field

end Langlands.GroupScheme.UnipotentMatrixCriterion
