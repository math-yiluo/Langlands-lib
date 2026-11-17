import Langlands.GroupScheme.HomScheme.AdicConjugatorSteps
import Langlands.GroupScheme.Torus.MultiplicativeTypeAdicHomComparisonStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeAdicLiftStatement

/-! # Reduction of adic lifting to infinitesimal lifting and adic Hom comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AdicAffinePoints

namespace Langlands.GroupScheme

namespace RelativeMultiplicativeType

/-- An étale surjection is a singleton fppf cover of the base. -/
def etaleSurjectiveFppfCover {S S' : Scheme.{u}} (p : S' ⟶ S) [Etale p] [Surjective p] :
    Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S :=
  Scheme.Cover.mkOfCovers PUnit (fun _ ↦ S') (fun _ ↦ p)
    (fun x ↦ by
      obtain ⟨y, hy⟩ := (inferInstance : Surjective p).surj x
      exact ⟨PUnit.unit, y, hy⟩)
    (fun _ ↦ ⟨inferInstance, inferInstance⟩)

/-- Diagonalizability on an étale surjective cover implies the relative multiplicative-type
predicate used by infinitesimal lifting. -/
theorem isMultiplicativeType_of_etale_surjective
    {S S' : Scheme.{u}} (p : S' ⟶ S) [Etale p] [Surjective p]
    (H : GroupScheme S) (hH : IsDiagonalizable ((baseChange p).obj H)) :
    IsMultiplicativeType H :=
  ⟨etaleSurjectiveFppfCover p, fun _ ↦ hH⟩

end RelativeMultiplicativeType

/-- SGA 3, Exposé IX, Corollaire 7.3 follows from its infinitesimal theorem and the full
adic Hom comparison. Both mathematical inputs remain explicit. -/
theorem multiplicativeTypeAdicLift_of_infinitesimal_of_homComparison
    (hInf : MultiplicativeTypeInfinitesimalLiftStatement.{u})
    (hComp : MultiplicativeTypeAdicHomComparisonStatement.{u}) :
    MultiplicativeTypeAdicLiftStatement.{u} := by
  intro A _ _ I _ H G _ _ hsplit
  have hH : RelativeMultiplicativeType.IsMultiplicativeType H := by
    obtain ⟨S', p, -, hp, hsurj, hdiag⟩ := hsplit
    let : Etale p := hp
    let : Surjective p := hsurj
    exact RelativeMultiplicativeType.isMultiplicativeType_of_etale_surjective p H hdiag
  have hbij := hComp A I H G hsplit
  let C (J : Ideal A) : Prop :=
    let r := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
    Function.Surjective ((baseChange r).map (X := H) (Y := G)) ∧
      ∀ f f' : H ⟶ G, (baseChange r).map f = (baseChange r).map f' →
        ∃ q : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ G.X,
          G.constantPoint q (Over.mk r) = 1 ∧ f' = f ≫ (G.innerIso q).hom
  have hC : C (I ^ (0 + 1)) :=
    ⟨HomScheme.Adic.first_quotient_surjective_of_infinitesimal I hInf H G hH hbij.surjective,
      HomScheme.Adic.conjugacy_of_infinitesimal_and_injective I hInf H G hH hbij.injective⟩
  exact (show I ^ (0 + 1) = I by simp) ▸ hC

end Langlands.GroupScheme
