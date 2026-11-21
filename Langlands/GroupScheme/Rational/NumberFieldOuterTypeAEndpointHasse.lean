import Langlands.GroupScheme.Rational.NumberFieldHermitianHasse
import Langlands.GroupScheme.SimplyConnected.OuterTypeAHermitianPresentationProof
import Langlands.GroupScheme.Examples.HermitianMatrixPresentationFromPoints

/-! # The Hasse kernel in outer type A with distinguished endpoints -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The localization kernel for numbered outer type-A groups with both ends distinguished. -/
def NumberFieldOuterTypeAEndpointHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ) (e : d.Vertex ≃ Fin n),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b)) →
    d.StarImagePair e Fin.revPerm →
    (∀ a, ((e a).val = 0 ∨ (e a).val + 1 = n) → a ∈ d.distinguishedVertices) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- The endpoint presentation yields the actual Hermitian matrix Hasse calculation. -/
theorem numberFieldOuterTypeAEndpointHasse : NumberFieldOuterTypeAEndpointHasseStatement.{u} := by
  intro F _ _ G _ _ d n e hsc habs hcart hstar hend L _ _ _ _ ξ hξ
  obtain ⟨E, _, _, _, _, _, J, ρ, _, _, hJ, hdet, hinj, himage, hnat, _, _⟩ :=
    outerTypeAHermitianPresentation F G d n e hsc habs hcart hstar hend
  let H : HermitianMatrix.Form (SU3Root.fieldInvolution F E) (Fin (n + 1)) :=
    ⟨Matrix.GeneralLinearGroup.mk'' J hdet, hJ⟩
  let p := HermitianMatrix.SchemeModel.Presentation.ofMatrixPoints F E H G ρ hinj himage hnat
  exact HermitianMatrix.numberFieldHermitianHasse F E (n + 1) (Nat.zero_lt_succ n) H G p L ξ hξ

end Langlands.GroupScheme
