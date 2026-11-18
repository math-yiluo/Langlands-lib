import Langlands.AlgebraicGeometry.IntegerFiniteEtaleSection
import Langlands.AlgebraicGeometry.Picard.ValuationBaseNormality
import Langlands.GroupScheme.Torus.MultiplicativeTypeNormalIsotrivialStatement

/-! # Integer diagonalizability from normal-base isotriviality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeMultiplicativeType

/-- General normal-base isotriviality implies diagonalizability of every
group of multiplicative type over the lifted integer spectrum. -/
def IntegerDiagonalizabilityFromNormalIsotrivialStatement : Prop :=
  Langlands.GroupScheme.MultiplicativeTypeNormalIsotrivialStatement.{u} →
    ∀ (G : GroupScheme (Spec (CommRingCat.of (ULift.{u} ℤ)))),
      IsMultiplicativeType G → IsDiagonalizable G

/-- A diagonalizable pullback along a morphism with a section gives a
diagonalizable group over the original base. -/
theorem IsDiagonalizable.of_section {S S' : Scheme.{u}} {G : GroupScheme S}
    (p : S' ⟶ S) (σ : S ⟶ S') (hσ : σ ≫ p = 𝟙 S)
    (hG : IsDiagonalizable ((GroupScheme.baseChange p).obj G)) :
    IsDiagonalizable G := by
  let e := Descent.pullbackComparison p σ (𝟙 S) hσ G ≪≫ baseChangeIdIso G
  exact IsDiagonalizable.of_iso e.symm (hG.baseChange σ)

/-- Finite étale isotriviality over the integers implies diagonalizability
over the original integer spectrum. -/
theorem isDiagonalizable_of_finiteEtale_integer
    {G : GroupScheme (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    {S' : Scheme.{u}} (p : S' ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)))
    [IsFinite p] [Etale p] [Surjective p]
    (hG : IsDiagonalizable ((GroupScheme.baseChange p).obj G)) :
    IsDiagonalizable G := by
  obtain ⟨σ, hσ⟩ := Langlands.AlgebraicGeometry.exists_section_of_finiteEtale_integer p
  exact hG.of_section p σ hσ

/-- The general normal-base isotriviality statement, when available, implies
that every group of multiplicative type over the integers is diagonalizable. -/
theorem integer_isDiagonalizable_of_normalIsotrivial
    (h : Langlands.GroupScheme.MultiplicativeTypeNormalIsotrivialStatement.{u})
    (G : GroupScheme (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (hG : IsMultiplicativeType G) : IsDiagonalizable G := by
  let : IsDomain (ULift.{u} ℤ) := ULift.ringEquiv.toMulEquiv.isDomain ℤ
  let : IsIntegrallyClosed (ULift.{u} ℤ) :=
    IsIntegrallyClosed.of_equiv (ULift.ringEquiv (R := ℤ)).symm
  obtain ⟨S', p, hfin, hét, hsurj, hdiag⟩ :=
    (h (Spec (CommRingCat.of (ULift.{u} ℤ)))
      (Langlands.AlgebraicGeometry.spec_hasNormalStalks _) G hG).2 inferInstance
  let : IsFinite p := hfin
  let : Etale p := hét
  let : Surjective p := hsurj
  exact isDiagonalizable_of_finiteEtale_integer p hdiag

end Langlands.GroupScheme.RelativeMultiplicativeType
