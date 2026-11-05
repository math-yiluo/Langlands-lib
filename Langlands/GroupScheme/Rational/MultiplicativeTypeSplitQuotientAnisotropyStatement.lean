import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Rational.AnisotropicTorusFiniteQuotient
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Reductive.Semisimple

/-! # Anisotropy of multiplicative-type quotients by maximal split subtori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- An actual fppf quotient of a finite-type multiplicative-type group by a
maximal split subtorus is a finite schematic extension of an anisotropic torus. -/
def MultiplicativeTypeSplitQuotientAnisotropyStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (Z : GroupScheme (Spec (CommRingCat.of k))), IsMultiplicativeType Z →
    ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (j : A.toGrp ⟶ Z),
      IsMaximalSplitTorus j →
      ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (q : Z ⟶ C),
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q →
        HasAnisotropicTorusFiniteQuotient C

variable {k : Type u} [Field k]
variable {M Z C : GroupScheme (Spec (CommRingCat.of k))}
variable {A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A split component becomes a maximal split subtorus in every actual
representative of the full scheme-theoretic center through which it factors. -/
theorem IsSplitComponent.isMaximalSplitTorus_centerFactor
    {i : A.toGrp ⟶ M} (hi : IsSplitComponent i)
    {z : Z ⟶ M} (hz : IsSchemeTheoreticCenter z)
    {j : A.toGrp ⟶ Z} (hfactor : j ≫ z = i) :
    IsMaximalSplitTorus j := by
  refine ⟨⟨hi.1.1.1, IsClosedSubgroup.of_comp hz.1 ?_⟩, ?_⟩
  · rw [hfactor]
    exact hi.1.1.2
  · intro A' j' hj' f hf
    apply hi.2 A' (j' ≫ z)
      ⟨⟨hj'.1, hj'.2.comp hz.1⟩, hz.isCentral.comp j'⟩ f
    calc
      f ≫ (j' ≫ z) = (f ≫ j') ≫ z := (Category.assoc _ _ _).symm
      _ = j ≫ z := by rw [hf]
      _ = i := hfactor

/-- Apply the structural target to the literal full-center quotient.
The structural anisotropy assertion remains an explicit hypothesis. -/
theorem MultiplicativeTypeSplitQuotientAnisotropyStatement.centerQuotient
    (hstruct : MultiplicativeTypeSplitQuotientAnisotropyStatement.{u})
    {z : Z ⟶ M} (hz : IsSchemeTheoreticCenter z)
    (hZ : IsMultiplicativeType Z)
    {i : A.toGrp ⟶ M} (hi : IsSplitComponent i)
    {j : A.toGrp ⟶ Z} (hfactor : j ≫ z = i)
    (q : Z ⟶ C)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q) :
    HasAnisotropicTorusFiniteQuotient C :=
  hstruct k Z hZ A j (hi.isMaximalSplitTorus_centerFactor hz hfactor) C q hq

end Langlands.GroupScheme
