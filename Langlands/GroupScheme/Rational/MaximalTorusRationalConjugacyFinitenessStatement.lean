import Langlands.GroupScheme.Rational.SubgroupConjugacy
import Langlands.GroupScheme.Torus.Maximal
import Mathlib.NumberTheory.LocalField.Basic

/-! # Finiteness of rational conjugacy classes of maximal tori -/

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

universe u

/-- A finite family of embedded maximal tori meets every rational conjugacy
class of embedded maximal tori in `G`. -/
def HasFiniteMaximalTorusConjugacyClasses {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∃ (n : ℕ) (T : Fin n → CommGroupScheme (Spec (CommRingCat.of k)))
      (j : ∀ a, (T a).toGrp ⟶ G),
    (∀ a, IsMaximalTorus (j a)) ∧
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
        IsMaximalTorus i → ∃ a, SubgroupConjugate i (j a)

/-- A connected reductive group over a characteristic-zero nonarchimedean
local field has finitely many rational conjugacy classes of maximal tori. -/
def MaximalTorusRationalConjugacyFinitenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (G : GroupScheme (Spec (CommRingCat.of F))),
    IsConnectedReductive G → HasFiniteMaximalTorusConjugacyClasses G

end Langlands.GroupScheme
