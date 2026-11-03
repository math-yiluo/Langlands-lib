import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.SubgroupConjugacy

/-! # Rational conjugacy of Levis of a parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Two supplied rational Levis of a rational parabolic are conjugate by a
unique rational point of any specified geometric unipotent radical. -/
def RationalLeviConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
      IsParabolicSubgroup j →
      ∀ (L L' : GroupScheme (Spec (CommRingCat.of k))) (l : L ⟶ P) (l' : L' ⟶ P),
        IsRationalLeviSubgroup l → IsRationalLeviSubgroup l' →
        ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (r : U ⟶ P),
          LeviSubgroup.IsGeometricUnipotentRadical r →
          ∃! q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X,
            ∃ e : L ≅ L',
              l ≫ (P.innerIso (q ≫ r.hom.hom)).hom = e.hom ≫ l'

end Langlands.GroupScheme
