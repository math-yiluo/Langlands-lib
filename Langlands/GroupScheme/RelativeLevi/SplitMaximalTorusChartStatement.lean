import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.Torus.Maximal
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Statement: affine étale split maximal-torus charts for a relative parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every point of a relative parabolic in a reductive group has an affine étale
chart on which the parabolic contains a standard split torus that is maximal in
every geometric fibre of the ambient reductive group. This is the maximal-torus
part of Conrad, *Reductive group schemes* (2014), Proposition 5.2.3, followed by
étale splitting and restriction to an affine neighbourhood. -/
def RelativeParabolicSplitMaximalTorusChartStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P : GroupScheme S) (i : P ⟶ G),
    IsReductive G → IsRelativeParabolicSubgroup i → ∀ s : S,
      ∃ (r : Type u) (_ : CommRing r)
        (f : Spec (CommRingCat.of r) ⟶ S), Etale f ∧
        ∃ t : Spec (CommRingCat.of r), f t = s ∧
          ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
            (j : splitTorus (Spec (CommRingCat.of r)) I ⟶ (baseChange f).obj P),
            IsClosedSubgroup j ∧
              ∀ x : Spec (CommRingCat.of r),
                IsMaximalTorus (T := splitTorus.commGroupScheme
                  (Spec (CommRingCat.of
                    (AlgebraicClosure ((Spec (CommRingCat.of r)).residueField x)))) I)
                  ((splitTorus.baseChangeIso (geometricPoint _ x) I).inv ≫
                    (baseChange (geometricPoint _ x)).map (j ≫ (baseChange f).map i))

end Langlands.GroupScheme
