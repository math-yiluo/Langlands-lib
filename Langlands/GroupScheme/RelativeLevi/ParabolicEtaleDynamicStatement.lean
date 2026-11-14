import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.Dynamic.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Etale-local dynamic presentations of relative parabolic subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A relative parabolic subgroup of a reductive group scheme has, near every
base point in the etale topology, an actual dynamic presentation. This is the
consequence of Conrad (2014), Proposition 5.2.3, obtained by etale-local
splitting of the maximal torus and then Zariski localization. -/
def RelativeParabolicPointwiseEtaleLocalDynamicStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P : GroupScheme S) (i : P ⟶ G) (s : S),
    IsReductive G → IsRelativeParabolicSubgroup i →
      ∃ (T : Scheme.{u}) (f : T ⟶ S), Etale f ∧
        (∃ t : T, f.base t = s) ∧
        ∃ χ : (Gm T).toGrp ⟶ (GroupScheme.baseChange f).obj G,
          (Dynamic.parabolic χ).IsRepresentedBy ((GroupScheme.baseChange f).map i)

end Langlands.GroupScheme
