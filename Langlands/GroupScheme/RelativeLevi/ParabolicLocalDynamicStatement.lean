import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.Dynamic.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Statement: relative parabolic subgroups are etale-locally dynamic -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The dynamic part of Conrad, Proposition 5.2.3, after etale localization:
every relative parabolic represents the dynamic parabolic of a cocharacter on
an etale cover of the base. No closedness of the original inclusion is assumed. -/
def RelativeParabolicEtaleLocalDynamicStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P : GroupScheme S) (i : P ⟶ G),
    IsReductive G → IsRelativeParabolicSubgroup i →
      ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
        ∀ a : 𝒰.I₀,
          ∃ χ : (Gm (𝒰.X a)).toGrp ⟶ (GroupScheme.baseChange (𝒰.f a)).obj G,
            (Dynamic.parabolic χ).IsRepresentedBy ((GroupScheme.baseChange (𝒰.f a)).map i)

end Langlands.GroupScheme
