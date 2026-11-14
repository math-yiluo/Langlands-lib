import Langlands.GroupScheme.RelativeLevi.TorusLeviStatement
import Langlands.GroupScheme.Dynamic.Basic

/-! # Statement: local dynamic presentations along a prescribed maximal torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A relative parabolic containing a prescribed maximal torus is, étale-locally,
the dynamic parabolic of a cocharacter of that same torus. This is the local
presentation used in Conrad (2014), Proposition 5.4.5, from Proposition 5.2.3. -/
def RelativeTorusDynamicPresentationStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P : GroupScheme S) (i : P ⟶ G) (T : CommGroupScheme S)
    (t : T.toGrp ⟶ P),
    IsReductive G → IsRelativeParabolicSubgroup i →
    RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t → IsFibrewiseMaximalTorus t →
      ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
        ∀ a : 𝒰.I₀,
          ∃ nu : (Gm (𝒰.X a)).toGrp ⟶ (GroupScheme.baseChange (𝒰.f a)).obj T.toGrp,
            (Dynamic.parabolic
              (nu ≫ (GroupScheme.baseChange (𝒰.f a)).map t ≫
                (GroupScheme.baseChange (𝒰.f a)).map i)).IsRepresentedBy
              ((GroupScheme.baseChange (𝒰.f a)).map i)

end Langlands.GroupScheme
