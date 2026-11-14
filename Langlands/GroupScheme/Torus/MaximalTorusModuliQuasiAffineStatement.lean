import Langlands.GroupScheme.Torus.MaximalTorusSchemeStatement

/-! # Quasi-affineness of supplied universal maximal-torus moduli -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The universal parameter scheme of maximal tori in a reductive group is
quasi-affine over its base, when such a universal family is supplied. -/
def MaximalTorusModuliQuasiAffineStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    ∀ (M : Over S) (K : CommGroupScheme M.left)
      (j : K.toGrp ⟶ (GroupScheme.baseChange M.hom).obj G),
      RelativeTorus.IsTorus K.toGrp → IsClosedSubgroup j → IsFibrewiseMaximalTorus j →
      (∀ (T : Over S) (T' : CommGroupScheme T.left)
          (t : T'.toGrp ⟶ (GroupScheme.baseChange T.hom).obj G),
        RelativeTorus.IsTorus T'.toGrp → IsClosedSubgroup t → IsFibrewiseMaximalTorus t →
          ∃! a : T ⟶ M, TorusSubgroupModuli.evaluate j a = SubgroupFunctor.range t) →
      ∀ V : S.affineOpens, (M.hom ⁻¹ᵁ (V : S.Opens)).toScheme.IsQuasiAffine

end Langlands.GroupScheme
