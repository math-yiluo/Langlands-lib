import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Torus.Relative

/-! # Smooth closed torus normalizers in separated smooth groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The relative-torus case of SGA 3, Exposé XI, Corollary 5.3 bis, without
the affineness hypothesis on the ambient group, as permitted by Exposé XI,
Remark 5.6.

Over an arbitrary base scheme, the normalizer of a closed relative torus in a
smooth separated quasi-compact group scheme is represented by a closed
subgroup scheme which is smooth over the base. The normalizer is the
published all-test functor `torusNormalizer t`. -/
def SeparatedTorusNormalizerStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S),
    Smooth G.X.hom → IsSeparated G.X.hom → QuasiCompact G.X.hom →
    ∀ (T : CommGroupScheme S) (t : T.toGrp ⟶ G),
      RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t →
      ∃ (N : GroupScheme S) (n : N ⟶ G),
        IsClosedSubgroup n ∧ Smooth N.X.hom ∧ (torusNormalizer t).IsRepresentedBy n

end Langlands.GroupScheme
