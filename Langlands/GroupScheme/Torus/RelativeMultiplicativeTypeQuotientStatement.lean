import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
import Langlands.GroupScheme.Dynamic.Functoriality
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Statement: quotients by centralizers and normalizers of multiplicative-type subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- **Quotients by centralizers and normalizers** (Conrad, *Reductive group schemes* (2014),
Theorem 2.3.1, first two sentences). Let `G` be a smooth affine group scheme over a scheme
`S` and `i : H ⟶ G` a closed subgroup of multiplicative type.
1. The normalizer `N_G(H)` is represented by a closed subgroup of `G`.
2. For every subgroup `Z` representing `Z_G(H)`, the quotient `G/Z_G(H)` exists as a smooth
   `S`-scheme that is quasi-affine over `S`.
3. For every subgroup `N` representing `N_G(H)`, the quotient `G/N_G(H)` exists as a smooth
   `S`-scheme that is quasi-affine over `S`, and the quotient `W_G(H) = N_G(H)/Z_G(H)`
   exists as a separated étale `S`-group of finite presentation. -/
def RelativeMultiplicativeTypeQuotientStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (H : CommGroupScheme S) (i : H.toGrp ⟶ G),
    IsMultiplicativeType H.toGrp → IsClosedSubgroup i →
      let IsQuasiAffineOver : Over S → Prop := fun Y =>
        ∀ V : S.affineOpens, (Y.hom ⁻¹ᵁ (V : S.Opens)).toScheme.IsQuasiAffine
      (∃ (N : GroupScheme S) (n : N ⟶ G),
        IsClosedSubgroup n ∧ (torusNormalizer i).IsRepresentedBy n) ∧
      (∀ (Z : GroupScheme S) (z : Z ⟶ G), (torusCentralizer i).IsRepresentedBy z →
        ∃ Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient z,
          Smooth Q.scheme.hom ∧ IsQuasiAffineOver Q.scheme) ∧
      (∀ (N : GroupScheme S) (n : N ⟶ G), (torusNormalizer i).IsRepresentedBy n →
        (∃ Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient n,
          Smooth Q.scheme.hom ∧ IsQuasiAffineOver Q.scheme) ∧
        ∃ (W : GroupScheme S) (q : N ⟶ W),
          RelativeRoot.IsFppfQuotient ((torusCentralizer i).comap n) q ∧
            Etale W.X.hom ∧ IsSeparated W.X.hom ∧ QuasiCompact W.X.hom)

end Langlands.GroupScheme
