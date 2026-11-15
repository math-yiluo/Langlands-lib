import Langlands.GroupScheme.SpecialLinear
import Langlands.AlgebraicGeometry.Picard.LineBundle

/-! # The Picard groups of `SLₙ` and `GLₙ` vanish: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The Picard groups of `SLₙ` and `GLₙ` are zero** (Milne, *Algebraic Groups* (2017),
Proposition 20.30). For every field `k` and every finite index type `n`, every line bundle
on the underlying scheme of `SLₙ` over `k`, and every line bundle on the underlying scheme
of `GLₙ` over `k`, is isomorphic to the trivial line bundle.

Line bundles are the Library's locally free rank-one sheaves of modules
(`Langlands.AlgebraicGeometry.Picard.LineBundle`), and `LineBundle.trivial X` is the
structure sheaf. -/
def LinearPicardTrivialStatement : Prop :=
  ∀ (k : Type u) [Field k] (n : Type) [Fintype n] [DecidableEq n],
    let PicardTrivial : Scheme.{u} → Prop := fun X =>
      ∀ L : Langlands.AlgebraicGeometry.Picard.LineBundle X,
        Nonempty (L ≅ Langlands.AlgebraicGeometry.Picard.LineBundle.trivial X)
    PicardTrivial (SpecialLinear.groupScheme n (CommRingCat.of k)).X.left ∧
      PicardTrivial (GeneralLinear.groupScheme n (CommRingCat.of k)).X.left

end Langlands.GroupScheme
