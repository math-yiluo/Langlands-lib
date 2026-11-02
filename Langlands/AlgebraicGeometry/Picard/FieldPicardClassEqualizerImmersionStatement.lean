import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Langlands.AlgebraicGeometry.Picard.RelativePicardSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # The locus where two Picard classes of actual line bundles agree is an immersion -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Let `X` be a proper scheme over a field `k`, let `T` be a scheme over `k`, and let `L`
and `M` be line bundles on `T ×_k X`. There is an immersion `ι : Z ⟶ T` over `k` such that
a morphism `g : T' ⟶ T` over `k` factors through `ι` exactly when the fppf Picard classes of
the pullbacks of `L` and `M` to `T' ×_k X` are equal. -/
def FieldPicardClassEqualizerImmersionStatement : Prop :=
  ∀ (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k))), IsProper X.hom →
    ∀ (T : Over (Spec (CommRingCat.of k)))
      (L M : LineBundle ((relativeSpace X.hom).obj T)),
      ∃ (Z : Over (Spec (CommRingCat.of k))) (ι : Z ⟶ T), IsImmersion ι.left ∧
        AlgebraicSpace.RepresentsEqualizer (F := RelativePicard.classSheafPresheaf X.hom) ι
          (RelativePicard.sheafClassOf X.hom T L) (RelativePicard.sheafClassOf X.hom T M)

end Langlands.AlgebraicGeometry.Picard
