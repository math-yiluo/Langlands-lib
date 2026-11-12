import Langlands.GroupScheme.Reductive.StarAction
import Langlands.GroupScheme.Reductive.QuasiSplit
import Mathlib.FieldTheory.IsSepClosed

/-! # The star action of a quasi-split group is the natural action: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For a quasi-split connected reductive group over `k`, Galois pinning data over the
separable closure can be chosen so that the star action of `Gal(k_s/k)` is the ordinary
Galois action on the root datum of the chosen `k`-torus. -/
def StarActionQuasiSplitStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom], IsQuasiSplit G →
      ∃ d : GaloisPinningData k (SeparableClosure k) G,
        ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
          (d.starAction σ).val = d.galoisAction σ

end Langlands.GroupScheme
