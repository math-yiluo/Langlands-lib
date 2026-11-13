import Langlands.GroupScheme.Reductive.StarAction
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SeparableClosure

/-! # The star action over the separable closure is realized at a finite Galois stage:
statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

local instance starActionFiniteStageBaseChangeAffine (k E : Type u) [Field k] [Field E]
    [Algebra k E] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

/-- Galois pinning data `d` of `G` over the separable closure of `k` is matched by Galois
pinning data `d'` of `G` over some finite Galois extension `L` of `k`, embedded in the
separable closure by `ι`. Some isomorphism `e` of root data from `d'` to `d` preserves the
chosen bases. It intertwines the star action of `σ ∈ Gal(L/k)` with the star action of every
`τ ∈ Aut_k(k^sep)` that restricts to `σ` along `ι`. -/
def StarActionFiniteStageStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : GaloisPinningData k (SeparableClosure k) G),
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : FiniteDimensional k L)
      (_ : IsGalois k L) (ι : L →ₐ[k] SeparableClosure k) (d' : GaloisPinningData k L G)
      (e : RootPairing.Equiv d'.toSplitPinning.rootDatum d.toSplitPinning.rootDatum),
      (∀ a, a ∈ d'.toSplitPinning.base.support ↔
        e.indexEquiv a ∈ d.toSplitPinning.base.support) ∧
      ∀ (σ : L ≃ₐ[k] L) (τ : SeparableClosure k ≃ₐ[k] SeparableClosure k),
        (∀ x, τ (ι x) = ι (σ x)) →
          RootPairing.Equiv.comp e (d'.starAction σ).val =
            RootPairing.Equiv.comp (d.starAction τ).val e

end Langlands.GroupScheme
