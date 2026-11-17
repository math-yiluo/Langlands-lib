import Langlands.GroupScheme.Reductive.StarAction
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.SeparableClosure

/-! # Statement: every finite-order based automorphism is the class of a form over a finite field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Existence of forms over a finite field with a given class** (Conrad, *Reductive group
schemes* (2014), Example 7.2.3, surjectivity part). Let `k` be a finite field and `G₀` a
split connected reductive group over `k` with pinning `p`. For every based automorphism
`θ ∈ Aut(R, Δ)` of finite order there are an affine group `G` of locally finite type over `k`,
Galois pinning data `d` of `G` over the separable closure `k_s` and a base-preserving
isomorphism `f` from the root datum of `p` to that of `d` with `f ∘ θ = μ_d(Frob) ∘ f`, where
`μ_d` is the star action and `Frob` the arithmetic Frobenius of `k_s`. This is clause 1 of
`FiniteFieldFormClassificationStatement`. -/
def FiniteFieldFormExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (G₀ : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G₀.X.hom] (p : SplitPinning G₀) (θ : p.basedRootDatumAut), IsOfFinOrder θ →
    ∃ (G : GroupScheme (Spec (CommRingCat.of k))) (_ : IsAffineHom G.X.hom)
      (_ : LocallyOfFiniteType G.X.hom) (d : GaloisPinningData k (SeparableClosure k) G)
      (f : RootPairing.Equiv p.rootDatum d.toSplitPinning.rootDatum),
      (∀ a, a ∈ p.base.support ↔ f.indexEquiv a ∈ d.toSplitPinning.base.support) ∧
      RootPairing.Equiv.comp f θ.val =
        RootPairing.Equiv.comp
          (d.starAction (FiniteField.frobeniusAlgEquivOfAlgebraic k (SeparableClosure k))).val f

end Langlands.GroupScheme
