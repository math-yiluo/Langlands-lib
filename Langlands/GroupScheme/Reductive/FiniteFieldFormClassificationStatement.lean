import Langlands.GroupScheme.Reductive.StarAction
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.SeparableClosure

/-! # Statement: forms of a split reductive group over a finite field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Forms of a split reductive group over a finite field** (Conrad, *Reductive group
schemes* (2014), Example 7.2.3). Let `k` be a finite field, `G₀` a split connected reductive
group over `k` with pinning `p`, and `Θ = Aut(R, Δ)` the group of automorphisms of its root
datum preserving the base. Say that a group `G` over `k` with Galois pinning data `d` over the
separable closure `k_s` has class `θ ∈ Θ` if some base-preserving isomorphism `f` from the root
datum of `p` to that of `d` satisfies `f ∘ θ = μ_d(Frob) ∘ f`, where `μ_d` is the star action
and `Frob` is the arithmetic Frobenius `x ↦ x^{#k}` of `k_s`. Then every `θ` of finite order
is the class of some group, and two groups with classes `θ` and `θ'` are isomorphic over `k`
if and only if `θ` and `θ'` are conjugate in `Θ`. -/
def FiniteFieldFormClassificationStatement : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (G₀ : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G₀.X.hom] (p : SplitPinning G₀),
    let HasClass : ∀ (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
        [LocallyOfFiniteType G.X.hom],
        GaloisPinningData k (SeparableClosure k) G → p.basedRootDatumAut → Prop :=
      fun _ _ _ d θ =>
        ∃ f : RootPairing.Equiv p.rootDatum d.toSplitPinning.rootDatum,
          (∀ a, a ∈ p.base.support ↔ f.indexEquiv a ∈ d.toSplitPinning.base.support) ∧
          RootPairing.Equiv.comp f θ.val =
            RootPairing.Equiv.comp
              (d.starAction (FiniteField.frobeniusAlgEquivOfAlgebraic k (SeparableClosure k))).val
              f
    (∀ θ : p.basedRootDatumAut, IsOfFinOrder θ →
      ∃ (G : GroupScheme (Spec (CommRingCat.of k))) (_ : IsAffineHom G.X.hom)
        (_ : LocallyOfFiniteType G.X.hom) (d : GaloisPinningData k (SeparableClosure k) G),
        HasClass G d θ) ∧
    ∀ (G G' : GroupScheme (Spec (CommRingCat.of k)))
      [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
      [IsAffineHom G'.X.hom] [LocallyOfFiniteType G'.X.hom]
      (d : GaloisPinningData k (SeparableClosure k) G)
      (d' : GaloisPinningData k (SeparableClosure k) G') (θ θ' : p.basedRootDatumAut),
      HasClass G d θ → HasClass G' d' θ' → (Nonempty (G ≅ G') ↔ IsConj θ θ')

end Langlands.GroupScheme
