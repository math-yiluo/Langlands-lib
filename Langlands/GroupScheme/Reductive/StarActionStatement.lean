import Langlands.GroupScheme.Reductive.StarAction
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Independence of choices and continuity of the star action: statements -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

local instance starActionStatementBaseChangeAffine (k E : Type u) [Field k] [Field E]
    [Algebra k E] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

/-- The star action does not depend on the choice of Galois pinning data. For two choices
`d` and `d'`, some `E`-point `g` of `G_E` conjugates the torus of `d` onto the torus of `d'`.
The isomorphism of root data induced by this conjugation preserves the chosen bases and
intertwines the two star actions. -/
def StarActionIndependenceStatement : Prop :=
  ∀ (k E : Type u) [Field k] [Field E] [Algebra k E]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d d' : GaloisPinningData k E G),
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of E))) ⟶
        ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X)
      (φ : d.toSplitPinning.torus ≅ d'.toSplitPinning.torus)
      (e : RootPairing.Equiv d.toSplitPinning.rootDatum d'.toSplitPinning.rootDatum),
      d.toSplitPinning.inclusion ≫
          (((GroupScheme.baseChange (algebraBaseMap k E)).obj G).innerIso g).hom =
        CommGroupScheme.groupHom φ.hom ≫ d'.toSplitPinning.inclusion ∧
      (⇑e.weightMap = ⇑(characterLattice.congr φ)) ∧
      (∀ a, a ∈ d.toSplitPinning.base.support ↔
        e.indexEquiv a ∈ d'.toSplitPinning.base.support) ∧
      ∀ σ : E ≃ₐ[k] E,
        RootPairing.Equiv.comp e (d.starAction σ).val =
          RootPairing.Equiv.comp (d'.starAction σ).val e

/-- Continuity of the star action: for an algebraic extension `E/k`, every `σ ∈ Aut_k(E)`
fixing a suitable finite-dimensional intermediate field acts trivially, both through the
ordinary Galois action on the root datum and through the star action. -/
def StarActionContinuityStatement : Prop :=
  ∀ (k E : Type u) [Field k] [Field E] [Algebra k E] [Algebra.IsAlgebraic k E]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : GaloisPinningData k E G),
    ∃ L : IntermediateField k E, FiniteDimensional k L ∧
      ∀ σ : E ≃ₐ[k] E, (∀ x ∈ L, σ x = x) →
        d.galoisAction σ = 1 ∧ d.starAction σ = 1

end Langlands.GroupScheme
