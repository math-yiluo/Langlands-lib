import Langlands.GroupScheme.Rational.LeviSplitComponentRecallStatements
import Langlands.GroupScheme.Rational.LanglandsDecompositionCones

/-! # Split components of nested Levis and characters of standard Levis (Renard V.3.6, V.3.13)

Two geometric realization statements for the linear algebra of Renard V.3.6 and V.3.13.

* For rational Levi subgroups `M ⊆ L` of rational parabolics of a connected reductive group,
  the split component `A_L` of `L` lies in the split component `A_M` of `M`. With `L = G`
  this is `A_G ⊂ A_M`, the compatible diagram assumed by the published
  `RenardLeviCentralDecompositionStatement`.
* For a standard Levi `M` of a maximal split torus `T`, restriction of rational characters
  from `M` to `T` has real image the annihilator of the coroots of the selected simple
  roots: `𝔞*_M ⊂ 𝔞*_∅` is described by the coroots.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Renard V.3.13 (`A_G ⊂ A_L ⊂ A_M`) and the compatible diagram of V.3.6: let `G` be a
connected reductive group over a field `k`, `p : P ⟶ G` and `q : Q ⟶ G` parabolic
subgroups, `lM : M ⟶ P` and `lL : L ⟶ Q` rational Levi factors, and `m : M ⟶ L` a morphism
with `m ≫ lL ≫ q = lM ≫ p` (so `M ⊆ L` inside `G`). For split components `aL : A_L ⟶ L`
and `aM : A_M ⟶ M` there is a homomorphism `f : A_L ⟶ A_M` with `f ≫ aM ≫ m = aL`. -/
def LeviSplitComponentInclusionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P Q M L : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (q : Q ⟶ G) (lM : M ⟶ P) (lL : L ⟶ Q) (m : M ⟶ L),
      IsParabolicSubgroup p → IsParabolicSubgroup q →
      IsRationalLeviSubgroup lM → IsRationalLeviSubgroup lL →
      m ≫ lL ≫ q = lM ≫ p →
      ∀ (AL AM : CommGroupScheme (Spec (CommRingCat.of k)))
        (aL : AL.toGrp ⟶ L) (aM : AM.toGrp ⟶ M),
        IsSplitComponent aL → IsSplitComponent aM →
        ∃ f : AL ⟶ AM, CommGroupScheme.groupHom f ≫ aM ≫ m = aL

/-- Renard V.3.13 (`𝔞*_M ⊂ 𝔞*_∅` as the annihilator of the coroots of `M`): let `G` be a
connected reductive group over a field `k`, `i : T ⟶ G` a maximal split torus, `ν` a generic
cocharacter, `J` a set of simple relative roots for `ν`, `j : L ⟶ G` a closed subgroup
representing the standard Levi of `J`, and `t : T ⟶ L` with `t ≫ j = i`. For integral
reflection data `D` (supplying the coroots), restriction of real rational characters along
`t` has image exactly the real characters of `T` that vanish on the coroots `α̌`, `α ∈ J`. -/
def StandardLeviCharacterAnnihilatorStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    ∀ ν : cocharacterLattice T, IsGenericCocharacter i ν →
    ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
    ∀ (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ G),
      IsClosedSubgroup j →
      (standardLevi i ν J).IsRepresentedBy j →
      ∀ t : T.toGrp ⟶ L, t ≫ j = i →
      ∀ D : RelativeRootReflectionData i,
        (rationalCharacterRestrictReal t).range = corootAnnihilator i D J

/-- The two realization statements above. -/
def LeviCentralCompatibilityStatements : Prop :=
  LeviSplitComponentInclusionStatement.{u} ∧ StandardLeviCharacterAnnihilatorStatement.{u}

end Langlands.GroupScheme
