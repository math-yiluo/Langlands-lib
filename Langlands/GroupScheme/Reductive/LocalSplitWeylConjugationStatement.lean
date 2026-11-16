import Langlands.GroupScheme.Reductive.LocalSplitIsomorphismAssembly
import Langlands.GroupScheme.Reductive.LocalSplitRankOneNormalStatement
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationStatement

/-! # Statement: universality of Weyl conjugation in Weyl families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- **Common Weyl conjugation units.** For words `W` and simple-root data `u` of `G` and `u'`
of `H`, write `v = weylFamily P W u`, `v' = weylFamily P W u'`, and `n_c`, `n'_c` for the Weyl
points `rootWeylPoint P u c`, `rootWeylPoint P u' c`. For every simple root `c` and every root
`d` there is a single unit `κ` with `Ad(n_c) ∘ v_d = v_{s_c d} ∘ (x ↦ κ x)` in `G` and
`Ad(n'_c) ∘ v'_d = v'_{s_c d} ∘ (x ↦ κ x)` in `H`. Here `s_c d` is the index
`P.reflectionPerm c d`. -/
def WeylConjugationRelations (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base)
    (W : ∀ α, SimpleWord P b α) (u : J → (Ga R ⟶ G)) (u' : J → (Ga R ⟶ H)) : Prop :=
  ∀ c ∈ b.support, ∀ d : J, ∃ κ : Rˣ,
    weylFamily P W u d ≫ (G.innerIso (rootWeylPoint P u c)).hom =
        scaleHom (κ : R) ≫ weylFamily P W u (P.reflectionPerm c d) ∧
      weylFamily P W u' d ≫ (H.innerIso (rootWeylPoint P u' c)).hom =
        scaleHom (κ : R) ≫ weylFamily P W u' (P.reflectionPerm c d)

end LocalSplitCell

open LocalSplitCell in
/-- **Universality of Weyl conjugation in Weyl families over a local ring.** Take two reductive
groups over a local ring with closed fibrewise maximal coordinate split tori carrying the same
fibrewise root datum, a base `b` with descending words `W`, and Weyl-normalized simple-root
data `u`, `u'` for `b` that are rank-one normal at every simple root. Then conjugation by the
simple Weyl points acts on the two Weyl families by common units
(`WeylConjugationRelations`). -/
def LocalSplitWeylConjugationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (I : Type u) [Fintype I] [DecidableEq I]
    (J : Type u) (G H : GroupScheme (Spec (CommRingCat.of R)))
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom],
    IsReductive G → IsReductive H →
    ∀ (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
      (i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H),
      IsClosedSubgroup i → IsClosedSubgroup i' →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i' →
      ∀ (P : RootDatum J (I → ℤ) (I → ℤ)),
      IsFibrewiseRootDatumOf I G i P → IsFibrewiseRootDatumOf I H i' P →
      ∀ (b : P.Base) (W : ∀ α, SimpleWord P b α), IsDescendingWords P b W →
      ∀ (u : J → (Ga R ⟶ G)) (u' : J → (Ga R ⟶ H)),
      (∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a) ∧
        IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a))) →
      (∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a)) →
      (∀ a ∈ b.support, IsRootParametrization i' (P.root a) (u' a) ∧
        IsRootParametrization i' (P.root (P.reflectionPerm a a)) (u' (P.reflectionPerm a a))) →
      (∀ a ∈ b.support, IsWeylPoint i' (rootWeylPoint P u' a) (P.reflection a)) →
      (∀ a ∈ b.support, RankOneNormal i P u a) →
      (∀ a ∈ b.support, RankOneNormal i' P u' a) →
      WeylConjugationRelations P b W u u'

end Langlands.GroupScheme
