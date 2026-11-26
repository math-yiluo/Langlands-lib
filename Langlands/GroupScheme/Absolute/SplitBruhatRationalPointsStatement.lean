import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Rational.BruhatPointReduction

/-! # Split Bruhat decomposition on rational points -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G B : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The Weyl class of a rational point normalizing `T` corresponds to its
double coset by the rational point image of `B`. -/
def BorelTorusBruhatRationalPoints (b : B ⟶ G) (t : T.toGrp ⟶ G) : Prop :=
  let Gk := Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X
  let Bk : Subgroup Gk :=
    (SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  ∃ e : relativeWeylGroup t ≃ DoubleCoset.Quotient (G := Gk) Bk Bk,
    ∀ n : normalizerPoints t, e (QuotientGroup.mk n) = DoubleCoset.mk Bk Bk n.val

/-- The split Bruhat decomposition gives a bijection on rational points for
every Borel pair whose maximal torus is split. -/
def SplitBruhatRationalPointsStatement : Prop :=
  ∀ (k : Type u) [Field k] (G B : GroupScheme (Spec (CommRingCat.of k)))
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G) (t : T.toGrp ⟶ G),
      IsConnectedReductive G → IsBorelPair b t → IsSplitTorus T.toGrp →
        BorelTorusBruhatRationalPoints b t

end Langlands.GroupScheme
