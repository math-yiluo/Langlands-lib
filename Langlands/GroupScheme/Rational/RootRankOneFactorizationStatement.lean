import Langlands.GroupScheme.Rational.RelativeReflection
import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.GroupScheme.Rational.Characters

/-! # Actual relative-root rank-one factorization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeRoot

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
  [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- Two opposite-root points whose product with `u` normalizes the actual torus.
No nonidentity or reflection condition is included in this predicate. -/
def IsOppositeFactorPair (a : characterLattice T) (u : rationalPoints G)
    (p : rationalPoints G × rationalPoints G) : Prop :=
  p.1 ∈ (subgroup i (-a)).carrier (Over.mk (𝟙 _)) ∧
    p.2 ∈ (subgroup i (-a)).carrier (Over.mk (𝟙 _)) ∧
    p.1 * u * p.2 ∈ normalizerPoints i

/-- Every nonidentity actual root point has a unique normalizing opposite pair.
The product represents the relative reflection; for a nonmultipliable root
the factors coincide and the square of the product lies in the actual torus. -/
def HasRankOneFactorization : Prop :=
  ∀ (a : characterLattice T), a ∈ relativeRoots i →
    ∀ (u : rationalPoints G),
      u ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) → u ≠ 1 →
      (∃! p : rationalPoints G × rationalPoints G, IsOppositeFactorPair i a u p) ∧
        ∀ (p : rationalPoints G × rationalPoints G) (hp : IsOppositeFactorPair i a u p),
          p.1 ≠ 1 ∧ p.2 ≠ 1 ∧
            IsRelativeReflection i a
              (QuotientGroup.mk (⟨p.1 * u * p.2, hp.2.2⟩ : normalizerPoints i)) ∧
            ((2 : ℤ) • a ∉ relativeRoots i →
              p.1 = p.2 ∧
                p.1 = (p.1 * u * p.2)⁻¹ * u * (p.1 * u * p.2) ∧
                (p.1 * u * p.2) * (p.1 * u * p.2) ∈ (rationalPoints.map i).range)

end RelativeRoot

/-- **Relative-root rank-one factorization** (Kaletha–Prasad 2.11.17,
Conrad–Gabber–Prasad C.2.24(i),(iii)), specialized to connected reductive
groups over arbitrary fields and their actual maximal split tori. -/
def RootRankOneFactorizationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    RelativeRoot.HasRankOneFactorization i

end Langlands.GroupScheme
