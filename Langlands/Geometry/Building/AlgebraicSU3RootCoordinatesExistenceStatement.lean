import Langlands.Geometry.Building.AlgebraicRankOneCoordinates

/-! # Existence of algebraic SU3 rank-one coordinates at multipliable roots: statement -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- **SU3 half of the algebraic rank-one coordinates.** For a connected reductive group with a
torus centralizer of its supplied maximal split torus, every indivisible relative root `b`
whose double `2 • b` is again a relative root has coherent opposite-root SU3 coordinates, and
the standard SU3 Weyl element maps into the normalizer of that same split torus.

This is the second clause of `AlgebraicRankOneCoordinatesExistenceStatement`, with the same
binders. Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition 7.1.1
(printed p. 239), the case where `2a` is a root. -/
def AlgebraicSU3RootCoordinatesExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (S Z : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : S.toGrp ⟶ G) (j : Z.toGrp ⟶ G) (s : S.toGrp ⟶ Z.toGrp),
      IsMaximalSplitTorus i →
      IsTorus Z.toGrp →
      (torusCentralizer i).IsRepresentedBy j →
      s ≫ j = i →
      ∀ b : characterLattice S,
        b ∈ RelativeRoot.indivisibleRoots i →
          2 • b ∈ relativeRoots i →
            ∃ C : AlgebraicSU3RootCoordinates i j s b,
              C.rho ⟨SU3Root.weylElement,
                SU3Root.weylElement_mem_specialUnitarySubgroup
                  (SU3Root.fieldInvolution C.base C.extension)⟩ ∈ normalizerPoints i

end Langlands.Geometry.Building
