import Langlands.Geometry.Building.AlgebraicRankOneCoordinates
import Langlands.GroupScheme.SpecialLinearBinaryBigCell

/-! # Existence of coherent algebraic opposite-root rank-one coordinates -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- A connected reductive group with a torus centralizer of its supplied maximal
split torus has coherent opposite-root SL2 or SU3 coordinates, with the standard
Weyl element mapping into the normalizer of that same split torus. -/
def AlgebraicRankOneCoordinatesExistenceStatement : Prop :=
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
          (2 • b ∉ relativeRoots i →
            ∃ C : AlgebraicSL2RootCoordinates i j s b,
              C.rho SpecialLinear.BinaryUpper.weylMatrix ∈ normalizerPoints i) ∧
          (2 • b ∈ relativeRoots i →
            ∃ C : AlgebraicSU3RootCoordinates i j s b,
              C.rho ⟨SU3Root.weylElement,
                SU3Root.weylElement_mem_specialUnitarySubgroup
                  (SU3Root.fieldInvolution C.base C.extension)⟩ ∈ normalizerPoints i)

end Langlands.Geometry.Building
