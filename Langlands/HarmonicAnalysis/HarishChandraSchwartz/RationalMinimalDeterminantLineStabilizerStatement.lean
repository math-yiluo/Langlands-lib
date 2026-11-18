import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicDeterminantLine
import Langlands.GroupScheme.Rational.RelativeRoots

/-! # Stabilizer of the minimal adjoint determinant vector in the opposite radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.HarishChandraSchwartz

/-- The actual minimal adjoint determinant vector has trivial rational-point stabilizer
in the radical of the opposite generic cocharacter. -/
def RationalMinimalDeterminantLineStabilizerStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i → ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ (U : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom U.X.hom] (iU : U ⟶ G),
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy iU →
    ∀ (N d : ℕ) (cG : Lie.FiniteCoordinates G N) (cU : Lie.FiniteCoordinates U d),
    ∀ x ∈ (Dynamic.unipotent
        (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ i))).rationalPoints,
      ((Dynamic.adjointExteriorRepresentation cG (d := d)).rationalMatrix x : Matrix _ _ k) *ᵥ
          Dynamic.adjointExteriorCoordinates cG cU iU (CommAlgCat.of _ k) =
        Dynamic.adjointExteriorCoordinates cG cU iU (CommAlgCat.of _ k) → x = 1

end Langlands.HarishChandraSchwartz
