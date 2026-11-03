import Langlands.GroupScheme.AutomorphicAction.AffineCocycleQuotient
import Langlands.GroupScheme.Rational.KernelCentralizerSmooth
import Langlands.GroupScheme.Torus.KernelDiagonalizable
import Langlands.GroupScheme.Torus.DiagonalizableGeometry

/-! # Full-character-kernel affine quotient specialization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
variable {G C : GroupScheme (Spec (CommRingCat.of k))}
variable (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (a : characterLattice S)

/-- The actual full-kernel conjugation action in diagonalizable coordinates. -/
def kernelDiagonalizableAction :
    AutomorphicAction
      (Diagonalizable.groupScheme (CommRingCat.of k)
        (Diagonalizable.quotientLattice a)).toGrp G :=
  (((AutomorphicAction.conjugation i).restrict (characterKernelι a)).restrict
    (Diagonalizable.kernelDiagonalizableIso S hS a).inv)

/-- Reparametrization preserves the full all-test kernel centralizer functor. -/
theorem kernelDiagonalizableAction_fixedSubgroup :
    (kernelDiagonalizableAction hS i a).fixedSubgroup = kernelCentralizer i a :=
  AutomorphicAction.fixedSubgroup_restrict_iso
    ((AutomorphicAction.conjugation i).restrict (characterKernelι a))
    (Diagonalizable.kernelDiagonalizableIso S hS a).symm

/-- A fixed-subgroup representative remains the same representative in the
diagonalizable coordinates of the actual full kernel. -/
theorem kernelDiagonalizableAction_isRepresentedBy
    (j : C ⟶ G) (hrep : (kernelCentralizer i a).IsRepresentedBy j) :
    (kernelDiagonalizableAction hS i a).fixedSubgroup.IsRepresentedBy j := by
  rw [kernelDiagonalizableAction_fixedSubgroup]
  exact hrep

/-- An actual affine cocycle orbit for the full-kernel action gives the
published homogeneous quotient of the actual centralizer representative. -/
def kernelCentralizerAffineHomogeneousQuotient
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (M : (kernelDiagonalizableAction hS i a).CocycleModel)
    (j : C ⟶ G) (hrep : (kernelCentralizer i a).IsRepresentedBy j)
    (O : Over (Spec (CommRingCat.of k))) [IsAffineHom O.hom]
    (p : G.X ⟶ O) (e : O ⟶ M.scheme) [Mono e]
    (he : p ≫ e = M.orbit) (hp : Smooth p.left) (hs : Surjective p.left) :
    HomogeneousQuotientFromEmbedding.HomogeneousQuotient j :=
  M.affineHomogeneousQuotientOfOrbit j
    (kernelDiagonalizableAction_isRepresentedBy hS i a j hrep) O p e he hp hs

/-- Affineness concerns the same supplied orbit, used as the actual quotient. -/
theorem kernelCentralizerAffineHomogeneousQuotient_isAffineHom
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (M : (kernelDiagonalizableAction hS i a).CocycleModel)
    (j : C ⟶ G) (hrep : (kernelCentralizer i a).IsRepresentedBy j)
    (O : Over (Spec (CommRingCat.of k))) [IsAffineHom O.hom]
    (p : G.X ⟶ O) (e : O ⟶ M.scheme) [Mono e]
    (he : p ≫ e = M.orbit) (hp : Smooth p.left) (hs : Surjective p.left) :
    IsAffineHom (kernelCentralizerAffineHomogeneousQuotient hS i a
      M j hrep O p e he hp hs).scheme.hom :=
  inferInstanceAs (IsAffineHom O.hom)

end Langlands.GroupScheme.RelativeRoot
