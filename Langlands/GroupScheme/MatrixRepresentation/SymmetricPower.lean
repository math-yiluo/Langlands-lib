import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.Multiplicative
import Langlands.GroupScheme.AffinePoints
import Langlands.Algebra.SymmetricMatrix

/-! # Actual symmetric powers of finite matrix representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

open Langlands.Algebra.SymmetricMatrix

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]

/-- The symmetric action, expressed as general-linear points over every scheme
of test. -/
def symmetricPoints (ρ : MatrixRepresentation G n) (d : ℕ) (T : Over (Spec R)) :
    (T ⟶ G.X) →* (T ⟶ (GeneralLinear.groupScheme (Index n d) R).X) :=
  (GeneralLinear.pointsEquiv (Index n d) R T).symm.toMonoidHom.comp
    ((glHom Γ(T.left, ⊤) n d).comp (ρ.pointMatrix T))

/-- The symmetric action commutes with arbitrary pullback of test schemes. -/
theorem symmetricPoints_naturality (ρ : MatrixRepresentation G n) (d : ℕ)
    {T T' : Over (Spec R)} (a : T' ⟶ T) (x : T ⟶ G.X) :
    symmetricPoints ρ d T' (a ≫ x) = a ≫ symmetricPoints ρ d T x := by
  apply (GeneralLinear.pointsEquiv (Index n d) R T').injective
  rw [GeneralLinear.pointsEquiv_naturality]
  simp only [symmetricPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  rw [pointMatrix_naturality, glHom_map]

/-- The actual degree-`d` symmetric power, with its canonical finite monomial
coordinates. It applies over arbitrary commutative base rings. -/
def symmetricPower (ρ : MatrixRepresentation G n) (d : ℕ) :
    MatrixRepresentation G (Index n d) :=
  homOfPoints (symmetricPoints ρ d) (symmetricPoints_naturality ρ d)

/-- The constructed representation has the symmetric general-linear action on
every scheme test, including nonreduced tests. -/
theorem symmetricPower_pointMatrix (ρ : MatrixRepresentation G n) (d : ℕ)
    (T : Over (Spec R)) (x : T ⟶ G.X) :
    (ρ.symmetricPower d).pointMatrix T x =
      glHom Γ(T.left, ⊤) n d (ρ.pointMatrix T x) := by
  rw [pointMatrix_apply, symmetricPower, comp_homOfPoints]
  exact (GeneralLinear.pointsEquiv (Index n d) R T).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
/-- The symmetric-power formula directly in the affine test algebra. -/
theorem symmetricPower_affineMatrix (ρ : MatrixRepresentation G n) (d : ℕ)
    (A : CommAlgCat.{u} R) (x : G.affinePoints A) :
    (ρ.symmetricPower d).affineMatrix A x = glHom A n d (ρ.affineMatrix A x) := by
  have h := symmetricPower_pointMatrix ρ d ((algSpec R).obj (op A)) x
  rw [pointMatrix_eq_affineMatrix, pointMatrix_eq_affineMatrix] at h
  erw [glHom_map] at h
  have hinj : Function.Injective
      (Matrix.GeneralLinearGroup.map (Corepresented.affineSectionsIso A).inv.hom.toRingHom :
        GL (Index n d) A → GL (Index n d) Γ(((algSpec R).obj (op A)).left, ⊤)) := by
    intro M N hMN
    apply Units.ext
    ext i j
    exact (Corepresented.affineSectionsAlgEquiv A).symm.injective
      (congrArg (fun B : GL (Index n d) Γ(((algSpec R).obj (op A)).left, ⊤) =>
        B.val i j) hMN)
  exact hinj h

/-- Symmetric powers commute with restriction to any group-scheme morphism. -/
theorem symmetricPower_restrict (ρ : MatrixRepresentation G n) (d : ℕ) (i : H ⟶ G) :
    (ρ.restrict i).symmetricPower d = (ρ.symmetricPower d).restrict i := by
  apply hom_ext_points
  intro T x
  apply (GeneralLinear.pointsEquiv (Index n d) R T).injective
  change ((ρ.restrict i).symmetricPower d).pointMatrix T x =
    ((ρ.symmetricPower d).restrict i).pointMatrix T x
  simp only [pointMatrix_restrict, symmetricPower_pointMatrix]

end Langlands.GroupScheme.MatrixRepresentation
