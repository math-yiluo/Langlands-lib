import Langlands.Geometry.FormalGroup.PDivisibleSplitPolarization
import Langlands.GroupScheme.Cartier.FiniteDualLinearBaseChange

/-! # Actual heights of p-divisible products and Cartier duals -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace Langlands.GroupScheme.Cartier.FiniteDual

variable {R : CommRingCat.{u}}

private def sectionsIso {X Y : Over (Spec R)} (i : X ≅ Y) : sections Y ≃ₐ[R] sections X :=
  let e := ((algΓ R).mapIso i).unop
  AlgEquiv.ofAlgHom e.hom.hom e.inv.hom
    (congrArg (fun f => CommAlgCat.Hom.hom f) e.inv_hom_id)
    (congrArg (fun f => CommAlgCat.Hom.hom f) e.hom_inv_id)

private def schemeAsSpec (G : CommGroupScheme (Spec R)) [IsAffine G.X.left] :
    G.X ≅ specOver R (AffineCoordinates.hopfAlgebra G.toGrp) :=
  (Grp.forget _).mapIso (AffineCoordinates.hopfSpecIso G.toGrp).symm

/-- Global sections of the actual affine group recover its chosen Hopf coordinates. -/
def sectionsCoordinateEquiv (G : CommGroupScheme (Spec R)) [IsAffine G.X.left] :
    sections G.X ≃ₐ[R] AffineCoordinates.hopfAlgebra G.toGrp :=
  (sectionsIso (schemeAsSpec G)).symm.trans (sectionsSpec R (AffineCoordinates.hopfAlgebra G.toGrp))

/-- The actual product of two affine commutative group schemes has the tensor
product of their affine coordinate algebras. -/
def productSectionsEquiv (G H : CommGroupScheme (Spec R)) [IsAffine G.X.left] [IsAffine H.X.left] :
    (sections G.X ⊗[R] sections H.X) ≃ₐ[R] sections (CommGroupScheme.prod G H).X := by
  let A := AffineCoordinates.hopfAlgebra G.toGrp
  let B := AffineCoordinates.hopfAlgebra H.toGrp
  let e : (CommGroupScheme.prod G H).X ≅ specOver R (A ⊗[R] B) :=
    (schemeAsSpec G ⊗ᵢ schemeAsSpec H) ≪≫ Functor.Monoidal.μIso (algSpec R)
      (op (CommAlgCat.of R A)) (op (CommAlgCat.of R B))
  exact (Algebra.TensorProduct.congr (sectionsCoordinateEquiv G) (sectionsCoordinateEquiv H)).trans
    ((sectionsSpec R (A ⊗[R] B)).symm.trans (sectionsIso e))

end Langlands.GroupScheme.Cartier.FiniteDual

namespace Langlands.PDivisibleGroup

open GroupScheme GroupScheme.Cartier GroupScheme.Cartier.FiniteDual

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime]

local instance levelFinite (G : PDivisibleGroup R p) (n : ℕ) : IsFinite (G.inclusions.obj n).X.hom :=
  (G.finiteLocallyFree n).1
local instance levelFlat (G : PDivisibleGroup R p) (n : ℕ) : Flat (G.inclusions.obj n).X.hom :=
  (G.finiteLocallyFree n).2.1
local instance levelFinitePresentation (G : PDivisibleGroup R p) (n : ℕ) :
    LocallyOfFinitePresentation (G.inclusions.obj n).X.hom := (G.finiteLocallyFree n).2.2
local instance levelAffine (G : PDivisibleGroup R p) (n : ℕ) : IsAffine (G.inclusions.obj n).X.left :=
  isAffine_of_isFinite (G.inclusions.obj n).toGrp

/-- The actual level rank of the product is the product of the two level ranks. -/
theorem levelRank_prod (G H : PDivisibleGroup R p) (n : ℕ) (x : PrimeSpectrum R) :
    (G.prod H).levelRank n x = G.levelRank n x * H.levelRank n x := by
  let C := sections (G.inclusions.obj n).X
  let E := sections (H.inclusions.obj n).X
  let eG := (sectionsCoordinateEquiv (G.inclusions.obj n)).toLinearEquiv
  let eH := (sectionsCoordinateEquiv (H.inclusions.obj n)).toLinearEquiv
  let : Module.Finite R (AffineCoordinates.hopfAlgebra (G.inclusions.obj n).toGrp) :=
    hopfAlgebra_finite (G.inclusions.obj n).toGrp
  let : Module.Flat R (AffineCoordinates.hopfAlgebra (G.inclusions.obj n).toGrp) :=
    hopfAlgebra_flat (G.inclusions.obj n).toGrp
  let : Module.Finite R (AffineCoordinates.hopfAlgebra (H.inclusions.obj n).toGrp) :=
    hopfAlgebra_finite (H.inclusions.obj n).toGrp
  let : Module.Flat R (AffineCoordinates.hopfAlgebra (H.inclusions.obj n).toGrp) :=
    hopfAlgebra_flat (H.inclusions.obj n).toGrp
  let : Module.Finite R C := Module.Finite.of_surjective eG.symm.toLinearMap eG.symm.surjective
  let : Module.Flat R C := Module.Flat.of_linearEquiv eG
  let : Module.Finite R E := Module.Finite.of_surjective eH.symm.toLinearMap eH.symm.surjective
  let : Module.Flat R E := Module.Flat.of_linearEquiv eH
  have e := (productSectionsEquiv (G.inclusions.obj n) (H.inclusions.obj n)).toLinearEquiv
  change Module.rankAtStalk (R := R) (sections (CommGroupScheme.prod (G.inclusions.obj n)
    (H.inclusions.obj n)).X) x = Module.rankAtStalk (R := R) C x * Module.rankAtStalk (R := R) E x
  exact (congrFun (Module.rankAtStalk_eq_of_equiv e) x).symm.trans
    (congrFun (Module.rankAtStalk_tensorProduct (R := R) (M := C) E) x)

/-- The actual level rank is unchanged by Cartier duality. -/
theorem levelRank_dual (G : PDivisibleGroup R p) (hExact : FiniteCartierDualExactnessStatement.{u})
    (n : ℕ) (x : PrimeSpectrum R) : (G.dual hExact).levelRank n x = G.levelRank n x := by
  let A := AffineCoordinates.hopfAlgebra (G.inclusions.obj n).toGrp
  let : Module.Finite R A := hopfAlgebra_finite (G.inclusions.obj n).toGrp
  let : Module.Projective R A := hopfAlgebra_projective (G.inclusions.obj n).toGrp
  let : Coalgebra.IsCocomm R A := affineCoordinates_isCocomm (G.inclusions.obj n)
  let e := (sectionsSpec R (Dual R A)).toLinearEquiv
  change Module.rankAtStalk (R := R) (sections (specOver R (Dual R A))) x =
    Module.rankAtStalk (R := R) (sections (G.inclusions.obj n).X) x
  have h := congrFun (Module.rankAtStalk_eq_of_equiv
    (sectionsCoordinateEquiv (G.inclusions.obj n)).toLinearEquiv) x
  exact (congrFun (Module.rankAtStalk_eq_of_equiv e) x).trans ((rankAtStalk_dual R A x).trans h.symm)

/-- The product of constant-height towers has the sum of their heights. -/
theorem HasHeight.prod {G H : PDivisibleGroup R p} {g h : ℕ} (hG : G.HasHeight g) (hH : H.HasHeight h) :
    (G.prod H).HasHeight (g + h) := by
  intro n x
  rw [levelRank_prod, hG n x, hH n x, ← pow_add, Nat.mul_add]

/-- Cartier duality preserves the height of the actual tower. -/
theorem HasHeight.dual {G : PDivisibleGroup R p} {h : ℕ} (hG : G.HasHeight h)
    (hExact : FiniteCartierDualExactnessStatement.{u}) : (G.dual hExact).HasHeight h := by
  intro n x
  rw [levelRank_dual, hG n x]

/-- The split polarized tower has twice the height of the primal tower. -/
theorem HasHeight.splitWithDual {G : PDivisibleGroup R p} {h : ℕ} (hG : G.HasHeight h)
    (hExact : FiniteCartierDualExactnessStatement.{u}) : (G.splitWithDual hExact).HasHeight (2 * h) := by
  rw [Nat.two_mul]
  exact hG.prod (hG.dual hExact)

end Langlands.PDivisibleGroup
