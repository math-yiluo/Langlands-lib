import Langlands.GroupScheme.Dynamic.GeneralLinearStabilizer
import Langlands.Group.CompactMatrixZariskiClosure
import Langlands.GroupScheme.MatrixRepresentationPolynomialImage
import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.Reductive.RationalPointDensityProof
import Langlands.GroupScheme.Rational.SplitUnipotentRationalDetection
import Langlands.GroupScheme.Rational.CharacterLatticeProof

/-! # Matrix polynomials vanishing on a finite-index subgroup of rational points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial Opposite
open Langlands.GroupScheme.GeneralLinear
open Langlands.Group.CompactMatrixZariski
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)

local instance sectionsAlgebra' (T : Over (Spec (CommRingCat.of k))) :
    Algebra k Γ(T.left, ⊤) :=
  ((algΓ (CommRingCat.of k)).obj T).unop.algebra

/-- The global function on `G` given by a polynomial in the matrix and inverse entries of `ρ`. -/
def matrixFunction : MvPolynomial (Coordinate n) k →ₐ[k] Γ(G.X.left, ⊤) :=
  aeval (R := k) (values (pointsEquiv n _ G.X ρ.hom.hom))

omit [DecidableEq n] in
theorem values_map {R S : Type*} [CommRing R] [CommRing S] [DecidableEq n] (f : R →+* S)
    (g : GL n R) : values (Matrix.GeneralLinearGroup.map f g) = f ∘ values g :=
  by apply GeneralLinear.values_map

/-- Pulling the function of `p` back to a point gives the value of `p` at its matrix. -/
theorem appTop_matrixFunction (x : G.affinePoints (CommAlgCat.of k k))
    (p : MvPolynomial (Coordinate n) k) :
    x.left.appTop (ρ.matrixFunction p) =
      Dynamic.affineTestEquiv k k (eval (values (ρ.affineMatrix (CommAlgCat.of k k) x)) p) := by
  have h1 := aeval_values_pointsEquiv (k := k) (n := n) G.X ρ.hom.hom p
  have h2 := aeval_values_pointsEquiv (k := k) (n := n) _ (x ≫ ρ.hom.hom) p
  have hcompare : pointsEquiv n _ _ (x ≫ ρ.hom.hom) =
      Matrix.GeneralLinearGroup.map (Dynamic.affineTestEquiv k k).toRingHom
        (ρ.affineMatrix (CommAlgCat.of k k) x) :=
    ρ.pointMatrix_eq_affineMatrix _ x
  have h3 : ∀ t, x.left.appTop (ρ.hom.hom.left.appTop t) =
      (x ≫ ρ.hom.hom).left.appTop t := fun t => by
    rw [Over.comp_left, Scheme.Hom.comp_appTop]
    rfl
  rw [matrixFunction, h1]
  refine (h3 _).trans (h2.symm.trans ?_)
  rw [hcompare, values_map, ← coe_aeval_eq_eval]
  exact (MvPolynomial.comp_aeval_apply (f := values (ρ.affineMatrix (CommAlgCat.of k k) x))
    (Dynamic.affineTestEquiv k k).toAlgHom p).symm

/-- Over an infinite field, a matrix polynomial that vanishes on the matrices of a finite-index
subgroup of the rational points of a connected reductive group vanishes on the matrices of all
rational points. -/
theorem eval_eq_zero_of_finiteIndex [Infinite k] (hG : IsConnectedReductive G)
    (H : Subgroup (G.affinePoints (CommAlgCat.of k k))) [H.FiniteIndex]
    (p : MvPolynomial (Coordinate n) k)
    (hp : ∀ h ∈ H, eval (values (ρ.affineMatrix (CommAlgCat.of k k) h)) p = 0)
    (g : G.affinePoints (CommAlgCat.of k k)) :
    eval (values (ρ.affineMatrix (CommAlgCat.of k k) g)) p = 0 := by
  set r := ρ.affineMatrix (CommAlgCat.of k k)
  have : Fintype (G.affinePoints (CommAlgCat.of k k) ⧸ H) := Fintype.ofFinite _
  let F := ∏ q : G.affinePoints (CommAlgCat.of k k) ⧸ H, leftTranslate (r q.out)⁻¹ p
  have hevalF : ∀ y, eval (values (r y)) F = 0 := by
    intro y
    rw [map_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ (QuotientGroup.mk y)) ?_
    rw [eval_leftTranslate, ← map_inv, ← map_mul]
    exact hp _ (QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk y : _ ⧸ H)))
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : IsIntegral G.X.left := CharacterLatticeProof.isIntegral_of_smooth k G.X.hom
  have hzero : ρ.matrixFunction F = 0 := by
    apply RationalDensity.rationalPointsDetectFunctions_of_dense (X := G.X) (reductiveRationalPointDensity k G hG)
    intro x
    have h := ρ.appTop_matrixFunction (GaloisPointComparison.rationalCoeffEquiv k G x) F
    rw [GaloisPointComparison.rationalCoeffEquiv_left] at h
    refine h.trans ?_
    rw [hevalF, map_zero]
    rfl
  have hprod : ∏ q : G.affinePoints (CommAlgCat.of k k) ⧸ H,
      ρ.matrixFunction (leftTranslate (r q.out)⁻¹ p) = 0 := by
    rw [← map_prod]
    exact hzero
  obtain ⟨q, -, hq⟩ := Finset.prod_eq_zero_iff.mp hprod
  have h := ρ.appTop_matrixFunction (q.out * g) (leftTranslate (r q.out)⁻¹ p)
  rw [hq, map_zero] at h
  have h' := (Dynamic.affineTestEquiv k k).injective (h.symm.trans (map_zero _).symm)
  rwa [eval_leftTranslate, map_mul, inv_mul_cancel_left] at h'

end Langlands.GroupScheme.MatrixRepresentation
