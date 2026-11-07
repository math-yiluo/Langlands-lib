import Langlands.GroupScheme.Reductive.SteinbergBigCellReduction
import Langlands.GroupScheme.Reductive.SplitRootRankOneRelations
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.MatrixRepresentation.VectorGroupPolynomial
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Rank-one degree bounds for actual left-covariant coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Polynomial

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace Langlands.GroupScheme.RankOneCovariantCutoff

open AffineCoordinates

variable {k : Type u} [Field k]

/-- A polynomial and its reciprocal twist can both be regular only if the
original polynomial has degree at most the twisting exponent. -/
theorem natDegree_le_of_reciprocal [Infinite k] (P Q : k[X]) (m : ℕ)
    (h : ∀ t : k, t ≠ 0 → Q.eval t = t ^ m * P.eval t⁻¹) :
    P.natDegree ≤ m := by
  by_contra hle
  have hlt : m < P.natDegree := by omega
  have hP : P ≠ 0 := by
    intro he
    simp only [he, Polynomial.natDegree_zero] at hlt
    omega
  have hid : P.reverse = Polynomial.X ^ (P.natDegree - m) * Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_univ.sdiff (Set.finite_singleton (0 : k))).mono
    intro t ht
    have ht0 : t ≠ 0 := by simpa only [Set.mem_sdiff, Set.mem_univ,
      Set.mem_singleton_iff, true_and] using ht
    let : Invertible t := invertibleOfNonzero ht0
    have hr' := Polynomial.eval₂_reverse_mul_pow (RingHom.id k) t⁻¹ P
    have he : P.reverse.eval t = t ^ P.natDegree * P.eval t⁻¹ := by
      simpa only [invOf_eq_inv, inv_inv, Polynomial.eval₂_id, inv_pow, div_inv_eq_mul, mul_comm] using
        (eq_div_iff (pow_ne_zero _ (inv_ne_zero ht0))).mpr hr'
    change P.reverse.eval t = (Polynomial.X ^ (P.natDegree - m) * Q).eval t
    rw [he, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, h t ht0]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hlt.le]
  have hz := congrArg (fun f : k[X] => f.coeff 0) hid
  rw [Polynomial.coeff_zero_reverse, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    zero_pow (Nat.sub_ne_zero_of_lt hlt), zero_mul] at hz
  exact (Polynomial.leadingCoeff_ne_zero.mpr hP) hz

/-- Inverting the all-test rank-one relation gives the reciprocal
transition used to compare two regular affine-line curves. -/
theorem reciprocal_transition
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (nu : cocharacterLattice T) (xp xm : RootCell.Ga k ⟶ G)
    (Z : Over (Spec (CommRingCat.of k)))
    (hrel : RootCell.RelationOver i nu xp xm Z) (z : Γ(Z.left, ⊤)ˣ) :
    (RootCell.pt (1 : Γ(Z.left, ⊤)) ≫ xm.hom.hom) *
        (RootCell.pt ((z : Γ(Z.left, ⊤)) - 1) ≫ xp.hom.hom) =
      (RootCell.pt ((↑z⁻¹ : Γ(Z.left, ⊤)) * ((z : Γ(Z.left, ⊤)) - 1)) ≫ xp.hom.hom) *
        ((Gm.pointsEquiv _ Z).symm z⁻¹ ≫ (CommGroupScheme.groupHom nu).hom.hom ≫
          i.hom.hom) * (RootCell.pt (↑z⁻¹ : Γ(Z.left, ⊤)) ≫ xm.hom.hom) := by
  have he := hrel (RootCell.pt (-((z : Γ(Z.left, ⊤)) - 1))) (RootCell.pt (-1))
    (RootCell.pt (↑z⁻¹ * (-((z : Γ(Z.left, ⊤)) - 1))))
    (RootCell.pt (↑z⁻¹ * (-1))) z (by simp only [RootCell.crd_pt]; ring)
    (by simp only [RootCell.crd_pt]) (by simp only [RootCell.crd_pt])
  have hi := congrArg Inv.inv he
  dsimp only [RootCell.RelationAt] at hi
  simpa only [mul_neg, mul_one, RankOneRootCellRelation.gpt_neg,
    GrpObj.inv_comp, mul_inv_rev, inv_inv, map_inv, Category.assoc, mul_assoc] using hi

variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local instance {K : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom K.X.hom] :
    IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

/-- Actual coordinate evaluation with its global-section codomain explicit. -/
def sectionValue (Z : Over (Spec (CommRingCat.of k))) (g : Z ⟶ G.X)
    (b : algebra G) : Γ(Z.left, ⊤) :=
  pointAlgebraHom G Z g b

/-- Actual coordinate evaluation over an affine coefficient algebra, with the
relative-spectrum section comparison removed. -/
def affineValue (A : CommAlgCat (CommRingCat.of k))
    (g : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X) : algebra G →ₐ[k] A :=
  (specCounitEquiv A).symm.toAlgHom.comp (pointAlgebraHom G _ g)

theorem affineValue_naturality {A B : CommAlgCat (CommRingCat.of k)}
    (f : A ⟶ B) (g : (algSpec (CommRingCat.of k)).obj (op A) ⟶ G.X)
    (b : algebra G) :
    affineValue G B ((algSpec (CommRingCat.of k)).map f.op ≫ g) b =
      f.hom (affineValue G A g b) := by
  apply (specCounitEquiv B).injective
  change (specCounitEquiv B) ((specCounitEquiv B).symm _) = _
  rw [AlgEquiv.apply_symm_apply, pointAlgebraHom_naturality]
  have hn := Corepresented.affineSectionsIso_inv_naturality f
  have he := ConcreteCategory.congr_hom hn (affineValue G A g b)
  change ((algΓ (CommRingCat.of k)).map ((algSpec (CommRingCat.of k)).map f.op)).unop.hom
      (specCounitEquiv A (affineValue G A g b)) =
    specCounitEquiv B (f.hom (affineValue G A g b)) at he
  change ((algΓ (CommRingCat.of k)).map ((algSpec (CommRingCat.of k)).map f.op)).unop.hom
    (specCounitEquiv A ((specCounitEquiv A).symm _)) = _ at he
  simp only [AlgEquiv.apply_symm_apply] at he
  exact he

/-- The actual polynomial coordinate of any morphism from the affine
additive line, with no group-homomorphism assumption on the curve. -/
def curvePolynomial (a : (RootCell.Ga k).X ⟶ G.X) : algebra G →ₐ[k] k[X] :=
  (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toAlgHom.comp
    (affineValue G (VectorGroup.coordinateAlgebra (CommRingCat.of k) 1) a)

theorem curvePolynomial_aeval (a : (RootCell.Ga k).X ⟶ G.X)
    (b : algebra G) (A : CommAlgCat (CommRingCat.of k)) (t : A) :
    Polynomial.aeval t (curvePolynomial G a b) =
      affineValue G A (VectorGroup.affinePoint A (fun _ => t) ≫ a) b := by
  rw [VectorGroup.affinePoint, affineValue_naturality]
  change Polynomial.eval₂ (algebraMap k A) t
    (MvPolynomial.uniqueAlgEquiv k (Fin 1) _) =
      MvPolynomial.eval₂ (algebraMap k A) (fun _ => t) _
  exact MvPolynomial.eval₂_const_uniqueAlgEquiv

/-- Affine scalar parameters agree with the all-test section parameter. -/
theorem affinePoint_eq_pt (A : CommAlgCat (CommRingCat.of k)) (t : A) :
    VectorGroup.affinePoint A (fun _ : Fin 1 => t) = RootCell.pt (specCounitEquiv A t) := by
  apply RootCell.crd_injective
  rw [RootCell.crd_pt]
  change (Corepresented.pointsEquiv (VectorGroup.functor (CommRingCat.of k) 1)
    (VectorGroup.corepresentableBy (CommRingCat.of k) 1) _ _).toAdd 0 = _
  rw [Corepresented.pointsEquiv_eq_affinePointsEquiv,
    VectorGroup.affinePointsEquiv_affinePoint]
  rfl

/-- Evaluation of the actual curve polynomial, in global sections. -/
theorem curvePolynomial_eval (a : (RootCell.Ga k).X ⟶ G.X)
    (b : algebra G) (t : k) :
    specCounitEquiv (CommAlgCat.of k k) ((curvePolynomial G a b).eval t) =
      sectionValue G ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k)))
        (RootCell.pt (specCounitEquiv (CommAlgCat.of k k) t) ≫ a) b := by
  have he := curvePolynomial_aeval G a b (CommAlgCat.of k k) t
  rw [affinePoint_eq_pt] at he
  have he' := congrArg (specCounitEquiv (CommAlgCat.of k k)) he
  change specCounitEquiv (CommAlgCat.of k k)
    (Polynomial.eval₂ (algebraMap k k) t _) =
      specCounitEquiv (CommAlgCat.of k k)
        ((specCounitEquiv (CommAlgCat.of k k)).symm _) at he'
  simp only [Algebra.algebraMap_self, Polynomial.eval₂_id, AlgEquiv.apply_symm_apply] at he'
  exact he'

/-- The actual negative-root curve through a fixed rational point. -/
def negativeCurve (xm : RootCell.Ga k ⟶ G)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) : (RootCell.Ga k).X ⟶ G.X :=
  xm.hom.hom * G.constantPoint g (RootCell.Ga k).X

/-- The second regular curve in the reciprocal transition. -/
def transitionCurve (xp xm : RootCell.Ga k ⟶ G)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) : (RootCell.Ga k).X ⟶ G.X :=
  (RootCell.pt 1 ≫ xm.hom.hom) *
    (RootCell.pt (RootCell.crd (𝟙 (RootCell.Ga k).X) - 1) ≫ xp.hom.hom) *
      G.constantPoint g (RootCell.Ga k).X

omit [IsAffineHom G.X.hom] in
theorem point_negativeCurve (xm : RootCell.Ga k ⟶ G)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (Z : Over (Spec (CommRingCat.of k))) (t : Γ(Z.left, ⊤)) :
    RootCell.pt t ≫ negativeCurve G xm g =
      (RootCell.pt t ≫ xm.hom.hom) * G.constantPoint g Z := by
  rw [negativeCurve, MonObj.comp_mul, G.constantPoint_naturality]

omit [IsAffineHom G.X.hom] in
theorem point_transitionCurve (xp xm : RootCell.Ga k ⟶ G)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (Z : Over (Spec (CommRingCat.of k))) (t : Γ(Z.left, ⊤)) :
    RootCell.pt t ≫ transitionCurve G xp xm g =
      (RootCell.pt 1 ≫ xm.hom.hom) * (RootCell.pt (t - 1) ≫ xp.hom.hom) *
        G.constantPoint g Z := by
  rw [transitionCurve, MonObj.comp_mul, MonObj.comp_mul,
    G.constantPoint_naturality]
  simp only [← Category.assoc, RankOneRootCellRelation.comp_gpt,
    map_one, map_sub]
  have he := RootCell.crd_comp (RootCell.pt t) (𝟙 (RootCell.Ga k).X)
  simp only [Category.comp_id, RootCell.crd_pt] at he
  rw [← he]

/-- The coroot covariance and positive-root invariance of an actual coordinate
bound its degree along every negative-root curve through a rational point. -/
theorem natDegree_negativeCurve_le [Infinite k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (nu : cocharacterLattice T) (xp xm : RootCell.Ga k ⟶ G)
    (hrel : ∀ Z, RootCell.RelationOver i nu xp xm Z) (b : algebra G) (m : ℕ)
    (hxp : ∀ (Z : Over (Spec (CommRingCat.of k)))
      (a : Z ⟶ (RootCell.Ga k).X) (g : Z ⟶ G.X),
      sectionValue G Z ((a ≫ xp.hom.hom) * g) b = sectionValue G Z g b)
    (hnu : ∀ (Z : Over (Spec (CommRingCat.of k))) (z : Γ(Z.left, ⊤)ˣ)
      (g : Z ⟶ G.X), sectionValue G Z
        (((Gm.pointsEquiv _ Z).symm z ≫ (CommGroupScheme.groupHom nu).hom.hom ≫
          i.hom.hom) * g) b =
            (↑z⁻¹ : Γ(Z.left, ⊤)) ^ m * sectionValue G Z g b)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    (curvePolynomial G (negativeCurve G xm g) b).natDegree ≤ m := by
  apply natDegree_le_of_reciprocal _ (curvePolynomial G (transitionCurve G xp xm g) b) m
  intro t ht
  let A := CommAlgCat.of k k
  let Z := (algSpec (CommRingCat.of k)).obj (op A)
  let z : Γ(Z.left, ⊤)ˣ := Units.map (specCounitEquiv A).toMonoidHom (Units.mk0 t ht)
  have hz : (z : Γ(Z.left, ⊤)) = specCounitEquiv A t := rfl
  have hzi : (↑z⁻¹ : Γ(Z.left, ⊤)) = specCounitEquiv A t⁻¹ := by
    change specCounitEquiv A (↑(Units.mk0 t ht)⁻¹ : k) = _
    rw [Units.val_inv_eq_inv_val]
    rfl
  apply (specCounitEquiv A).injective
  rw [map_mul, map_pow, curvePolynomial_eval, curvePolynomial_eval,
    point_transitionCurve, point_negativeCurve]
  rw [← hz, reciprocal_transition i nu xp xm Z (hrel Z) z]
  simp only [mul_assoc]
  rw [hxp, hnu]
  simp only [inv_inv, hz, hzi]
  rfl

end Langlands.GroupScheme.RankOneCovariantCutoff
