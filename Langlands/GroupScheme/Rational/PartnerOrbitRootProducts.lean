import Langlands.GroupScheme.Rational.PartnerOrbitUnitaryCoordinates
import Langlands.GroupScheme.Rational.OrthogonalOrbitWeylNormalizer
import Langlands.GroupScheme.Rational.SimpleRootFiberProducts
import Langlands.Geometry.Building.QuasiSplitMultipliableOpposite
import Langlands.GroupScheme.Rational.SimpleCorootCoordinates

/-! # Root-group products over partnered orbits of simple roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitPinning

open SpecialLinear SpecialLinear.BinaryPresentation

local notation "SL3" A => Matrix.SpecialLinearGroup (Fin 3) A

section Matrices

variable {K : Type*} [Field K]

/-- The corner transvection `1 + t E₀₂`. -/
def cornerUpper (t : K) : SL3 K :=
  ⟨!![1, 0, t; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

/-- The corner transvection `1 + t E₂₀`. -/
def cornerLower (t : K) : SL3 K :=
  ⟨!![1, 0, 0; 0, 1, 0; t, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_cornerUpper (t : K) :
    (cornerUpper t : Matrix (Fin 3) (Fin 3) K) = !![1, 0, t; 0, 1, 0; 0, 0, 1] := rfl

theorem coe_cornerLower (t : K) :
    (cornerLower t : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 1, 0; t, 0, 1] := rfl

/-- The left Weyl matrix carries the right upper transvection to the corner one. -/
theorem left_weyl_mul_cornerUpper (t : K) :
    TernaryPresentation.left BinaryUpper.weylMatrix * cornerUpper t =
      TernaryPresentation.right (upper t) * TernaryPresentation.left BinaryUpper.weylMatrix := by
  ext r s
  simp only [Matrix.SpecialLinearGroup.coe_mul, TernaryPresentation.coe_left,
    TernaryPresentation.coe_right]
  fin_cases r <;> fin_cases s <;>
    simp [cornerUpper, TernaryPresentation.leftMatrix, TernaryPresentation.rightMatrix,
      BinaryUpper.weylMatrix, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_three]

/-- The left Weyl matrix carries the right lower transvection to the corner one. -/
theorem left_weyl_mul_cornerLower (t : K) :
    TernaryPresentation.left BinaryUpper.weylMatrix * cornerLower t =
      TernaryPresentation.right (lower t) * TernaryPresentation.left BinaryUpper.weylMatrix := by
  ext r s
  simp only [Matrix.SpecialLinearGroup.coe_mul, TernaryPresentation.coe_left,
    TernaryPresentation.coe_right]
  fin_cases r <;> fin_cases s <;>
    simp [cornerLower, TernaryPresentation.leftMatrix, TernaryPresentation.rightMatrix,
      BinaryUpper.weylMatrix, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_three]

/-- The ordered upper product `e₁₂(u) e₀₂(w) e₀₁(v)`. -/
theorem coe_upperTriple (u w v : K) :
    ((TernaryPresentation.right (upper u) * cornerUpper w * TernaryPresentation.left (upper v) :
      SL3 K) : Matrix (Fin 3) (Fin 3) K) = !![1, v, w; 0, 1, u; 0, 0, 1] := by
  ext r s
  simp only [Matrix.SpecialLinearGroup.coe_mul, TernaryPresentation.coe_left,
    TernaryPresentation.coe_right]
  fin_cases r <;> fin_cases s <;>
    simp [cornerUpper, TernaryPresentation.leftMatrix, TernaryPresentation.rightMatrix,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_three]

/-- The ordered lower product `e₁₀(v) e₂₀(w) e₂₁(u)`. -/
theorem coe_lowerTriple (v w u : K) :
    ((TernaryPresentation.left (lower v) * cornerLower w * TernaryPresentation.right (lower u) :
      SL3 K) : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; v, 1, 0; w, u, 1] := by
  ext r s
  simp only [Matrix.SpecialLinearGroup.coe_mul, TernaryPresentation.coe_left,
    TernaryPresentation.coe_right]
  fin_cases r <;> fin_cases s <;>
    simp [cornerLower, TernaryPresentation.leftMatrix, TernaryPresentation.rightMatrix,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_three]

/-- An upper unipotent matrix is the ordered product of its three root transvections. -/
theorem eq_upperTriple {g : SL3 K} (hg : IsUpperSL3 g) :
    g = TernaryPresentation.right (upper ((g : Matrix (Fin 3) (Fin 3) K) 1 2)) *
      cornerUpper ((g : Matrix (Fin 3) (Fin 3) K) 0 2) *
      TernaryPresentation.left (upper ((g : Matrix (Fin 3) (Fin 3) K) 0 1)) := by
  obtain ⟨hd, hl⟩ := hg
  apply Subtype.ext
  rw [coe_upperTriple]
  ext r s
  fin_cases r <;> fin_cases s <;> simp [hd, hl]

/-- A lower unipotent matrix is the ordered product of its three root transvections. -/
theorem eq_lowerTriple {g : SL3 K} (hg : IsLowerSL3 g) :
    g = TernaryPresentation.left (lower ((g : Matrix (Fin 3) (Fin 3) K) 1 0)) *
      cornerLower ((g : Matrix (Fin 3) (Fin 3) K) 2 0) *
      TernaryPresentation.right (lower ((g : Matrix (Fin 3) (Fin 3) K) 2 1)) := by
  obtain ⟨hd, hl⟩ := hg
  have hd' : ∀ i, (g : Matrix (Fin 3) (Fin 3) K) i i = 1 := fun i => by
    simpa using hd i
  have hl' : ∀ i j : Fin 3, i < j → (g : Matrix (Fin 3) (Fin 3) K) i j = 0 := fun i j h => by
    simpa using hl j i h
  apply Subtype.ext
  rw [coe_lowerTriple]
  ext r s
  fin_cases r <;> fin_cases s <;> simp [hd', hl']

theorem isUpperSL3_upperTriple (u w v : K) :
    IsUpperSL3 (TernaryPresentation.right (upper u) * cornerUpper w *
      TernaryPresentation.left (upper v)) := by
  unfold IsUpperSL3
  rw [coe_upperTriple]
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i <;> simp
  · fin_cases i <;> fin_cases j <;> simp_all

theorem isLowerSL3_lowerTriple (v w u : K) :
    IsLowerSL3 (TernaryPresentation.left (lower v) * cornerLower w *
      TernaryPresentation.right (lower u)) := by
  unfold IsLowerSL3
  rw [coe_lowerTriple]
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i <;> simp
  · fin_cases i <;> fin_cases j <;> simp_all

theorem isCentralUpperSL3_cornerUpper (w : K) : IsCentralUpperSL3 (cornerUpper w) := by
  refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_, ?_⟩
  · fin_cases i <;> simp [cornerUpper]
  · fin_cases i <;> fin_cases j <;> simp_all [cornerUpper]
  · simp [cornerUpper]
  · simp [cornerUpper]

theorem isCentralLowerSL3_cornerLower (w : K) : IsCentralLowerSL3 (cornerLower w) := by
  refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_, ?_⟩
  · fin_cases i <;> simp [cornerLower]
  · fin_cases i <;> fin_cases j <;> simp_all [cornerLower]
  · simp [cornerLower]
  · simp [cornerLower]

theorem eq_cornerUpper {g : SL3 K} (hg : IsCentralUpperSL3 g) :
    g = cornerUpper ((g : Matrix (Fin 3) (Fin 3) K) 0 2) := by
  obtain ⟨⟨hd, hl⟩, h01, h12⟩ := hg
  apply Subtype.ext
  rw [coe_cornerUpper]
  ext r s
  fin_cases r <;> fin_cases s <;> simp [hd, hl, h01, h12]

theorem eq_cornerLower {g : SL3 K} (hg : IsCentralLowerSL3 g) :
    g = cornerLower ((g : Matrix (Fin 3) (Fin 3) K) 2 0) := by
  obtain ⟨⟨hd, hl⟩, h10, h21⟩ := hg
  have hd' : ∀ i, (g : Matrix (Fin 3) (Fin 3) K) i i = 1 := fun i => by
    simpa using hd i
  have hl' : ∀ i j : Fin 3, i < j → (g : Matrix (Fin 3) (Fin 3) K) i j = 0 := fun i j h => by
    simpa using hl j i h
  apply Subtype.ext
  rw [coe_cornerLower]
  ext r s
  fin_cases r <;> fin_cases s <;> simp [hd', hl', h10, h21]

theorem cornerUpper_mul_neg (w : K) : cornerUpper w * cornerUpper (-w) = 1 := by
  ext r s
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases r <;> fin_cases s <;> simp [cornerUpper, Matrix.mul_apply, Fin.sum_univ_three]

theorem cornerLower_mul_neg (w : K) : cornerLower w * cornerLower (-w) = 1 := by
  ext r s
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases r <;> fin_cases s <;> simp [cornerLower, Matrix.mul_apply, Fin.sum_univ_three]

theorem outer_cornerUpper (w : K) :
    TernaryPresentation.outer (cornerUpper w) = cornerUpper (-w) := by
  ext r s
  rw [TernaryPresentation.coe_outer, TernaryPresentation.outerMatrix,
    inv_eq_of_mul_eq_one_right (cornerUpper_mul_neg w)]
  fin_cases r <;> fin_cases s <;>
    simp [cornerUpper, TernaryPresentation.antidiagonal, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.vecMul, dotProduct]

theorem outer_cornerLower (w : K) :
    TernaryPresentation.outer (cornerLower w) = cornerLower (-w) := by
  ext r s
  rw [TernaryPresentation.coe_outer, TernaryPresentation.outerMatrix,
    inv_eq_of_mul_eq_one_right (cornerLower_mul_neg w)]
  fin_cases r <;> fin_cases s <;>
    simp [cornerLower, TernaryPresentation.antidiagonal, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.vecMul, dotProduct]

theorem isUpperSL3_outer {g : SL3 K} (hg : IsUpperSL3 g) :
    IsUpperSL3 (TernaryPresentation.outer g) := by
  rw [eq_upperTriple hg, map_mul, map_mul, TernaryPresentation.outer_right, outer_cornerUpper,
    TernaryPresentation.outer_left]
  unfold IsUpperSL3
  simp only [Matrix.SpecialLinearGroup.coe_mul, TernaryPresentation.coe_left,
    TernaryPresentation.coe_right]
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i <;>
      simp [cornerUpper, TernaryPresentation.leftMatrix, TernaryPresentation.rightMatrix,
        Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three]
  · fin_cases i <;> fin_cases j <;>
      simp_all [cornerUpper, TernaryPresentation.leftMatrix, TernaryPresentation.rightMatrix,
        Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three]

theorem isLowerSL3_outer {g : SL3 K} (hg : IsLowerSL3 g) :
    IsLowerSL3 (TernaryPresentation.outer g) := by
  rw [eq_lowerTriple hg, map_mul, map_mul, TernaryPresentation.outer_right, outer_cornerLower,
    TernaryPresentation.outer_left]
  unfold IsLowerSL3
  simp only [Matrix.SpecialLinearGroup.coe_mul, TernaryPresentation.coe_left,
    TernaryPresentation.coe_right]
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i <;>
      simp [cornerLower, TernaryPresentation.leftMatrix, TernaryPresentation.rightMatrix,
        Matrix.SpecialLinearGroup.transvection_coe]
  · fin_cases i <;> fin_cases j <;>
      simp_all [cornerLower, TernaryPresentation.leftMatrix, TernaryPresentation.rightMatrix,
        Matrix.SpecialLinearGroup.transvection_coe]

theorem isCentralUpperSL3_outer {g : SL3 K} (hg : IsCentralUpperSL3 g) :
    IsCentralUpperSL3 (TernaryPresentation.outer g) := by
  rw [eq_cornerUpper hg, outer_cornerUpper]
  exact isCentralUpperSL3_cornerUpper _

theorem isCentralLowerSL3_outer {g : SL3 K} (hg : IsCentralLowerSL3 g) :
    IsCentralLowerSL3 (TernaryPresentation.outer g) := by
  rw [eq_cornerLower hg, outer_cornerLower]
  exact isCentralLowerSL3_cornerLower _

/-- The antidiagonal Weyl matrix `J` as a ternary special linear matrix. -/
def gramSL3 : SL3 K := ⟨SU3Root.gram K, by simp [SU3Root.gram, Matrix.det_fin_three]⟩

/-- `J` is the product of the left, right and left Weyl matrices. -/
theorem gramSL3_eq :
    (gramSL3 : SL3 K) = TernaryPresentation.left BinaryUpper.weylMatrix *
      TernaryPresentation.right BinaryUpper.weylMatrix *
        TernaryPresentation.left BinaryUpper.weylMatrix := by
  ext r s
  simp only [Matrix.SpecialLinearGroup.coe_mul, TernaryPresentation.coe_left,
    TernaryPresentation.coe_right]
  fin_cases r <;> fin_cases s <;>
    simp [gramSL3, SU3Root.gram, TernaryPresentation.leftMatrix, TernaryPresentation.rightMatrix,
      BinaryUpper.weylMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem map_gramSL3 {K' : Type*} [Field K'] (f : K →+* K') :
    Matrix.SpecialLinearGroup.map f (gramSL3 : SL3 K) = gramSL3 := by
  ext r s
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  fin_cases r <;> fin_cases s <;> simp [gramSL3, SU3Root.gram]

/-- The product of a left and a right diagonal matrix. -/
theorem coe_left_diag_mul_right_diag (s t : Kˣ) :
    ((TernaryPresentation.left (diag s) * TernaryPresentation.right (diag t) : SL3 K) :
      Matrix (Fin 3) (Fin 3) K) =
      !![(s : K), 0, 0; 0, ((s⁻¹ : Kˣ) : K) * t, 0; 0, 0, ((t⁻¹ : Kˣ) : K)] := by
  ext r r'
  simp only [Matrix.SpecialLinearGroup.coe_mul, TernaryPresentation.coe_left,
    TernaryPresentation.coe_right]
  fin_cases r <;> fin_cases r' <;>
    simp [TernaryPresentation.leftMatrix, TernaryPresentation.rightMatrix,
      Root.contractingMatrix, Matrix.mul_apply, Fin.sum_univ_three]

end Matrices

section Split

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {p : SplitPinning G}
  (hAdj : AdjacentSimpleRootSpecialLinearStatement.{u})
  (x : p.NormalizedSimpleRootParametrizations)

local instance partnerOrbitRootProductsMono : Mono p.inclusion.hom.hom.left :=
  p.isMaximalTorus.2.1.mono

/-- The inverse of the image of the Weyl matrix under the rank-one homomorphism of a simple
root, as a point of the normalizer of the pinned torus. -/
def weylInvPoint (a : p.base.support) : normalizerPoints p.inclusion :=
  ⟨(rootSL2 x a BinaryUpper.weylMatrix)⁻¹,
    (normalizerPoints p.inclusion).inv_mem (rootSL2_weylMatrix_mem x a)⟩

theorem coe_weylInvPoint (a : p.base.support) :
    (weylInvPoint x a : rationalPoints G) = (rootSL2 x a BinaryUpper.weylMatrix)⁻¹ := rfl

variable [LocallyOfFiniteType G.X.hom] in
/-- The inverse Weyl point acts on characters by the reflection of the simple root. -/
theorem weylAction_weylInvPoint (a : p.base.support) (χ : characterLattice p.torus) :
    weylAction p.inclusion (weylInvPoint x a) χ =
      χ - p.rootDatum.toLinearMap χ (p.rootDatum.coroot a) • p.rootDatum.root a := by
  have hw : (rootSL2 x a BinaryUpper.weylMatrix)⁻¹ =
      (x a).negPoint (-1) * (x a).unitPoint * (x a).negPoint (-1) := by
    rw [← map_inv, weylMatrix_inv_eq, map_mul, map_mul, rootSL2_lower, rootSL2_upper]
    change (x a).negPoint (-1) * (x a).linked.xpPoint 1 * (x a).negPoint (-1) = _
    rw [(x a).xpPoint_linked]
    rfl
  have he : weylInvPoint x a = ⟨(x a).negPoint (-1) * (x a).unitPoint * (x a).negPoint (-1),
      ((x a).isOppositeFactorPair_unitPoint).2.2⟩ := Subtype.ext hw
  rw [he]
  exact Langlands.Geometry.Building.weylAction_oppositeFactorPair_eq p.inclusion p.isSplitTorus
    p.isMaximalTorus.2.1 p.isRootDatum (a : p.rootIndex) (x a).unitPoint_mem
    (x a).unitPoint_ne_one (x a).isOppositeFactorPair_unitPoint χ

variable [LocallyOfFiniteType G.X.hom] in
theorem weylAction_weylInvPoint_root {a b : p.base.support}
    (hba : p.rootDatum.pairing b a = -1) :
    weylAction p.inclusion (weylInvPoint x a) (p.rootDatum.root b) =
      p.rootDatum.root a + p.rootDatum.root b := by
  rw [weylAction_weylInvPoint, RootPairing.root_coroot_eq_pairing, hba, neg_one_smul,
    sub_neg_eq_add, add_comm]

variable [LocallyOfFiniteType G.X.hom] in
theorem weylAction_weylInvPoint_neg_root {a b : p.base.support}
    (hba : p.rootDatum.pairing b a = -1) :
    weylAction p.inclusion (weylInvPoint x a) (-p.rootDatum.root b) =
      -(p.rootDatum.root a + p.rootDatum.root b) := by
  rw [map_neg, weylAction_weylInvPoint_root x hba]

/-- Conjugation by a normalizer point carries root groups to Weyl-translated root groups. -/
theorem conj_mem_rootGroupPoints_iff (n : normalizerPoints p.inclusion)
    (χ : characterLattice p.torus) (g : rationalPoints G) :
    (n : rationalPoints G) * g * (n : rationalPoints G)⁻¹ ∈
        Langlands.Geometry.Building.rootGroupPoints p.inclusion (weylAction p.inclusion n χ) ↔
      g ∈ Langlands.Geometry.Building.rootGroupPoints p.inclusion χ := by
  have h := RelativeRoot.normalizer_conj_mem_iff p.inclusion χ n (U := Over.mk (𝟙 _)) g
  rw [GroupScheme.constantPoint_self] at h
  exact h

section Pair

variable {a b : p.base.support} (hab : p.rootDatum.pairing a b = -1)
  (hba : p.rootDatum.pairing b a = -1)

include hab hba in
theorem pairSL3_left_upper (t : k) :
    pairSL3 hAdj x a b (TernaryPresentation.left (upper t)) = (rankData x a).xp t := by
  rw [pairSL3_left hAdj x hab hba, rootSL2_upper]

include hab hba in
theorem pairSL3_right_upper (t : k) :
    pairSL3 hAdj x a b (TernaryPresentation.right (upper t)) = (rankData x b).xp t := by
  rw [pairSL3_right hAdj x hab hba, rootSL2_upper]

include hab hba in
theorem pairSL3_left_lower (t : k) :
    pairSL3 hAdj x a b (TernaryPresentation.left (lower t)) = (rankData x a).xm t := by
  rw [pairSL3_left hAdj x hab hba, rootSL2_lower]

include hab hba in
theorem pairSL3_right_lower (t : k) :
    pairSL3 hAdj x a b (TernaryPresentation.right (lower t)) = (rankData x b).xm t := by
  rw [pairSL3_right hAdj x hab hba, rootSL2_lower]

include hab hba in
/-- The corner transvection goes to the conjugate of the root point of `b` by the inverse
Weyl point of `a`. -/
theorem pairSL3_cornerUpper (t : k) :
    pairSL3 hAdj x a b (cornerUpper t) =
      (weylInvPoint x a : rationalPoints G) * (rankData x b).xp t *
        (weylInvPoint x a : rationalPoints G)⁻¹ := by
  have h := congrArg (pairSL3 hAdj x a b) (left_weyl_mul_cornerUpper t)
  rw [map_mul, map_mul, pairSL3_left hAdj x hab hba, pairSL3_right hAdj x hab hba,
    rootSL2_upper] at h
  rw [coe_weylInvPoint, inv_inv, mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]

include hab hba in
theorem pairSL3_cornerLower (t : k) :
    pairSL3 hAdj x a b (cornerLower t) =
      (weylInvPoint x a : rationalPoints G) * (rankData x b).xm t *
        (weylInvPoint x a : rationalPoints G)⁻¹ := by
  have h := congrArg (pairSL3 hAdj x a b) (left_weyl_mul_cornerLower t)
  rw [map_mul, map_mul, pairSL3_left hAdj x hab hba, pairSL3_right hAdj x hab hba,
    rootSL2_lower] at h
  rw [coe_weylInvPoint, inv_inv, mul_assoc, ← h, ← mul_assoc, inv_mul_cancel, one_mul]

variable [LocallyOfFiniteType G.X.hom] in
include hab hba in
theorem pairSL3_cornerUpper_mem (t : k) :
    pairSL3 hAdj x a b (cornerUpper t) ∈ Langlands.Geometry.Building.rootGroupPoints
      p.inclusion (p.rootDatum.root a + p.rootDatum.root b) := by
  rw [pairSL3_cornerUpper hAdj x hab hba, ← weylAction_weylInvPoint_root x hba,
    conj_mem_rootGroupPoints_iff, rankData_xp]
  exact (x b).toRootParametrization.rationalPoint_mem t

variable [LocallyOfFiniteType G.X.hom] in
include hab hba in
theorem pairSL3_cornerLower_mem (t : k) :
    pairSL3 hAdj x a b (cornerLower t) ∈ Langlands.Geometry.Building.rootGroupPoints
      p.inclusion (-(p.rootDatum.root a + p.rootDatum.root b)) := by
  rw [pairSL3_cornerLower hAdj x hab hba, ← weylAction_weylInvPoint_neg_root x hba,
    conj_mem_rootGroupPoints_iff, rankData_xm]
  exact (x b).linked.xmPoint_mem t

variable [LocallyOfFiniteType G.X.hom] in
include hab hba in
theorem exists_pairSL3_cornerUpper_eq {g : rationalPoints G}
    (hg : g ∈ Langlands.Geometry.Building.rootGroupPoints p.inclusion
      (p.rootDatum.root a + p.rootDatum.root b)) :
    ∃ t : k, pairSL3 hAdj x a b (cornerUpper t) = g := by
  have h1 : (weylInvPoint x a : rationalPoints G) *
      ((weylInvPoint x a : rationalPoints G)⁻¹ * g * (weylInvPoint x a : rationalPoints G)) *
        (weylInvPoint x a : rationalPoints G)⁻¹ = g := by group
  have hmem : (weylInvPoint x a : rationalPoints G)⁻¹ * g *
      (weylInvPoint x a : rationalPoints G) ∈
      Langlands.Geometry.Building.rootGroupPoints p.inclusion (p.rootDatum.root b) := by
    refine (conj_mem_rootGroupPoints_iff (weylInvPoint x a) _ _).mp ?_
    rw [weylAction_weylInvPoint_root x hba, h1]
    exact hg
  obtain ⟨t, ht⟩ := (x b).linked.exists_xpPoint_eq hmem
  refine ⟨t, ?_⟩
  rw [pairSL3_cornerUpper hAdj x hab hba]
  change (weylInvPoint x a : rationalPoints G) * (x b).linked.xpPoint t *
    (weylInvPoint x a : rationalPoints G)⁻¹ = g
  rw [ht]
  group

variable [LocallyOfFiniteType G.X.hom] in
include hab hba in
theorem exists_pairSL3_cornerLower_eq {g : rationalPoints G}
    (hg : g ∈ Langlands.Geometry.Building.rootGroupPoints p.inclusion
      (-(p.rootDatum.root a + p.rootDatum.root b))) :
    ∃ t : k, pairSL3 hAdj x a b (cornerLower t) = g := by
  have h1 : (weylInvPoint x a : rationalPoints G) *
      ((weylInvPoint x a : rationalPoints G)⁻¹ * g * (weylInvPoint x a : rationalPoints G)) *
        (weylInvPoint x a : rationalPoints G)⁻¹ = g := by group
  have hmem : (weylInvPoint x a : rationalPoints G)⁻¹ * g *
      (weylInvPoint x a : rationalPoints G) ∈
      Langlands.Geometry.Building.rootGroupPoints p.inclusion (-p.rootDatum.root b) := by
    refine (conj_mem_rootGroupPoints_iff (weylInvPoint x a) _ _).mp ?_
    rw [weylAction_weylInvPoint_neg_root x hba, h1]
    exact hg
  obtain ⟨t, ht⟩ := (x b).linked.exists_xmPoint_eq hmem
  refine ⟨t, ?_⟩
  rw [pairSL3_cornerLower hAdj x hab hba]
  change (weylInvPoint x a : rationalPoints G) * (x b).linked.xmPoint t *
    (weylInvPoint x a : rationalPoints G)⁻¹ = g
  rw [ht]
  group

include hab hba in
theorem pairSL3_cornerUpper_injective :
    Function.Injective fun t : k => pairSL3 hAdj x a b (cornerUpper t) := by
  intro t t' h
  simp only [pairSL3_cornerUpper hAdj x hab hba, mul_left_inj, mul_right_inj] at h
  exact (x b).linked.xpPoint_injective h

include hab hba in
theorem pairSL3_cornerLower_injective :
    Function.Injective fun t : k => pairSL3 hAdj x a b (cornerLower t) := by
  intro t t' h
  simp only [pairSL3_cornerLower hAdj x hab hba, mul_left_inj, mul_right_inj] at h
  exact (x b).linked.xmPoint_injective h

include hab hba in
theorem pairSL3_gramSL3_mem :
    pairSL3 hAdj x a b gramSL3 ∈ normalizerPoints p.inclusion := by
  rw [gramSL3_eq, map_mul, map_mul, pairSL3_left hAdj x hab hba, pairSL3_right hAdj x hab hba]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (rootSL2_weylMatrix_mem x a)
    (rootSL2_weylMatrix_mem x b)) (rootSL2_weylMatrix_mem x a)

include hab hba in
theorem pairSL3_left_diag_mul_right_diag (s t : kˣ) :
    pairSL3 hAdj x a b (TernaryPresentation.left (diag s) * TernaryPresentation.right (diag t)) =
      rationalPoints.map p.inclusion (p.simpleCorootPoint a s * p.simpleCorootPoint b t) := by
  rw [map_mul, pairSL3_left hAdj x hab hba, pairSL3_right hAdj x hab hba, rootSL2_diag,
    rootSL2_diag, map_mul]
  rfl

end Pair

namespace PartnerData

variable {O : Set p.base.support} (D : PartnerData O)

section Lists

variable {n : ℕ} (e : D.orientation ≃ Fin n)

/-- The product over the orientation is the ordered product along any enumeration of it. -/
theorem pairOrbitSL3_eq_prod_ofFn (h : p.base.support → SL3 k) :
    D.pairOrbitSL3 hAdj x h = (List.ofFn fun l =>
      pairSL3 hAdj x (e.symm l) (D.partner (e.symm l)) (h (e.symm l))).prod := by
  classical
  have huniv : (Finset.univ : Finset D.orientation) = (List.ofFn fun l => e.symm l).toFinset := by
    ext t
    simp only [Finset.mem_univ, List.mem_toFinset, true_iff]
    exact List.mem_ofFn.mpr ⟨e t, by simp⟩
  rw [pairOrbitSL3_apply]
  refine (Finset.noncommProd_congr huniv (fun _ _ => rfl) _).trans ?_
  refine (Finset.noncommProd_toFinset _ _ _ (List.nodup_ofFn.mpr e.symm.injective)).trans ?_
  rw [List.map_ofFn]
  rfl

end Lists

section Extend

open Classical in
/-- Extension of a family on the orientation to a pair family. -/
def pairExtend (M : p.base.support → SL3 k) : p.base.support → SL3 k :=
  fun a => if a ∈ D.orientation then M a else TernaryPresentation.outer (M (D.partner a))

theorem pairExtend_of_mem (M : p.base.support → SL3 k) {a : p.base.support}
    (ha : a ∈ D.orientation) : D.pairExtend M a = M a := by
  unfold pairExtend
  rw [ite_eq_left ha]

theorem pairExtend_of_not_mem (M : p.base.support → SL3 k) {a : p.base.support}
    (ha : a ∉ D.orientation) :
    D.pairExtend M a = TernaryPresentation.outer (M (D.partner a)) := by
  unfold pairExtend
  rw [ite_eq_right ha]

theorem isPairFamily_pairExtend (M : p.base.support → SL3 k) : D.IsPairFamily (D.pairExtend M) := by
  intro a ha
  by_cases h : a ∈ D.orientation
  · have hp : D.partner a ∉ D.orientation := (D.mem_orientation_iff ha).mp h
    rw [D.pairExtend_of_not_mem M hp, D.partner_partner a ha, D.pairExtend_of_mem M h]
  · have hp : D.partner a ∈ D.orientation := D.partner_mem_orientation ha h
    rw [D.pairExtend_of_mem M hp, D.pairExtend_of_not_mem M h,
      TernaryPresentation.outer_outer]

theorem pairOrbitSL3_pairExtend (M : p.base.support → SL3 k) :
    D.pairOrbitSL3 hAdj x (D.pairExtend M) = D.pairOrbitSL3 hAdj x M := by
  rw [pairOrbitSL3_apply, pairOrbitSL3_apply]
  congr 1
  funext r
  rw [D.pairExtend_of_mem M r.2]

/-- A property preserved by the outer involution and holding on the orientation holds for the
extension on all of `O`. -/
theorem pairExtend_prop (P : (SL3 k) → Prop)
    (hP : ∀ g, P g → P (TernaryPresentation.outer g)) {M : p.base.support → SL3 k}
    (hM : ∀ a ∈ D.orientation, P (M a)) : ∀ a ∈ O, P (D.pairExtend M a) := by
  intro a ha
  by_cases h : a ∈ D.orientation
  · rw [D.pairExtend_of_mem M h]
    exact hM a h
  · rw [D.pairExtend_of_not_mem M h]
    exact hP _ (hM _ (D.partner_mem_orientation ha h))

/-- Two pair families agreeing on the orientation agree on `O`. -/
theorem eq_of_eq_on_orientation {h h' : p.base.support → SL3 k} (hh : D.IsPairFamily h)
    (hh' : D.IsPairFamily h') (heq : ∀ a ∈ D.orientation, h a = h' a) :
    ∀ a ∈ O, h a = h' a := by
  intro a ha
  by_cases h1 : a ∈ D.orientation
  · exact heq a h1
  · have hp := D.partner_mem_orientation ha h1
    have e1 := hh (D.partner a) (D.mem a ha)
    have e2 := hh' (D.partner a) (D.mem a ha)
    rw [D.partner_partner a ha] at e1 e2
    rw [e1, e2, heq _ hp]

end Extend

section UpperPieces

variable {n : ℕ} (e : D.orientation ≃ Fin n)

/-- The roots of the pieces, ordered `π r, r + π r, r` inside the piece of `r`. -/
def upperPieceRoot (l : Fin n) (c : Fin 3) : characterLattice p.torus :=
  ![p.rootDatum.root (D.partner (e.symm l)),
    p.rootDatum.root ((e.symm l : D.orientation) : p.base.support) +
      p.rootDatum.root (D.partner (e.symm l)),
    p.rootDatum.root ((e.symm l : D.orientation) : p.base.support)] c

/-- The roots of the pieces along `Fin (n * 3)`. -/
def upperPieceEnum (k' : Fin (n * 3)) : characterLattice p.torus :=
  D.upperPieceRoot e (finProdFinEquiv.symm k').1 (finProdFinEquiv.symm k').2

theorem upperPieceEnum_finProd (l : Fin n) (c : Fin 3) :
    D.upperPieceEnum e (finProdFinEquiv (l, c)) = D.upperPieceRoot e l c := by
  simp [upperPieceEnum]

/-- The three root-group factors of the piece of `r` with entries `u, w, v`. -/
def upperPiecePoint (u w v : Fin n → k) (l : Fin n) (c : Fin 3) : rationalPoints G :=
  ![pairSL3 hAdj x (e.symm l) (D.partner (e.symm l)) (TernaryPresentation.right (upper (u l))),
    pairSL3 hAdj x (e.symm l) (D.partner (e.symm l)) (cornerUpper (w l)),
    pairSL3 hAdj x (e.symm l) (D.partner (e.symm l)) (TernaryPresentation.left (upper (v l)))] c

variable [LocallyOfFiniteType G.X.hom] in
theorem upperPiecePoint_mem (u w v : Fin n → k) (l : Fin n) (c : Fin 3) :
    D.upperPiecePoint hAdj x e u w v l c ∈
      Langlands.Geometry.Building.rootGroupPoints p.inclusion (D.upperPieceRoot e l c) := by
  have hr := D.mem_of_mem_orientation (e.symm l).2
  obtain ⟨hab, hba⟩ := D.pairing _ hr
  fin_cases c
  · change pairSL3 hAdj x (e.symm l) (D.partner (e.symm l))
        (TernaryPresentation.right (upper (u l))) ∈
      Langlands.Geometry.Building.rootGroupPoints p.inclusion
        (p.rootDatum.root (D.partner (e.symm l)))
    rw [pairSL3_right_upper hAdj x hab hba, rankData_xp]
    exact (x _).toRootParametrization.rationalPoint_mem _
  · exact pairSL3_cornerUpper_mem hAdj x hab hba _
  · change pairSL3 hAdj x (e.symm l) (D.partner (e.symm l))
        (TernaryPresentation.left (upper (v l))) ∈
      Langlands.Geometry.Building.rootGroupPoints p.inclusion
        (p.rootDatum.root ((e.symm l : D.orientation) : p.base.support))
    rw [pairSL3_left_upper hAdj x hab hba, rankData_xp]
    exact (x _).toRootParametrization.rationalPoint_mem _

theorem prod_upperPiecePoint (u w v : Fin n → k) :
    (List.ofFn fun k' : Fin (n * 3) => D.upperPiecePoint hAdj x e u w v
        (finProdFinEquiv.symm k').1 (finProdFinEquiv.symm k').2).prod =
      (List.ofFn fun l => pairSL3 hAdj x (e.symm l) (D.partner (e.symm l))
        (TernaryPresentation.right (upper (u l)) * cornerUpper (w l) *
          TernaryPresentation.left (upper (v l)))).prod := by
  rw [Langlands.Geometry.Building.list_ofFn_prod_finProd]
  congr 1
  apply List.ofFn_inj.mpr
  funext l
  simp only [Equiv.symm_apply_apply, map_mul]
  rfl

/-- The product over the orientation of an upper family is the ordered product of the
root-group factors of its pieces. -/
theorem pairOrbitSL3_eq_prod_upperPiecePoint {h : p.base.support → SL3 k}
    (hh : ∀ a ∈ O, IsUpperSL3 (h a)) :
    D.pairOrbitSL3 hAdj x h = (List.ofFn fun k' : Fin (n * 3) => D.upperPiecePoint hAdj x e
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 1 2)
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 0 2)
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 0 1)
      (finProdFinEquiv.symm k').1 (finProdFinEquiv.symm k').2).prod := by
  rw [prod_upperPiecePoint, D.pairOrbitSL3_eq_prod_ofFn hAdj x e]
  congr 1
  apply List.ofFn_inj.mpr
  funext l
  rw [← eq_upperTriple (hh _ (D.mem_of_mem_orientation (e.symm l).2))]

variable (U : Subgroup (rationalPoints G))

variable [LocallyOfFiniteType G.X.hom] in
/-- **Membership.** Products of upper families lie in a subgroup that is the ordered product of
the root groups of the pieces. -/
theorem pairOrbitSL3_mem_of_isUpper
    (hU : ∀ g, g ∈ U ↔ ∃ y : (k' : Fin (n * 3)) → Langlands.Geometry.Building.rootGroupPoints
        p.inclusion (D.upperPieceEnum e k'),
      g = (List.ofFn fun k' => (y k' : rationalPoints G)).prod)
    (h : p.base.support → SL3 k) (hh : ∀ a ∈ O, IsUpperSL3 (h a)) :
    D.pairOrbitSL3 hAdj x h ∈ U := by
  rw [hU]
  refine ⟨fun k' => ⟨D.upperPiecePoint hAdj x e
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 1 2)
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 0 2)
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 0 1)
      (finProdFinEquiv.symm k').1 (finProdFinEquiv.symm k').2,
    D.upperPiecePoint_mem hAdj x e _ _ _ _ _⟩, ?_⟩
  exact D.pairOrbitSL3_eq_prod_upperPiecePoint hAdj x e hh

variable [LocallyOfFiniteType G.X.hom] in
/-- **Products.** Every member of such a subgroup is the product of an upper pair family. -/
theorem exists_isUpper_pairOrbitSL3_eq
    (hU : ∀ g, g ∈ U ↔ ∃ y : (k' : Fin (n * 3)) → Langlands.Geometry.Building.rootGroupPoints
        p.inclusion (D.upperPieceEnum e k'),
      g = (List.ofFn fun k' => (y k' : rationalPoints G)).prod)
    {g : rationalPoints G} (hg : g ∈ U) :
    ∃ h : p.base.support → SL3 k, (∀ a ∈ O, IsUpperSL3 (h a)) ∧ D.IsPairFamily h ∧
      D.pairOrbitSL3 hAdj x h = g := by
  classical
  obtain ⟨y, rfl⟩ := (hU g).mp hg
  have key : ∀ (l : Fin n) (c : Fin 3), (y (finProdFinEquiv (l, c)) : rationalPoints G) ∈
      Langlands.Geometry.Building.rootGroupPoints p.inclusion (D.upperPieceRoot e l c) :=
    fun l c => D.upperPieceEnum_finProd e l c ▸ (y (finProdFinEquiv (l, c))).2
  have h0 : ∀ l, ∃ t : k, pairSL3 hAdj x (e.symm l) (D.partner (e.symm l))
      (TernaryPresentation.right (upper t)) = y (finProdFinEquiv (l, 0)) := by
    intro l
    obtain ⟨hab, hba⟩ := D.pairing _ (D.mem_of_mem_orientation (e.symm l).2)
    obtain ⟨t, ht⟩ := (x (D.partner (e.symm l))).toRootParametrization.exists_rationalPoint_eq
      (key l 0)
    exact ⟨t, by rw [pairSL3_right_upper hAdj x hab hba, rankData_xp, ht]⟩
  have h1 : ∀ l, ∃ t : k, pairSL3 hAdj x (e.symm l) (D.partner (e.symm l))
      (cornerUpper t) = y (finProdFinEquiv (l, 1)) := by
    intro l
    obtain ⟨hab, hba⟩ := D.pairing _ (D.mem_of_mem_orientation (e.symm l).2)
    exact exists_pairSL3_cornerUpper_eq hAdj x hab hba (key l 1)
  have h2 : ∀ l, ∃ t : k, pairSL3 hAdj x (e.symm l) (D.partner (e.symm l))
      (TernaryPresentation.left (upper t)) = y (finProdFinEquiv (l, 2)) := by
    intro l
    obtain ⟨hab, hba⟩ := D.pairing _ (D.mem_of_mem_orientation (e.symm l).2)
    obtain ⟨t, ht⟩ := (x ((e.symm l : D.orientation) : p.base.support)).toRootParametrization.exists_rationalPoint_eq
      (key l 2)
    exact ⟨t, by rw [pairSL3_left_upper hAdj x hab hba, rankData_xp, ht]⟩
  choose u hu using h0
  choose w hw using h1
  choose v hv using h2
  let M : p.base.support → SL3 k := fun a => if ha : a ∈ D.orientation then
    TernaryPresentation.right (upper (u (e ⟨a, ha⟩))) * cornerUpper (w (e ⟨a, ha⟩)) *
      TernaryPresentation.left (upper (v (e ⟨a, ha⟩))) else 1
  have hM : ∀ l, M (e.symm l) = TernaryPresentation.right (upper (u l)) * cornerUpper (w l) *
      TernaryPresentation.left (upper (v l)) := by
    intro l
    simp only [M]
    rw [dite_eq_left (e.symm l).2]
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
  refine ⟨D.pairExtend M, D.pairExtend_prop IsUpperSL3 (fun g hg => isUpperSL3_outer hg)
    (fun a ha => ?_), D.isPairFamily_pairExtend M, ?_⟩
  · have hMa : M a = TernaryPresentation.right (upper (u (e ⟨a, ha⟩))) *
        cornerUpper (w (e ⟨a, ha⟩)) * TernaryPresentation.left (upper (v (e ⟨a, ha⟩))) := by
      simp only [M]
      rw [dite_eq_left ha]
    rw [hMa]
    exact isUpperSL3_upperTriple _ _ _
  · rw [pairOrbitSL3_pairExtend, D.pairOrbitSL3_eq_prod_ofFn hAdj x e,
      Langlands.Geometry.Building.list_ofFn_prod_finProd]
    congr 1
    apply List.ofFn_inj.mpr
    funext l
    rw [hM, map_mul, map_mul, hu l, hw l, hv l]

/-- **Uniqueness.** Upper pair families with the same product agree on `O`, when the ordered
products of root-group points of the pieces are unique. -/
theorem eq_of_isUpper_pairOrbitSL3_eq [LocallyOfFiniteType G.X.hom]
    (hU' : ∀ y y' : (k' : Fin (n * 3)) → Langlands.Geometry.Building.rootGroupPoints
        p.inclusion (D.upperPieceEnum e k'),
      (List.ofFn fun k' => (y k' : rationalPoints G)).prod =
        (List.ofFn fun k' => (y' k' : rationalPoints G)).prod → y = y')
    (h h' : p.base.support → SL3 k) (hh : ∀ a ∈ O, IsUpperSL3 (h a))
    (hh' : ∀ a ∈ O, IsUpperSL3 (h' a)) (hp : D.IsPairFamily h) (hp' : D.IsPairFamily h')
    (heq : D.pairOrbitSL3 hAdj x h = D.pairOrbitSL3 hAdj x h') : ∀ a ∈ O, h a = h' a := by
  apply D.eq_of_eq_on_orientation hp hp'
  intro a ha
  let y : (k' : Fin (n * 3)) → Langlands.Geometry.Building.rootGroupPoints p.inclusion
      (D.upperPieceEnum e k') := fun k' => ⟨D.upperPiecePoint hAdj x e
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 1 2)
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 0 2)
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 0 1)
      (finProdFinEquiv.symm k').1 (finProdFinEquiv.symm k').2,
    D.upperPiecePoint_mem hAdj x e _ _ _ _ _⟩
  let y' : (k' : Fin (n * 3)) → Langlands.Geometry.Building.rootGroupPoints p.inclusion
      (D.upperPieceEnum e k') := fun k' => ⟨D.upperPiecePoint hAdj x e
      (fun l => (h' (e.symm l) : Matrix (Fin 3) (Fin 3) k) 1 2)
      (fun l => (h' (e.symm l) : Matrix (Fin 3) (Fin 3) k) 0 2)
      (fun l => (h' (e.symm l) : Matrix (Fin 3) (Fin 3) k) 0 1)
      (finProdFinEquiv.symm k').1 (finProdFinEquiv.symm k').2,
    D.upperPiecePoint_mem hAdj x e _ _ _ _ _⟩
  have hy : y = y' := hU' y y' ((D.pairOrbitSL3_eq_prod_upperPiecePoint hAdj x e hh).symm.trans
    (heq.trans (D.pairOrbitSL3_eq_prod_upperPiecePoint hAdj x e hh')))
  have hc : ∀ c : Fin 3, D.upperPiecePoint hAdj x e
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 1 2)
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 0 2)
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 0 1) (e ⟨a, ha⟩) c =
    D.upperPiecePoint hAdj x e
      (fun l => (h' (e.symm l) : Matrix (Fin 3) (Fin 3) k) 1 2)
      (fun l => (h' (e.symm l) : Matrix (Fin 3) (Fin 3) k) 0 2)
      (fun l => (h' (e.symm l) : Matrix (Fin 3) (Fin 3) k) 0 1) (e ⟨a, ha⟩) c := by
    intro c
    have := congrArg (fun Y : (k' : Fin (n * 3)) → Langlands.Geometry.Building.rootGroupPoints
      p.inclusion (D.upperPieceEnum e k') => (Y (finProdFinEquiv (e ⟨a, ha⟩, c)) :
        rationalPoints G)) hy
    simpa only [y, y', Equiv.symm_apply_apply] using this
  have hr : (e.symm (e ⟨a, ha⟩) : p.base.support) = a := by simp
  obtain ⟨hab, hba⟩ := D.pairing _ (D.mem_of_mem_orientation ha)
  have e0 := hc 0
  have e1 := hc 1
  have e2 := hc 2
  simp only [upperPiecePoint, Equiv.symm_apply_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2
  rw [pairSL3_right_upper hAdj x hab hba, pairSL3_right_upper hAdj x hab hba, rankData_xp,
    rankData_xp] at e0
  rw [pairSL3_left_upper hAdj x hab hba, pairSL3_left_upper hAdj x hab hba, rankData_xp,
    rankData_xp] at e2
  have f0 := (x _).toRootParametrization.rationalPoint_injective e0
  have f1 := pairSL3_cornerUpper_injective hAdj x hab hba e1
  have f2 := (x _).toRootParametrization.rationalPoint_injective e2
  rw [eq_upperTriple (hh a (D.mem_of_mem_orientation ha)),
    eq_upperTriple (hh' a (D.mem_of_mem_orientation ha)), f0, f1, f2]

end UpperPieces

section LowerPieces

variable {n : ℕ} (e : D.orientation ≃ Fin n)

/-- The negated roots of the pieces, ordered `-r, -(r + π r), -π r` inside the piece of
`r`. -/
def lowerPieceRoot (l : Fin n) (c : Fin 3) : characterLattice p.torus :=
  ![-p.rootDatum.root ((e.symm l : D.orientation) : p.base.support),
    -(p.rootDatum.root ((e.symm l : D.orientation) : p.base.support) +
      p.rootDatum.root (D.partner (e.symm l))),
    -p.rootDatum.root (D.partner (e.symm l))] c

/-- The roots of the pieces along `Fin (n * 3)`. -/
def lowerPieceEnum (k' : Fin (n * 3)) : characterLattice p.torus :=
  D.lowerPieceRoot e (finProdFinEquiv.symm k').1 (finProdFinEquiv.symm k').2

theorem lowerPieceEnum_finProd (l : Fin n) (c : Fin 3) :
    D.lowerPieceEnum e (finProdFinEquiv (l, c)) = D.lowerPieceRoot e l c := by
  simp [lowerPieceEnum]

/-- The three root-group factors of the lower piece of `r` with entries `v, w, u`. -/
def lowerPiecePoint (v w u : Fin n → k) (l : Fin n) (c : Fin 3) : rationalPoints G :=
  ![pairSL3 hAdj x (e.symm l) (D.partner (e.symm l)) (TernaryPresentation.left (lower (v l))),
    pairSL3 hAdj x (e.symm l) (D.partner (e.symm l)) (cornerLower (w l)),
    pairSL3 hAdj x (e.symm l) (D.partner (e.symm l)) (TernaryPresentation.right (lower (u l)))] c

variable [LocallyOfFiniteType G.X.hom] in
theorem lowerPiecePoint_mem (v w u : Fin n → k) (l : Fin n) (c : Fin 3) :
    D.lowerPiecePoint hAdj x e v w u l c ∈
      Langlands.Geometry.Building.rootGroupPoints p.inclusion (D.lowerPieceRoot e l c) := by
  have hr := D.mem_of_mem_orientation (e.symm l).2
  obtain ⟨hab, hba⟩ := D.pairing _ hr
  fin_cases c
  · change pairSL3 hAdj x (e.symm l) (D.partner (e.symm l))
        (TernaryPresentation.left (lower (v l))) ∈
      Langlands.Geometry.Building.rootGroupPoints p.inclusion
        (-p.rootDatum.root ((e.symm l : D.orientation) : p.base.support))
    rw [pairSL3_left_lower hAdj x hab hba, rankData_xm]
    exact (x _).linked.xmPoint_mem _
  · exact pairSL3_cornerLower_mem hAdj x hab hba _
  · change pairSL3 hAdj x (e.symm l) (D.partner (e.symm l))
        (TernaryPresentation.right (lower (u l))) ∈
      Langlands.Geometry.Building.rootGroupPoints p.inclusion
        (-p.rootDatum.root (D.partner (e.symm l)))
    rw [pairSL3_right_lower hAdj x hab hba, rankData_xm]
    exact (x _).linked.xmPoint_mem _

theorem prod_lowerPiecePoint (v w u : Fin n → k) :
    (List.ofFn fun k' : Fin (n * 3) => D.lowerPiecePoint hAdj x e v w u
        (finProdFinEquiv.symm k').1 (finProdFinEquiv.symm k').2).prod =
      (List.ofFn fun l => pairSL3 hAdj x (e.symm l) (D.partner (e.symm l))
        (TernaryPresentation.left (lower (v l)) * cornerLower (w l) *
          TernaryPresentation.right (lower (u l)))).prod := by
  rw [Langlands.Geometry.Building.list_ofFn_prod_finProd]
  congr 1
  apply List.ofFn_inj.mpr
  funext l
  simp only [Equiv.symm_apply_apply, map_mul]
  rfl

/-- The product over the orientation of an lower family is the ordered product of the
root-group factors of its pieces. -/
theorem pairOrbitSL3_eq_prod_lowerPiecePoint {h : p.base.support → SL3 k}
    (hh : ∀ a ∈ O, IsLowerSL3 (h a)) :
    D.pairOrbitSL3 hAdj x h = (List.ofFn fun k' : Fin (n * 3) => D.lowerPiecePoint hAdj x e
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 1 0)
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 2 0)
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 2 1)
      (finProdFinEquiv.symm k').1 (finProdFinEquiv.symm k').2).prod := by
  rw [prod_lowerPiecePoint, D.pairOrbitSL3_eq_prod_ofFn hAdj x e]
  congr 1
  apply List.ofFn_inj.mpr
  funext l
  rw [← eq_lowerTriple (hh _ (D.mem_of_mem_orientation (e.symm l).2))]

variable (U : Subgroup (rationalPoints G))

variable [LocallyOfFiniteType G.X.hom] in
/-- **Membership.** Products of lower families lie in a subgroup that is the ordered product of
the root groups of the pieces. -/
theorem pairOrbitSL3_mem_of_isLower
    (hU : ∀ g, g ∈ U ↔ ∃ y : (k' : Fin (n * 3)) → Langlands.Geometry.Building.rootGroupPoints
        p.inclusion (D.lowerPieceEnum e k'),
      g = (List.ofFn fun k' => (y k' : rationalPoints G)).prod)
    (h : p.base.support → SL3 k) (hh : ∀ a ∈ O, IsLowerSL3 (h a)) :
    D.pairOrbitSL3 hAdj x h ∈ U := by
  rw [hU]
  refine ⟨fun k' => ⟨D.lowerPiecePoint hAdj x e
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 1 0)
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 2 0)
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 2 1)
      (finProdFinEquiv.symm k').1 (finProdFinEquiv.symm k').2,
    D.lowerPiecePoint_mem hAdj x e _ _ _ _ _⟩, ?_⟩
  exact D.pairOrbitSL3_eq_prod_lowerPiecePoint hAdj x e hh

variable [LocallyOfFiniteType G.X.hom] in
/-- **Products.** Every member of such a subgroup is the product of an lower pair family. -/
theorem exists_isLower_pairOrbitSL3_eq
    (hU : ∀ g, g ∈ U ↔ ∃ y : (k' : Fin (n * 3)) → Langlands.Geometry.Building.rootGroupPoints
        p.inclusion (D.lowerPieceEnum e k'),
      g = (List.ofFn fun k' => (y k' : rationalPoints G)).prod)
    {g : rationalPoints G} (hg : g ∈ U) :
    ∃ h : p.base.support → SL3 k, (∀ a ∈ O, IsLowerSL3 (h a)) ∧ D.IsPairFamily h ∧
      D.pairOrbitSL3 hAdj x h = g := by
  classical
  obtain ⟨y, rfl⟩ := (hU g).mp hg
  have key : ∀ (l : Fin n) (c : Fin 3), (y (finProdFinEquiv (l, c)) : rationalPoints G) ∈
      Langlands.Geometry.Building.rootGroupPoints p.inclusion (D.lowerPieceRoot e l c) :=
    fun l c => D.lowerPieceEnum_finProd e l c ▸ (y (finProdFinEquiv (l, c))).2
  have h0 : ∀ l, ∃ t : k, pairSL3 hAdj x (e.symm l) (D.partner (e.symm l))
      (TernaryPresentation.left (lower t)) = y (finProdFinEquiv (l, 0)) := by
    intro l
    obtain ⟨hab, hba⟩ := D.pairing _ (D.mem_of_mem_orientation (e.symm l).2)
    obtain ⟨t, ht⟩ := (x ((e.symm l : D.orientation) : p.base.support)).linked.exists_xmPoint_eq
      (key l 0)
    exact ⟨t, by rw [pairSL3_left_lower hAdj x hab hba, rankData_xm]; exact ht⟩
  have h1 : ∀ l, ∃ t : k, pairSL3 hAdj x (e.symm l) (D.partner (e.symm l))
      (cornerLower t) = y (finProdFinEquiv (l, 1)) := by
    intro l
    obtain ⟨hab, hba⟩ := D.pairing _ (D.mem_of_mem_orientation (e.symm l).2)
    exact exists_pairSL3_cornerLower_eq hAdj x hab hba (key l 1)
  have h2 : ∀ l, ∃ t : k, pairSL3 hAdj x (e.symm l) (D.partner (e.symm l))
      (TernaryPresentation.right (lower t)) = y (finProdFinEquiv (l, 2)) := by
    intro l
    obtain ⟨hab, hba⟩ := D.pairing _ (D.mem_of_mem_orientation (e.symm l).2)
    obtain ⟨t, ht⟩ := (x (D.partner (e.symm l))).linked.exists_xmPoint_eq (key l 2)
    exact ⟨t, by rw [pairSL3_right_lower hAdj x hab hba, rankData_xm]; exact ht⟩
  choose v hv using h0
  choose w hw using h1
  choose u hu using h2
  let M : p.base.support → SL3 k := fun a => if ha : a ∈ D.orientation then
    TernaryPresentation.left (lower (v (e ⟨a, ha⟩))) * cornerLower (w (e ⟨a, ha⟩)) *
      TernaryPresentation.right (lower (u (e ⟨a, ha⟩))) else 1
  have hM : ∀ l, M (e.symm l) = TernaryPresentation.left (lower (v l)) * cornerLower (w l) *
      TernaryPresentation.right (lower (u l)) := by
    intro l
    simp only [M]
    rw [dite_eq_left (e.symm l).2]
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
  refine ⟨D.pairExtend M, D.pairExtend_prop IsLowerSL3 (fun g hg => isLowerSL3_outer hg)
    (fun a ha => ?_), D.isPairFamily_pairExtend M, ?_⟩
  · have hMa : M a = TernaryPresentation.left (lower (v (e ⟨a, ha⟩))) *
        cornerLower (w (e ⟨a, ha⟩)) * TernaryPresentation.right (lower (u (e ⟨a, ha⟩))) := by
      simp only [M]
      rw [dite_eq_left ha]
    rw [hMa]
    exact isLowerSL3_lowerTriple _ _ _
  · rw [pairOrbitSL3_pairExtend, D.pairOrbitSL3_eq_prod_ofFn hAdj x e,
      Langlands.Geometry.Building.list_ofFn_prod_finProd]
    congr 1
    apply List.ofFn_inj.mpr
    funext l
    rw [hM, map_mul, map_mul, hv l, hw l, hu l]

/-- **Uniqueness.** Lower pair families with the same product agree on `O`, when the ordered
products of root-group points of the pieces are unique. -/
theorem eq_of_isLower_pairOrbitSL3_eq [LocallyOfFiniteType G.X.hom]
    (hU' : ∀ y y' : (k' : Fin (n * 3)) → Langlands.Geometry.Building.rootGroupPoints
        p.inclusion (D.lowerPieceEnum e k'),
      (List.ofFn fun k' => (y k' : rationalPoints G)).prod =
        (List.ofFn fun k' => (y' k' : rationalPoints G)).prod → y = y')
    (h h' : p.base.support → SL3 k) (hh : ∀ a ∈ O, IsLowerSL3 (h a))
    (hh' : ∀ a ∈ O, IsLowerSL3 (h' a)) (hp : D.IsPairFamily h) (hp' : D.IsPairFamily h')
    (heq : D.pairOrbitSL3 hAdj x h = D.pairOrbitSL3 hAdj x h') : ∀ a ∈ O, h a = h' a := by
  apply D.eq_of_eq_on_orientation hp hp'
  intro a ha
  let y : (k' : Fin (n * 3)) → Langlands.Geometry.Building.rootGroupPoints p.inclusion
      (D.lowerPieceEnum e k') := fun k' => ⟨D.lowerPiecePoint hAdj x e
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 1 0)
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 2 0)
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 2 1)
      (finProdFinEquiv.symm k').1 (finProdFinEquiv.symm k').2,
    D.lowerPiecePoint_mem hAdj x e _ _ _ _ _⟩
  let y' : (k' : Fin (n * 3)) → Langlands.Geometry.Building.rootGroupPoints p.inclusion
      (D.lowerPieceEnum e k') := fun k' => ⟨D.lowerPiecePoint hAdj x e
      (fun l => (h' (e.symm l) : Matrix (Fin 3) (Fin 3) k) 1 0)
      (fun l => (h' (e.symm l) : Matrix (Fin 3) (Fin 3) k) 2 0)
      (fun l => (h' (e.symm l) : Matrix (Fin 3) (Fin 3) k) 2 1)
      (finProdFinEquiv.symm k').1 (finProdFinEquiv.symm k').2,
    D.lowerPiecePoint_mem hAdj x e _ _ _ _ _⟩
  have hy : y = y' := hU' y y' ((D.pairOrbitSL3_eq_prod_lowerPiecePoint hAdj x e hh).symm.trans
    (heq.trans (D.pairOrbitSL3_eq_prod_lowerPiecePoint hAdj x e hh')))
  have hc : ∀ c : Fin 3, D.lowerPiecePoint hAdj x e
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 1 0)
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 2 0)
      (fun l => (h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 2 1) (e ⟨a, ha⟩) c =
    D.lowerPiecePoint hAdj x e
      (fun l => (h' (e.symm l) : Matrix (Fin 3) (Fin 3) k) 1 0)
      (fun l => (h' (e.symm l) : Matrix (Fin 3) (Fin 3) k) 2 0)
      (fun l => (h' (e.symm l) : Matrix (Fin 3) (Fin 3) k) 2 1) (e ⟨a, ha⟩) c := by
    intro c
    have := congrArg (fun Y : (k' : Fin (n * 3)) → Langlands.Geometry.Building.rootGroupPoints
      p.inclusion (D.lowerPieceEnum e k') => (Y (finProdFinEquiv (e ⟨a, ha⟩, c)) :
        rationalPoints G)) hy
    simpa only [y, y', Equiv.symm_apply_apply] using this
  have hr : (e.symm (e ⟨a, ha⟩) : p.base.support) = a := by simp
  obtain ⟨hab, hba⟩ := D.pairing _ (D.mem_of_mem_orientation ha)
  have e0 := hc 0
  have e1 := hc 1
  have e2 := hc 2
  simp only [lowerPiecePoint, Equiv.symm_apply_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e0 e1 e2
  rw [pairSL3_left_lower hAdj x hab hba, pairSL3_left_lower hAdj x hab hba, rankData_xm,
    rankData_xm] at e0
  rw [pairSL3_right_lower hAdj x hab hba, pairSL3_right_lower hAdj x hab hba, rankData_xm,
    rankData_xm] at e2
  have f0 := (x _).linked.xmPoint_injective e0
  have f1 := pairSL3_cornerLower_injective hAdj x hab hba e1
  have f2 := (x _).linked.xmPoint_injective e2
  rw [eq_lowerTriple (hh a (D.mem_of_mem_orientation ha)),
    eq_lowerTriple (hh' a (D.mem_of_mem_orientation ha)), f0, f1, f2]

end LowerPieces

section DoublePieces

variable {n : ℕ} (e : D.orientation ≃ Fin n) (U : Subgroup (rationalPoints G))

/-- The sum of the roots of the piece of `r`. -/
def doubleRoot (l : Fin n) : characterLattice p.torus :=
  p.rootDatum.root ((e.symm l : D.orientation) : p.base.support) +
    p.rootDatum.root (D.partner (e.symm l))

variable [LocallyOfFiniteType G.X.hom]

/-- **Membership.** Products of central upper families lie in a subgroup that is the ordered
product of the root groups of the sums of the pieces. -/
theorem pairOrbitSL3_mem_of_isCentralUpper
    (hU : ∀ g, g ∈ U ↔ ∃ y : (l : Fin n) → Langlands.Geometry.Building.rootGroupPoints
        p.inclusion (D.doubleRoot e l),
      g = (List.ofFn fun l => (y l : rationalPoints G)).prod)
    (h : p.base.support → SL3 k) (hh : ∀ a ∈ O, IsCentralUpperSL3 (h a)) :
    D.pairOrbitSL3 hAdj x h ∈ U := by
  rw [hU]
  refine ⟨fun l => ⟨pairSL3 hAdj x (e.symm l) (D.partner (e.symm l))
      (cornerUpper ((h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 0 2)), by
    obtain ⟨hab, hba⟩ := D.pairing _ (D.mem_of_mem_orientation (e.symm l).2)
    exact pairSL3_cornerUpper_mem hAdj x hab hba _⟩, ?_⟩
  rw [D.pairOrbitSL3_eq_prod_ofFn hAdj x e]
  congr 1
  apply List.ofFn_inj.mpr
  funext l
  exact congrArg _ (eq_cornerUpper (hh _ (D.mem_of_mem_orientation (e.symm l).2)))

/-- **Products.** Every member of such a subgroup is the product of a central upper pair
family. -/
theorem exists_isCentralUpper_pairOrbitSL3_eq
    (hU : ∀ g, g ∈ U ↔ ∃ y : (l : Fin n) → Langlands.Geometry.Building.rootGroupPoints
        p.inclusion (D.doubleRoot e l),
      g = (List.ofFn fun l => (y l : rationalPoints G)).prod)
    {g : rationalPoints G} (hg : g ∈ U) :
    ∃ h : p.base.support → SL3 k, (∀ a ∈ O, IsCentralUpperSL3 (h a)) ∧ D.IsPairFamily h ∧
      D.pairOrbitSL3 hAdj x h = g := by
  classical
  obtain ⟨y, rfl⟩ := (hU g).mp hg
  have h1 : ∀ l, ∃ t : k, pairSL3 hAdj x (e.symm l) (D.partner (e.symm l))
      (cornerUpper t) = y l := by
    intro l
    obtain ⟨hab, hba⟩ := D.pairing _ (D.mem_of_mem_orientation (e.symm l).2)
    exact exists_pairSL3_cornerUpper_eq hAdj x hab hba (y l).2
  choose w hw using h1
  let M : p.base.support → SL3 k := fun a => if ha : a ∈ D.orientation then
    cornerUpper (w (e ⟨a, ha⟩)) else 1
  have hM : ∀ l, M (e.symm l) = cornerUpper (w l) := by
    intro l
    simp only [M]
    rw [dite_eq_left (e.symm l).2]
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
  refine ⟨D.pairExtend M, D.pairExtend_prop IsCentralUpperSL3
    (fun g hg => isCentralUpperSL3_outer hg) (fun a ha => ?_), D.isPairFamily_pairExtend M, ?_⟩
  · simp only [M]
    rw [dite_eq_left ha]
    exact isCentralUpperSL3_cornerUpper _
  · rw [pairOrbitSL3_pairExtend, D.pairOrbitSL3_eq_prod_ofFn hAdj x e]
    congr 1
    apply List.ofFn_inj.mpr
    funext l
    rw [hM, hw l]

/-- **Membership.** Products of central lower families lie in a subgroup that is the ordered
product of the root groups of the negated sums of the pieces. -/
theorem pairOrbitSL3_mem_of_isCentralLower
    (hU : ∀ g, g ∈ U ↔ ∃ y : (l : Fin n) → Langlands.Geometry.Building.rootGroupPoints
        p.inclusion (-D.doubleRoot e l),
      g = (List.ofFn fun l => (y l : rationalPoints G)).prod)
    (h : p.base.support → SL3 k) (hh : ∀ a ∈ O, IsCentralLowerSL3 (h a)) :
    D.pairOrbitSL3 hAdj x h ∈ U := by
  rw [hU]
  refine ⟨fun l => ⟨pairSL3 hAdj x (e.symm l) (D.partner (e.symm l))
      (cornerLower ((h (e.symm l) : Matrix (Fin 3) (Fin 3) k) 2 0)), by
    obtain ⟨hab, hba⟩ := D.pairing _ (D.mem_of_mem_orientation (e.symm l).2)
    exact pairSL3_cornerLower_mem hAdj x hab hba _⟩, ?_⟩
  rw [D.pairOrbitSL3_eq_prod_ofFn hAdj x e]
  congr 1
  apply List.ofFn_inj.mpr
  funext l
  exact congrArg _ (eq_cornerLower (hh _ (D.mem_of_mem_orientation (e.symm l).2)))

/-- **Products.** Every member of such a subgroup is the product of a central lower pair
family. -/
theorem exists_isCentralLower_pairOrbitSL3_eq
    (hU : ∀ g, g ∈ U ↔ ∃ y : (l : Fin n) → Langlands.Geometry.Building.rootGroupPoints
        p.inclusion (-D.doubleRoot e l),
      g = (List.ofFn fun l => (y l : rationalPoints G)).prod)
    {g : rationalPoints G} (hg : g ∈ U) :
    ∃ h : p.base.support → SL3 k, (∀ a ∈ O, IsCentralLowerSL3 (h a)) ∧ D.IsPairFamily h ∧
      D.pairOrbitSL3 hAdj x h = g := by
  classical
  obtain ⟨y, rfl⟩ := (hU g).mp hg
  have h1 : ∀ l, ∃ t : k, pairSL3 hAdj x (e.symm l) (D.partner (e.symm l))
      (cornerLower t) = y l := by
    intro l
    obtain ⟨hab, hba⟩ := D.pairing _ (D.mem_of_mem_orientation (e.symm l).2)
    exact exists_pairSL3_cornerLower_eq hAdj x hab hba (y l).2
  choose w hw using h1
  let M : p.base.support → SL3 k := fun a => if ha : a ∈ D.orientation then
    cornerLower (w (e ⟨a, ha⟩)) else 1
  have hM : ∀ l, M (e.symm l) = cornerLower (w l) := by
    intro l
    simp only [M]
    rw [dite_eq_left (e.symm l).2]
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
  refine ⟨D.pairExtend M, D.pairExtend_prop IsCentralLowerSL3
    (fun g hg => isCentralLowerSL3_outer hg) (fun a ha => ?_), D.isPairFamily_pairExtend M, ?_⟩
  · simp only [M]
    rw [dite_eq_left ha]
    exact isCentralLowerSL3_cornerLower _
  · rw [pairOrbitSL3_pairExtend, D.pairOrbitSL3_eq_prod_ofFn hAdj x e]
    congr 1
    apply List.ofFn_inj.mpr
    funext l
    rw [hM, hw l]

end DoublePieces

section TorusWeyl

theorem pairOrbitSL3_gramSL3_mem :
    D.pairOrbitSL3 hAdj x (fun _ => gramSL3) ∈ normalizerPoints p.inclusion := by
  rw [pairOrbitSL3_apply]
  apply Subgroup.noncommProd_mem
  intro r _
  obtain ⟨hab, hba⟩ := D.pairing _ (D.mem_of_mem_orientation r.2)
  exact pairSL3_gramSL3_mem hAdj x hab hba

/-- A product over `O` is the product over the orientation of the products over the pairs. -/
theorem prod_eq_prod_orientation [Fintype O] {M : Type*} [CommMonoid M]
    (f : p.base.support → M) :
    ∏ b : O, f b = ∏ r : D.orientation, (f r * f (D.partner r)) := by
  classical
  let φ : D.orientation ⊕ D.orientation → O := Sum.elim
    (fun r => ⟨r, D.mem_of_mem_orientation r.2⟩)
    (fun r => ⟨D.partner r, D.mem _ (D.mem_of_mem_orientation r.2)⟩)
  have hφ : Function.Bijective φ := by
    refine ⟨?_, ?_⟩
    · rintro (r | r) (r' | r') h
      · have h' := congrArg Subtype.val h
        exact congrArg Sum.inl (Subtype.ext h')
      · have h' := congrArg Subtype.val h
        change (r : p.base.support) = D.partner r' at h'
        exact absurd (h' ▸ r.2)
          ((D.mem_orientation_iff (D.mem_of_mem_orientation r'.2)).mp r'.2)
      · have h' := congrArg Subtype.val h
        change D.partner (r : p.base.support) = r' at h'
        exact absurd (h' ▸ r'.2)
          ((D.mem_orientation_iff (D.mem_of_mem_orientation r.2)).mp r.2)
      · have h' := congrArg Subtype.val h
        change D.partner (r : p.base.support) = D.partner r' at h'
        have h'' : (r : p.base.support) = r' := by
          rw [← D.partner_partner _ (D.mem_of_mem_orientation r.2), h',
            D.partner_partner _ (D.mem_of_mem_orientation r'.2)]
        exact congrArg Sum.inr (Subtype.ext h'')
    · rintro ⟨b, hb⟩
      by_cases h : b ∈ D.orientation
      · exact ⟨Sum.inl ⟨b, h⟩, rfl⟩
      · refine ⟨Sum.inr ⟨D.partner b, D.partner_mem_orientation hb h⟩, ?_⟩
        exact Subtype.ext (D.partner_partner b hb)
  rw [← Fintype.prod_equiv (Equiv.ofBijective φ hφ) (fun z => f (φ z)) (fun b : O => f b)
    (fun _ => rfl), Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The product over the orientation of the diagonal pairs is the image of the product of the
simple-coroot points over `O`. -/
theorem pairOrbitSL3_diag [Fintype O] (t : p.base.support → kˣ) :
    D.pairOrbitSL3 hAdj x (fun a => TernaryPresentation.left (diag (t a)) *
      TernaryPresentation.right (diag (t (D.partner a)))) =
      rationalPoints.map p.inclusion (∏ b : O, p.simpleCorootPoint b (t b)) := by
  rw [D.prod_eq_prod_orientation (fun b => p.simpleCorootPoint b (t b)),
    ← Finset.noncommProd_eq_prod, Finset.map_noncommProd, pairOrbitSL3_apply]
  congr 1
  funext r
  obtain ⟨hab, hba⟩ := D.pairing _ (D.mem_of_mem_orientation r.2)
  exact pairSL3_left_diag_mul_right_diag hAdj x hab hba _ _

end TorusWeyl

end PartnerData

end Split

section Galois

open GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G)

local instance partnerOrbitRootProductsIsAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (hAdj : AdjacentSimpleRootSpecialLinearStatement.{u})
    (p : Langlands.GroupScheme.SplitPinning
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map i)
    (x : p.NormalizedSimpleRootParametrizations)
    {ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support}
    (hx : RootMapsGaloisCompatible k K p x ρ)
    (hroot : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
      characterLattice.congr eT (p.rootDatum.root (ρ σ a)) =
        characterLattice.galoisRepresentation k K T σ
          (characterLattice.congr eT (p.rootDatum.root a)))
    (hρpair : ∀ (σ : K ≃ₐ[k] K) (a b : p.base.support),
      p.rootDatum.pairing (ρ σ a) (ρ σ b) = p.rootDatum.pairing a b)
    {O : Set p.base.support} (D : PartnerData O)
    (hOs : ∀ (σ : K ≃ₐ[k] K) a, a ∈ O ↔ ρ σ a ∈ O)
    (hπρ : ∀ (σ : K ≃ₐ[k] K), ∀ a ∈ O, D.partner (ρ σ a) = ρ σ (D.partner a))
    {L : Type u} [Field L] [Algebra k L] (τ : p.base.support → (L →ₐ[k] K))
    (hτ : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support), a ∈ O → τ (ρ σ a) = σ.toAlgHom.comp (τ a))
    (c : SU3Root.RingInvolution L)
    (hτc : ∀ a ∈ O, ∀ y : L, τ (D.partner a) y = τ a (c.bar y))
    [FiniteDimensional k K] [IsGalois k K]

set_option hygiene false in
local notation "URho" => unitaryRho k K i hAdj p eT hT x hx hroot hρpair D hOs hπρ τ hτ c hτc

/-- The image of the antidiagonal Weyl element normalizes `i`. -/
theorem unitaryRho_weylElement_mem [Mono i.hom.hom.left] :
    URho ⟨SU3Root.weylElement, SU3Root.weylElement_mem_specialUnitarySubgroup c⟩ ∈
      normalizerPoints i := by
  apply (mem_normalizerPoints_rationalExtend_iff (K := K) i _).mp
  rw [rationalExtend_unitaryRho]
  have hw : (fun a => Matrix.SpecialLinearGroup.map (τ a).toRingHom
      ((SU3Root.fixedSpecialUnitaryEquiv c).symm
        ⟨SU3Root.weylElement, SU3Root.weylElement_mem_specialUnitarySubgroup c⟩).1) =
      fun _ => gramSL3 := by
    funext a
    have h1 : ((SU3Root.fixedSpecialUnitaryEquiv c).symm
        ⟨SU3Root.weylElement, SU3Root.weylElement_mem_specialUnitarySubgroup c⟩).1 =
        (gramSL3 : SL3 L) := Subtype.ext rfl
    rw [h1, map_gramSL3]
  rw [hw]
  exact mem_normalizerPoints_baseChange_of_pinning k K i p eT hT
    (D.pairOrbitSL3_gramSL3_mem hAdj x)

/-- The scalar extension of the image of the diagonal torus element `diag(t, t̄/t, 1/t̄)` is
the image of the product of the simple-coroot points `α_b^∨(τ_b t)` over `O`. -/
theorem rationalExtend_unitaryRho_diagonal [Fintype O] (t : Lˣ) :
    rationalExtend k K G (URho ⟨SU3Root.diagonal c t,
      SU3Root.diagonal_mem_specialUnitarySubgroup c t⟩) =
      rationalPoints.map p.inclusion
        (∏ b : O, p.simpleCorootPoint b (Units.map (τ b).toRingHom.toMonoidHom t)) := by
  rw [rationalExtend_unitaryRho, ← D.pairOrbitSL3_diag hAdj x
    (fun a => Units.map (τ a).toRingHom.toMonoidHom t)]
  apply PartnerData.pairOrbitSL3_congr
  intro a ha
  have hb : τ a (c.bar (t : L)) = τ (D.partner a) (t : L) := (hτc a ha _).symm
  ext r s
  rw [coe_left_diag_mul_right_diag, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply]
  change (τ a).toRingHom ((SU3Root.diagonal c t : Matrix (Fin 3) (Fin 3) L) r s) = _
  rw [SU3Root.diagonal_val]
  fin_cases r <;> fin_cases s <;>
    simp [Units.val_inv_eq_inv_val, map_inv₀, hb, mul_comm]

end Galois

end SplitPinning

end Langlands.GroupScheme
