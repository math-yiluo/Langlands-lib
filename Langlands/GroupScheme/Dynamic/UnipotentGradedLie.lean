import Langlands.GroupScheme.Dynamic.UnipotentGradedTopology
import Langlands.GroupScheme.Dynamic.CentralizerAdjointAction
import Langlands.GroupScheme.Lie.ActionDeterminant

/-! # The adjoint determinant on a dynamic unipotent Lie algebra in graded coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic.GradedCoordinates

open Corepresented

section DualNumbers

variable {k : Type u} [Field k]

/-- Evaluation of a polynomial at a vector of pure infinitesimals keeps the constant and the
linear terms only. -/
theorem aeval_inr {J : Type*} [Fintype J] [DecidableEq J] (w : J → k) (p : MvPolynomial J k) :
    aeval (fun j => (TrivSqZeroExt.inr (w j) : DualNumber k)) p =
      algebraMap k (DualNumber k) (p.coeff 0) +
        TrivSqZeroExt.inr (∑ j, p.coeff (Finsupp.single j 1) * w j) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : ∀ j : J, (C a : MvPolynomial J k).coeff (Finsupp.single j 1) = 0 := fun j => by
      rw [coeff_C, ite_eq_right_iff]
      intro h
      exact absurd h.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
    have h0 : (C a : MvPolynomial J k).coeff 0 = a := by
      rw [coeff_C, ite_eq_left_iff]
      intro h
      exact absurd rfl h
    rw [aeval_C, h0]
    simp [h]
  | add p q hp hq =>
    rw [map_add, hp, hq]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, RingHom.map_add, add_mul,
      Finset.sum_add_distrib, TrivSqZeroExt.inr_add]
    abel
  | mul_X p i hp =>
    have h0 : (p * X i).coeff 0 = 0 := by
      rw [coeff_mul_X']
      simp
    have h1 : ∀ j, (p * X i).coeff (Finsupp.single j 1) = if j = i then p.coeff 0 else 0 := by
      intro j
      rw [coeff_mul_X']
      by_cases hji : j = i
      · subst hji
        simp
      · have hi : i ∉ (Finsupp.single j 1).support := by
          simpa [eq_comm] using hji
        simp only [hi, hji, ite_false]
    have hsum : ∑ j, (p * X i).coeff (Finsupp.single j 1) * w j = p.coeff 0 * w i := by
      simp only [h1, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hsum, h0, map_mul, hp, aeval_X, add_mul, TrivSqZeroExt.inr_mul_inr, add_zero,
      RingHom.map_zero, zero_add, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      ← TrivSqZeroExt.inr_smul, smul_eq_mul]

end DualNumbers

section LieCoordinates

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  {U : GroupScheme (Spec (CommRingCat.of k))} {iU : U ⟶ G}
  (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)

/-- The dual numbers over `k` as a test algebra. -/
abbrev dualTest (k : Type u) [Field k] : CommAlgCat.{u} (CommRingCat.of k) :=
  CommAlgCat.of (CommRingCat.of k) (DualNumber k)

/-- The base field as a test algebra. -/
abbrev baseTest (k : Type u) [Field k] : CommAlgCat.{u} (CommRingCat.of k) :=
  CommAlgCat.of (CommRingCat.of k) k

/-- The cut functor of the first cyclic weight subgroup of conjugation through `χ`. -/
abbrev unipotentCut :=
  cutFunctor (isCutOutBy_weightIdeal (AffineCoordinates.corepresentation G)
    (cocharModelAction G χ) (Corepresented.cyclicTail (idExponent (k := k)) 1))

/-- The corepresentation of that cut functor by the quotient algebra. -/
abbrev unipotentCorep :=
  weightCorep (AffineCoordinates.corepresentation G) (cocharModelAction G χ)
    (Corepresented.cyclicTail (idExponent (k := k)) 1)

/-- The point of the first cyclic weight subgroup of the model given by a dual-number point of a
representative of the dynamic unipotent subgroup. -/
def lieCutPoint (y : Lie.AffinePoints U (DualNumber k)) : (unipotentCut G χ).obj (dualTest k) :=
  ⟨modelPoint G (dualTest k) (y ≫ iU.hom.hom),
    (mem_unipotent_iff_modelPoint G χ _).1 (by
      rw [← hU.2]
      exact SubgroupFunctor.mem_range.2 ⟨y, rfl⟩)⟩

@[simp] theorem lieCutPoint_val (y : Lie.AffinePoints U (DualNumber k)) :
    (lieCutPoint G χ hU y).1 = modelPoint G (dualTest k) (y ≫ iU.hom.hom) := rfl

theorem lieCutPoint_mul (y y' : Lie.AffinePoints U (DualNumber k)) :
    lieCutPoint G χ hU (y * y') = lieCutPoint G χ hU y * lieCutPoint G χ hU y' := by
  apply Subtype.ext
  change modelPoint G (dualTest k) ((y * y') ≫ iU.hom.hom) =
    modelPoint G (dualTest k) (y ≫ iU.hom.hom) * modelPoint G (dualTest k) (y' ≫ iU.hom.hom)
  rw [MonObj.mul_comp, map_mul]

/-- Change of dual-number coefficients commutes with the construction. -/
theorem lieCutPoint_affineMap (f : DualNumber k →ₐ[CommRingCat.of k] DualNumber k)
    (y : Lie.AffinePoints U (DualNumber k)) :
    lieCutPoint G χ hU (Lie.affineMap U f y) =
      (unipotentCut G χ).map (CommAlgCat.ofHom f) (lieCutPoint G χ hU y) := by
  apply Subtype.ext
  change modelPoint G (dualTest k) (Lie.affineMap U f y ≫ iU.hom.hom) =
    (AffineCoordinates.functor G).map (CommAlgCat.ofHom f)
      (modelPoint G (dualTest k) (y ≫ iU.hom.hom))
  rw [Lie.affineMap_apply, Category.assoc, modelPoint_naturality]

/-- The reduction of the cut point of a Lie kernel element is the identity. -/
theorem lieCutPoint_reduction (ξ : lieKernel U k) :
    (unipotentCut G χ).map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom (CommRingCat.of k) k k))
      (lieCutPoint G χ hU ξ.val) = 1 := by
  apply Subtype.ext
  change (AffineCoordinates.functor G).map (CommAlgCat.ofHom (TrivSqZeroExt.fstHom _ k k))
      (modelPoint G (dualTest k) (ξ.val ≫ iU.hom.hom)) = 1
  rw [← modelPoint_naturality, ← Category.assoc]
  have h : (algSpec (CommRingCat.of k)).map
      (CommAlgCat.ofHom (TrivSqZeroExt.fstHom (CommRingCat.of k) k k)).op ≫ ξ.val = 1 := ξ.property
  rw [h, MonObj.one_comp, map_one]

variable [IsAffineHom U.X.hom] {n : ℕ} {d : Fin n → ℕ}
  {x : Fin n → AffineCoordinates.algebra G ⧸ weightIdeal (AffineCoordinates.corepresentation G)
    (cocharModelAction G χ) (Corepresented.cyclicTail (idExponent (k := k)) 1)}
  (hd : ∀ i, 0 < d i)
  (hx : ∀ i, IsHomogeneous (weightCorep (AffineCoordinates.corepresentation G)
      (cocharModelAction G χ) (Corepresented.cyclicTail (idExponent (k := k)) 1))
    (weightAction (AffineCoordinates.corepresentation G) (cocharModelAction G χ)
      (Corepresented.cyclicTail (idExponent (k := k)) 1)) (d i • idExponent (k := k)) (x i))
  (hbij : Function.Bijective (aeval x : MvPolynomial (Fin n) k →ₐ[k]
    AffineCoordinates.algebra G ⧸ weightIdeal (AffineCoordinates.corepresentation G)
      (cocharModelAction G χ) (Corepresented.cyclicTail (idExponent (k := k)) 1)))

omit [IsAffineHom U.X.hom] in
include hd hx in
/-- The reduction of a coordinate of a Lie kernel element vanishes. -/
theorem fst_coord_lieCutPoint (ξ : lieKernel U k) (j : Fin n) :
    (coord (weightCorep (AffineCoordinates.corepresentation G) (cocharModelAction G χ)
      (Corepresented.cyclicTail (idExponent (k := k)) 1)) (lieCutPoint G χ hU ξ.val) (x j)).fst =
        0 := by
  have h := congrArg (fun u => coord (weightCorep (AffineCoordinates.corepresentation G)
    (cocharModelAction G χ) (Corepresented.cyclicTail (idExponent (k := k)) 1)) u (x j))
    (lieCutPoint_reduction G χ hU ξ)
  simp only [coord_map, AlgHom.comp_apply] at h
  rw [coord_one_of_isHomogeneous _ _ idExponent_ne_zero (hd j) (hx j)] at h
  exact h

variable (x) in
/-- The infinitesimal parts of the graded coordinates of Lie kernel elements. -/
def lieCoord (ξ : Additive (lieKernel U k)) : Fin n → k := fun j =>
  (coord (weightCorep (AffineCoordinates.corepresentation G) (cocharModelAction G χ)
    (Corepresented.cyclicTail (idExponent (k := k)) 1)) (lieCutPoint G χ hU ξ.toMul.val) (x j)).snd

omit [IsAffineHom U.X.hom] in
theorem lieCoord_add (ξ₁ ξ₂ : Additive (lieKernel U k)) :
    lieCoord G χ hU x (ξ₁ + ξ₂) = lieCoord G χ hU x ξ₁ + lieCoord G χ hU x ξ₂ := by
  funext j
  change (coord (unipotentCorep G χ) (lieCutPoint G χ hU (ξ₁.toMul.val * ξ₂.toMul.val))
    (x j)).snd = _
  rw [lieCutPoint_mul]
  have h1 := lieCutPoint_reduction G χ hU ξ₁.toMul
  have h2 := lieCutPoint_reduction G χ hU ξ₂.toMul
  exact snd_coord_mul (unipotentCorep G χ) (A := baseTest k) (z := lieCutPoint G χ hU ξ₁.toMul.val)
    (z' := lieCutPoint G χ hU ξ₂.toMul.val) h1 h2 (x j)

theorem lieCoord_smul (c : k) (ξ : Additive (lieKernel U k)) :
    lieCoord G χ hU x (c • ξ) = c • lieCoord G χ hU x ξ := by
  funext j
  change (coord (unipotentCorep G χ) (lieCutPoint G χ hU
    (Lie.affineMap U (GeneralLinear.DualNumber.epsilonScaleAlg (R := CommRingCat.of k) c)
      ξ.toMul.val)) (x j)).snd = c * _
  rw [lieCutPoint_affineMap, coord_map, AlgHom.comp_apply]
  exact GeneralLinear.DualNumber.epsilonScale_snd c _

/-- The Lie coordinates as a linear map. -/
def lieCoordLinear : Additive (lieKernel U k) →ₗ[k] (Fin n → k) where
  toFun := lieCoord G χ hU x
  map_add' := lieCoord_add G χ hU
  map_smul' := lieCoord_smul G χ hU

omit [IsAffineHom U.X.hom] in
include hd hx hbij in
/-- A Lie kernel element with vanishing Lie coordinates is trivial. -/
theorem lieCoord_injective : Function.Injective (lieCoord G χ hU x) := by
  have hzero : ∀ ξ : Additive (lieKernel U k), lieCoord G χ hU x ξ = 0 → ξ = 0 := by
    intro ξ hξ
    have hcut : lieCutPoint G χ hU ξ.toMul.val = 1 := by
      refine coord_eq_of_apply_eq (unipotentCorep G χ) hbij.2 fun j => ?_
      rw [coord_one_of_isHomogeneous _ _ idExponent_ne_zero (hd j) (hx j)]
      apply TrivSqZeroExt.ext
      · exact fst_coord_lieCutPoint G χ hU hd hx ξ.toMul j
      · exact congrFun hξ j
    have hmp : modelPoint G (dualTest k) (ξ.toMul.val ≫ iU.hom.hom) = 1 := congrArg Subtype.val hcut
    have hG1 : ξ.toMul.val ≫ iU.hom.hom = (1 : Lie.AffinePoints U (DualNumber k)) ≫ iU.hom.hom := by
      rw [MonObj.one_comp]
      apply modelPoint_injective G (dualTest k)
      rw [hmp, map_one]
    have : Mono iU.hom.hom := hU.1
    have hval : ξ.toMul.val = 1 := (cancel_mono iU.hom.hom).1 hG1
    exact congrArg Additive.ofMul (Subtype.ext hval)
  intro ξ₁ ξ₂ h
  have h' : lieCoord G χ hU x (ξ₁ - ξ₂) = 0 := by
    rw [sub_eq_add_neg, lieCoord_add, h, ← lieCoord_add, add_neg_cancel]
    funext j
    change (coord (unipotentCorep G χ) (lieCutPoint G χ hU 1) (x j)).snd = 0
    have h1 : lieCutPoint G χ hU 1 = 1 := by
      apply Subtype.ext
      change modelPoint G (dualTest k) ((1 : Lie.AffinePoints U (DualNumber k)) ≫ iU.hom.hom) = 1
      rw [MonObj.one_comp, map_one]
    rw [h1, coord_one_of_isHomogeneous _ _ idExponent_ne_zero (hd j) (hx j)]
    rfl
  exact sub_eq_zero.mp (hzero _ h')

omit [IsAffineHom U.X.hom] in
include hd hx hbij in
/-- Every vector is the Lie coordinate vector of a Lie kernel element. -/
theorem lieCoord_surjective : Function.Surjective (lieCoord G χ hU x) := by
  intro w
  obtain ⟨u, hu⟩ := exists_coord_eq (unipotentCorep G χ) hbij (A := dualTest k)
    (fun j => TrivSqZeroExt.inr (w j))
  have hg : (modelPointEquiv G (dualTest k)).symm u.1 ∈
      (Dynamic.unipotent χ).carrier ((algSpec (CommRingCat.of k)).obj (op (dualTest k))) := by
    rw [mem_unipotent_iff_modelPoint, modelPoint_modelPointEquiv_symm]
    exact u.2
  rw [← hU.2] at hg
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hg
  have : Mono iU.hom.hom := hU.1
  have hred : Lie.reduction U y = 1 := by
    apply (cancel_mono iU.hom.hom).1
    rw [MonObj.one_comp]
    apply modelPoint_injective G (baseTest k)
    rw [map_one]
    change modelPoint G (baseTest k) (((algSpec (CommRingCat.of k)).map
      (CommAlgCat.ofHom (TrivSqZeroExt.fstHom (CommRingCat.of k) k k)).op ≫ y) ≫ iU.hom.hom) = 1
    rw [Category.assoc, modelPoint_naturality, hy, modelPoint_modelPointEquiv_symm]
    have hcut : (unipotentCut G χ).map
        (CommAlgCat.ofHom (TrivSqZeroExt.fstHom (CommRingCat.of k) k k)) u = 1 := by
      refine coord_eq_of_apply_eq (unipotentCorep G χ) hbij.2 fun j => ?_
      rw [coord_map, AlgHom.comp_apply, hu,
        coord_one_of_isHomogeneous _ _ idExponent_ne_zero (hd j) (hx j)]
      rfl
    exact congrArg Subtype.val hcut
  refine ⟨Additive.ofMul ⟨y, hred⟩, ?_⟩
  funext j
  change (coord (unipotentCorep G χ) (lieCutPoint G χ hU y) (x j)).snd = w j
  have hyu : lieCutPoint G χ hU y = u := Subtype.ext (by
    change modelPoint G (dualTest k) (y ≫ iU.hom.hom) = u.1
    rw [hy, modelPoint_modelPointEquiv_symm])
  rw [hyu, hu]
  rfl

include hd hx hbij in
/-- The Lie coordinates as a linear equivalence. -/
def lieCoordEquiv : Additive (lieKernel U k) ≃ₗ[k] (Fin n → k) :=
  LinearEquiv.ofBijective (lieCoordLinear G χ hU (x := x))
    ⟨lieCoord_injective G χ hU hd hx hbij, lieCoord_surjective G χ hU hd hx hbij⟩

section Differential

variable {Z : GroupScheme (Spec (CommRingCat.of k))} {iZ : Z ⟶ G}
  (hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ)
  (m : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z.X)

omit [IsAffine G.X.left] [Smooth G.X.hom] [IsAffineHom G.X.hom] in
include hZ in
theorem mem_torusCentralizer_of_centralizer :
    m ≫ iZ.hom.hom ∈ (torusCentralizer χ).carrier _ := by
  rw [torusCentralizer_gm_eq_dynamicCentralizer, ← hZ.2]
  exact SubgroupFunctor.mem_range.2 ⟨m, rfl⟩

omit [IsAffineHom U.X.hom] in
/-- Differentiating the centralizer action is conjugation by the constant model point. -/
theorem lieCutPoint_act (y : Lie.AffinePoints U (DualNumber k)) :
    lieCutPoint G χ hU ((Dynamic.centralizerAdjointAction hZ hU).act
        (Lie.constant Z (toBase (baseTest k) ≫ m)) y) =
      cutConj (AffineCoordinates.corepresentation G) (cocharModelAction G χ)
        (z := constantFamily G (m ≫ iZ.hom.hom)) (constantFamily_naturality G _)
        (constantFamily_fixed G _ χ (mem_torusCentralizer_of_centralizer G χ hZ m)) _ (dualTest k)
        (lieCutPoint G χ hU y) := by
  apply Subtype.ext
  change modelPoint G (dualTest k) ((Dynamic.centralizerAdjointAction hZ hU).act
      (Lie.constant Z (toBase (baseTest k) ≫ m)) y ≫ iU.hom.hom) =
    constantFamily G (m ≫ iZ.hom.hom) (dualTest k) * modelPoint G (dualTest k) (y ≫ iU.hom.hom) *
      (constantFamily G (m ≫ iZ.hom.hom) (dualTest k))⁻¹
  rw [Dynamic.centralizerAdjointAction_act_comp, map_mul, map_mul, map_inv]
  have hc : Lie.constant Z (toBase (baseTest k) ≫ m) ≫ iZ.hom.hom =
      toBase (dualTest k) ≫ m ≫ iZ.hom.hom := by
    change ((algSpec (CommRingCat.of k)).map
      (CommAlgCat.ofHom (TrivSqZeroExt.inlAlgHom (CommRingCat.of k) k k)).op ≫
        toBase (baseTest k) ≫ m) ≫ iZ.hom.hom = _
    rw [← Category.assoc ((algSpec (CommRingCat.of k)).map _), toBase_naturality, Category.assoc]
  rw [hc]
  rfl

/-- The conjugation matrix of the rational point `m` in the graded coordinates. -/
abbrev centralizerMatrix : Matrix (Fin n) (Fin n) k :=
  conjMatrix (AffineCoordinates.corepresentation G) (cocharModelAction G χ)
    (constantFamily_naturality G (m ≫ iZ.hom.hom))
    (constantFamily_fixed G _ χ (mem_torusCentralizer_of_centralizer G χ hZ m))
    idExponent_ne_zero hx hbij.2

include hd in
/-- The differential of the centralizer action at `m`, in Lie coordinates, is multiplication by
the conjugation matrix. -/
theorem lieCoord_differential (ξ : Additive (lieKernel U k)) :
    lieCoord G χ hU x ((Dynamic.centralizerAdjointAction hZ hU).differential
        (toBase (baseTest k) ≫ m) ξ) =
      (centralizerMatrix G χ hx hbij hZ m).mulVec (lieCoord G χ hU x ξ) := by
  funext i
  change (coord (unipotentCorep G χ) (lieCutPoint G χ hU
    ((Dynamic.centralizerAdjointAction hZ hU).act (Lie.constant Z (toBase (baseTest k) ≫ m))
      ξ.toMul.val)) (x i)).snd = _
  rw [lieCutPoint_act, coord_cutConj, AlgHom.comp_apply, ← aeval_conjPoly, comp_aeval_apply]
  have hv : (fun j => coord (unipotentCorep G χ) (lieCutPoint G χ hU ξ.toMul.val) (x j)) =
      fun j => TrivSqZeroExt.inr (lieCoord G χ hU x ξ j) := by
    funext j
    apply TrivSqZeroExt.ext
    · exact fst_coord_lieCutPoint G χ hU hd hx ξ.toMul j
    · rfl
  rw [hv, aeval_inr]
  have h0 := (conjPoly_isWeightedHomogeneous (AffineCoordinates.corepresentation G)
    (cocharModelAction G χ) (constantFamily_naturality G (m ≫ iZ.hom.hom))
    (constantFamily_fixed G _ χ (mem_torusCentralizer_of_centralizer G χ hZ m))
    idExponent_ne_zero hx hbij.2 i).coeff_eq_zero 0 (by rw [map_zero]; exact (hd i).ne)
  rw [h0, map_zero, zero_add]
  rfl

include hd in
/-- The determinant of the differential at `m` is the determinant of the conjugation matrix. -/
theorem det_differential :
    (LinearEquiv.det ((Dynamic.centralizerAdjointAction hZ hU).differential
        (toBase (baseTest k) ≫ m)) : k) = (centralizerMatrix G χ hx hbij hZ m).det := by
  let Φ := lieCoordEquiv G χ hU hd hx hbij
  have hconj : (((Dynamic.centralizerAdjointAction hZ hU).differential
      (toBase (baseTest k) ≫ m)) : Additive (lieKernel U k) →ₗ[k] Additive (lieKernel U k)) =
      (Φ.symm : (Fin n → k) →ₗ[k] Additive (lieKernel U k)) ∘ₗ
        Matrix.toLin' (centralizerMatrix G χ hx hbij hZ m) ∘ₗ
          (Φ : Additive (lieKernel U k) →ₗ[k] (Fin n → k)) := by
    apply LinearMap.ext
    intro ξ
    apply Φ.injective
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, Matrix.toLin'_apply]
    exact lieCoord_differential G χ hU hd hx hbij hZ m ξ
  have hdet := LinearMap.det_conj (Matrix.toLin' (centralizerMatrix G χ hx hbij hZ m)) Φ.symm
  rw [LinearEquiv.symm_symm] at hdet
  rw [LinearEquiv.coe_det, hconj, hdet, LinearMap.det_toLin']

omit [IsAffine G.X.left] [Smooth G.X.hom] [IsAffineHom G.X.hom] in
/-- The structure map of the base test is the identity-test comparison of rational points. -/
theorem rationalPointEquiv_eq_toBase (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z.X) :
    Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv k Z.X p = toBase (baseTest k) ≫ p := by
  have h : (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).hom = toBase (baseTest k) :=
    (Over.mkIdTerminal (X := Spec (CommRingCat.of k))).hom_ext _ _
  apply Langlands.AlgebraicGeometry.PointTopology.RingPoint.ext
  rw [Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv_left, ← h]
  change p.left = (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).hom.left ≫ p.left
  change p.left = 𝟙 _ ≫ p.left
  rw [Category.id_comp]

omit [IsAffine G.X.left] [Smooth G.X.hom] [IsAffineHom G.X.hom] in
/-- The rational adjoint determinant character at `m` is the determinant of the differential. -/
theorem rationalCharacterEval_determinantCharacter [IsAffine Z.X.left] {e : ℕ}
    (c : Lie.FiniteCoordinates U e) :
    rationalCharacterEval ((Dynamic.centralizerAdjointAction hZ hU).determinantCharacter c) m =
      LinearEquiv.det ((Dynamic.centralizerAdjointAction hZ hU).differential
        (toBase (baseTest k) ≫ m)) := by
  rw [rationalCharacterEval_eq_affineUnitsEquiv, rationalPointEquiv_eq_toBase,
    affinePointsTarget_apply]
  exact (Dynamic.centralizerAdjointAction hZ hU).determinantCharacter_affinePoints c
    (baseTest k) (toBase (baseTest k) ≫ m)

end Differential

end LieCoordinates

end Langlands.GroupScheme.Dynamic.GradedCoordinates
