import Langlands.GroupScheme.Quaternionic.HyperbolicScalingMatrix
import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.FiniteAlgebraIdempotentTorus
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.MultiplicativePointTopology
import Langlands.GroupScheme.Rational.SplitTorusRationalDetection
import Langlands.GroupScheme.Rational.AnisotropicSplitTorusHom

/-! # An actual hyperbolic cocharacter in the quaternionic isometry group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.FiniteAlgebraUnits

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
  (p q : A) (hp : p * p = p) (hq : q * q = q) (hpq : p * q = 0) (hqp : q * p = 0)
  {d : ℕ} (b : Module.Basis (Fin d) K A)

theorem idempotentScalingHom_affinePoints (R : CommAlgCat.{u} (CommRingCat.of K))
    (x : GroupScheme.affinePoints (Gm (Spec (CommRingCat.of K))).toGrp R) :
    affinePointsEquiv b R (x ≫ (idempotentScalingHom p q hp hq hpq hqp b).hom.hom) =
      idempotentScalingUnits (K := K) p q hp hq hpq hqp R
        (Gm.affineUnitsEquiv (CommRingCat.of K) R x) := by
  change Corepresented.affinePointsEquiv (functor K A) (corepresentableBy b) R
    (x ≫ (idempotentScalingHom p q hp hq hpq hqp b).hom.hom) = _
  rw [← Corepresented.map_affineSectionsIso_pointsEquiv]
  change Units.map
    (Algebra.TensorProduct.map (Corepresented.affineSectionsIso R).hom.hom
      (AlgHom.id K A)).toMonoidHom
    (pointsEquiv b _ (x ≫ (idempotentScalingHom p q hp hq hpq hqp b).hom.hom)) = _
  rw [idempotentScalingHom_points]
  erw [idempotentScalingUnits_map]
  congr 1
  apply Units.ext
  exact DFunLike.congr_fun (Corepresented.affineSectionsIso_hom_ringHom R)
    (Gm.pointsEquiv (Spec (CommRingCat.of K)) _ x).val

theorem lid_idempotentScalingValue (t : Kˣ) :
    Algebra.TensorProduct.lid K A (idempotentScalingValue (K := K) p q K t) =
      1 + ((t : K) - 1) • p + (((t⁻¹ : Kˣ) : K) - 1) • q := by
  simp [idempotentScalingValue_eq]

end FiniteAlgebraUnits

namespace Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n] {q : σ.QuadraticForms n} {x y : n → D}

variable {σ}

namespace IsHyperbolicPair

/-- The actual multiplicative-group map into the matrix-algebra unit group. -/
def hyperbolicUnitTorus (h : σ.IsHyperbolicPair q x y) :
    (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D)) :=
  FiniteAlgebraUnits.idempotentScalingHom
    (σ.hyperbolicLineMatrix q x y) (σ.hyperbolicLineMatrix q y x)
    h.hyperbolicLineMatrix_idempotent h.symm.hyperbolicLineMatrix_idempotent
    h.hyperbolicLineMatrix_mul_swap h.symm.hyperbolicLineMatrix_mul_swap
    (Module.finBasis K (Matrix n n D))

theorem hyperbolicUnitTorus_affineMatrix (h : σ.IsHyperbolicPair q x y)
    (a : GroupScheme.affinePoints (Gm (Spec (CommRingCat.of K))).toGrp (CommAlgCat.of K K)) :
    Algebra.TensorProduct.lid K (Matrix n n D)
      (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D))
        (CommAlgCat.of K K) (a ≫ (h.hyperbolicUnitTorus).hom.hom) :
          K ⊗[K] Matrix n n D) =
      σ.hyperbolicScalingMatrix q x y (Gm.affineUnitsEquiv (CommRingCat.of K) (CommAlgCat.of K K) a) := by
  rw [hyperbolicUnitTorus, FiniteAlgebraUnits.idempotentScalingHom_affinePoints]
  exact FiniteAlgebraUnits.lid_idempotentScalingValue _ _ _

/-- An affine coefficient point satisfying the defining defect has an actual isometry lift. -/
theorem exists_isometryAffinePoint_of_defect (R : CommAlgCat.{u} (CommRingCat.of K))
    (u : (R ⊗[K] Matrix n n D)ˣ)
    (hu : IsometryCut.defect (σ.matrix n) (Quotient.out q) (u : R ⊗[K] Matrix n n D) ∈
      (σ.quadraticKernel n).baseChange R) :
    ∃ z : (σ.isometryGroup q).affinePoints R,
      z ≫ (σ.isometryGroupι q).hom.hom =
        (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D)) R).symm u := by
  let hI := IsometryCut.isCutOutBy
    (IsometryCut.isStable_alternatingSubspace (τ := σ.matrix n)) (Quotient.out q)
  let z := (Corepresented.affinePointsEquiv _ (Corepresented.cutCorepresentableBy hI) R).symm
    ⟨u, hu⟩
  refine ⟨z, ?_⟩
  apply (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D)) R).injective
  change Corepresented.affinePointsEquiv _ (FiniteAlgebraUnits.corepresentableBy
    (Module.finBasis K (Matrix n n D))) R
    (z ≫ (Corepresented.cutHom hI).hom.hom) = _
  rw [Corepresented.cutHom, Corepresented.groupSchemeMap_affinePoints]
  rw [MulEquiv.apply_symm_apply]
  change ((Corepresented.affinePointsEquiv _ (Corepresented.cutCorepresentableBy hI) R) z).val = u
  exact congrArg Subtype.val
    ((Corepresented.affinePointsEquiv _ (Corepresented.cutCorepresentableBy hI) R).apply_symm_apply ⟨u, hu⟩)

omit [FiniteDimensional K D] in
private theorem mem_baseChange_self_of_lid_mem (M : Submodule K (Matrix n n D))
    (z : K ⊗[K] Matrix n n D) (hz : Algebra.TensorProduct.lid K (Matrix n n D) z ∈ M) :
    z ∈ M.baseChange K := by
  have he : z = (1 : K) ⊗ₜ[K] Algebra.TensorProduct.lid K (Matrix n n D) z := by
    apply (Algebra.TensorProduct.lid K (Matrix n n D)).injective
    simp
  rw [he]
  exact Submodule.tmul_mem_baseChange_of_mem 1 hz

omit [FiniteDimensional K D] in
private theorem lid_matrix_baseChange (z : K ⊗[K] Matrix n n D) :
    Algebra.TensorProduct.lid K (Matrix n n D) ((σ.matrix n).baseChange K z) =
      σ.matrix n (Algebra.TensorProduct.lid K (Matrix n n D) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c M => simp
  | add z z' hz hz' => simp only [_root_.map_add, hz, hz']

/-- Ground-field coefficient points of the unit torus satisfy the actual defining defect. -/
theorem hyperbolicUnitTorus_defect_mem (h : σ.IsHyperbolicPair q x y)
    (a : GroupScheme.affinePoints (Gm (Spec (CommRingCat.of K))).toGrp (CommAlgCat.of K K)) :
    IsometryCut.defect (σ.matrix n) (Quotient.out q)
      (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D))
        (CommAlgCat.of K K) (a ≫ h.hyperbolicUnitTorus.hom.hom) : K ⊗[K] Matrix n n D) ∈
      (σ.quadraticKernel n).baseChange K := by
  apply mem_baseChange_self_of_lid_mem
  rw [IsometryCut.defect, _root_.map_sub, _root_.map_mul, _root_.map_mul,
    lid_matrix_baseChange, Algebra.TensorProduct.lid_tmul, one_smul,
    h.hyperbolicUnitTorus_affineMatrix]
  exact h.hyperbolicScalingMatrix_defect_mem _ _ (Submodule.Quotient.mk_out q)

variable [Infinite K]

/-- Over an infinite ground field the actual unit-torus map factors through the isometry group. -/
theorem exists_hyperbolicIsometryTorus (h : σ.IsHyperbolicPair q x y) :
    ∃ f : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q,
      f ≫ σ.isometryGroupι q = h.hyperbolicUnitTorus := by
  let j := (σ.isometryGroupι q).hom.hom
  have : IsClosedImmersion j.left := σ.isClosedSubgroup_isometryGroupι q
  have : Mono j.left := inferInstance
  have : Mono j := Over.mono_of_mono_left _
  obtain ⟨l, hl⟩ := isSplitTorus_gm.exists_factor_of_kpoints j
    h.hyperbolicUnitTorus.hom.hom (by
      intro a
      let aK := GaloisPointComparison.rationalCoeffEquiv K
        (Gm (Spec (CommRingCat.of K))).toGrp a
      let u := FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis K (Matrix n n D))
        (CommAlgCat.of K K) (aK ≫ h.hyperbolicUnitTorus.hom.hom)
      obtain ⟨z, hz⟩ := exists_isometryAffinePoint_of_defect (σ := σ)
        (CommAlgCat.of K K) u (h.hyperbolicUnitTorus_defect_mem aK)
      have hz' : z ≫ j = aK ≫ h.hyperbolicUnitTorus.hom.hom :=
        hz.trans ((FiniteAlgebraUnits.affinePointsEquiv
          (Module.finBasis K (Matrix n n D)) (CommAlgCat.of K K)).symm_apply_apply _)
      let z₀ := (GaloisPointComparison.rationalCoeffEquiv K (σ.isometryGroup q)).symm z
      refine ⟨z₀, ?_⟩
      change rationalPoints.map (σ.isometryGroupι q) z₀ =
        rationalPoints.map h.hyperbolicUnitTorus a
      apply (GaloisPointComparison.rationalCoeffEquiv K
        (FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D)))).injective
      rw [GaloisPointComparison.rationalCoeffEquiv_map,
        GaloisPointComparison.rationalCoeffEquiv_map]
      simpa only [affinePointsTarget_apply, z₀, MulEquiv.apply_symm_apply] using hz')
  have : IsMonHom l :=
    { one_hom := by
        apply (cancel_mono j).mp
        rw [Category.assoc, hl, IsMonHom.one_hom, IsMonHom.one_hom]
      mul_hom := by
        apply (cancel_mono j).mp
        rw [Category.assoc, hl, IsMonHom.mul_hom, Category.assoc,
          IsMonHom.mul_hom, CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc, hl] }
  exact ⟨Grp.homMk l, Grp.hom_ext _ _ hl⟩

/-- The actual hyperbolic cocharacter into the isometry group. -/
def hyperbolicIsometryTorus (h : σ.IsHyperbolicPair q x y) :
    (Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q :=
  Classical.choose h.exists_hyperbolicIsometryTorus

@[reassoc (attr := simp)] theorem hyperbolicIsometryTorus_comp (h : σ.IsHyperbolicPair q x y) :
    h.hyperbolicIsometryTorus ≫ σ.isometryGroupι q = h.hyperbolicUnitTorus :=
  Classical.choose_spec h.exists_hyperbolicIsometryTorus

/-- The first singular line detects that the actual unit cocharacter is nontrivial. -/
theorem hyperbolicUnitTorus_ne_zero (h : σ.IsHyperbolicPair q x y) :
    h.hyperbolicUnitTorus ≠ 0 := by
  classical
  intro hz
  obtain ⟨c, hc⟩ := ({0, 1} : Finset K).exists_notMem
  have hc' : c ≠ 0 ∧ c ≠ 1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hc
  let t := Units.mk0 c hc'.1
  have ht : t ≠ 1 := fun he => hc'.2 (congrArg Units.val he)
  let a := (Gm.affineUnitsEquiv (CommRingCat.of K) (CommAlgCat.of K K)).symm t
  have ha0 : a ≫ h.hyperbolicUnitTorus.hom.hom = 1 := by
    rw [hz]
    exact MonObj.comp_one a
  have hm := h.hyperbolicUnitTorus_affineMatrix a
  rw [ha0] at hm
  have hM : σ.hyperbolicScalingMatrix q x y t = 1 := by
    simpa only [a, MulEquiv.apply_symm_apply, _root_.map_one, Units.val_one] using hm.symm
  have hx : (t : K) • x = x := by
    have he := (σ.vecMul_hyperbolicScalingMatrix q x y x t).trans (h.hyperbolicScaling_left t)
    rw [hM, Matrix.vecMul_one] at he
    exact he.symm
  apply ht
  exact Units.ext (smul_left_injective K h.left_ne_zero (hx.trans (one_smul K x).symm))

theorem hyperbolicIsometryTorus_ne_zero (h : σ.IsHyperbolicPair q x y) :
    h.hyperbolicIsometryTorus ≠ 0 := by
  intro hz
  apply h.hyperbolicUnitTorus_ne_zero
  rw [← h.hyperbolicIsometryTorus_comp, hz, Limits.zero_comp]

variable [Smooth (σ.isometryGroup q).X.hom]

/-- The connected-source cocharacter lands in the identity component. -/
def hyperbolicConnectedTorus (h : σ.IsHyperbolicPair q x y) :
    (Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.connectedIsometryGroup q := by
  have : ConnectedSpace (Gm (Spec (CommRingCat.of K))).X.left := isSplitTorus_gm.connectedSpace
  exact IdentityComponent.factor (σ.isometryGroup q) h.hyperbolicIsometryTorus

@[reassoc (attr := simp)] theorem hyperbolicConnectedTorus_comp (h : σ.IsHyperbolicPair q x y) :
    h.hyperbolicConnectedTorus ≫ identityComponentι (σ.isometryGroup q) ≫ σ.isometryGroupι q =
      h.hyperbolicUnitTorus := by
  rw [hyperbolicConnectedTorus, IdentityComponent.factor_identityComponentι_assoc,
    h.hyperbolicIsometryTorus_comp]

/-- A hyperbolic pair gives split rank at least one for the smooth connected isometry group. -/
theorem one_le_splitRank_connectedIsometryGroup (h : σ.IsHyperbolicPair q x y) :
    1 ≤ splitRank (σ.connectedIsometryGroup q) := by
  apply Order.one_le_iff_ne_zero.mpr
  intro hz
  have hf : h.hyperbolicConnectedTorus = 0 :=
    IsAnisotropic.hom_eq_zero_of_isSplitTorus hz isSplitTorus_gm h.hyperbolicConnectedTorus
  apply h.hyperbolicUnitTorus_ne_zero
  rw [← h.hyperbolicConnectedTorus_comp, hf, Limits.zero_comp]

end IsHyperbolicPair

/-- Positive quadratic Witt index gives the rank-one lower bound over every infinite field. -/
theorem one_le_splitRank_connectedIsometryGroup_of_quadraticWittIndex_pos [Infinite K]
    (q : σ.QuadraticForms n) [Smooth (σ.isometryGroup q).X.hom]
    (hq : σ.IsNondegenerateQuadratic q) (hi : 0 < σ.quadraticWittIndex q) :
    1 ≤ splitRank (σ.connectedIsometryGroup q) := by
  obtain ⟨x, y, h⟩ := σ.exists_hyperbolicPair_of_quadraticWittIndex_pos q hq hi
  exact h.one_le_splitRank_connectedIsometryGroup

end Quaternionic.FirstKindInvolution

end Langlands.GroupScheme
