import Langlands.GroupScheme.Unipotent.PolynomialKernelVectorFactor
import Langlands.GroupScheme.Unipotent.PolynomialKernelCriterion
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.Rational.AffineLineExtensions
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.FieldTheory.IsSepClosed

/-! # Actual scalar extension of additive polynomial kernels -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.Unipotent

open OneDimensional RelativeRoot

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {n : ℕ}

/-- Forgetting the extension field composes the global-function structure map
with the original coefficient map. -/
theorem structureMap_map_algebraBaseMap (T : Over (Spec (CommRingCat.of K))) :
    AdditiveGroupQuotient.structureMap ((Over.map (algebraBaseMap k K)).obj T) =
      (AdditiveGroupQuotient.structureMap T).comp (algebraMap k K) := by
  unfold AdditiveGroupQuotient.structureMap
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (T.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))).appTop).hom = _
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The actual polynomial row vanishes exactly when its coordinate sum does. -/
theorem comp_polynomialRow_eq_one_iff
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of k) n).X) :
    x ≫ (polynomialRow f hf).hom.hom = 1 ↔
      (∑ i, (f i).eval₂ (AdditiveGroupQuotient.structureMap T)
        ((VectorGroup.coordinates (CommRingCat.of k) n T x).toAdd i)) = 0 := by
  rw [comp_polynomialRow]
  constructor
  · intro h
    have hcoord := congrArg
      (fun y => (VectorGroup.coordinates (CommRingCat.of k) 1 T y).toAdd 0) h
    simpa only [polynomialRowPoints_coord, map_one, toAdd_one, Pi.zero_apply] using hcoord
  · intro h
    apply VectorGroup.points_ext
    intro j
    rw [polynomialRowPoints_coord, h]
    simp only [map_one, toAdd_one, Pi.zero_apply]

/-- The coordinate comparison for vector-group points over an extended field. -/
def scalarVectorPointsEquiv (n : ℕ) (T : Over (Spec (CommRingCat.of K))) :
    (((Over.map (algebraBaseMap k K)).obj T) ⟶
      (VectorGroup.groupScheme (CommRingCat.of k) n).X) ≃*
        (T ⟶ (VectorGroup.groupScheme (CommRingCat.of K) n).X) :=
  (VectorGroup.coordinates (CommRingCat.of k) n
    ((Over.map (algebraBaseMap k K)).obj T)).trans
      (VectorGroup.coordinates (CommRingCat.of K) n T).symm

@[simp]
theorem scalarVectorPointsEquiv_coord (T : Over (Spec (CommRingCat.of K)))
    (x : ((Over.map (algebraBaseMap k K)).obj T) ⟶
      (VectorGroup.groupScheme (CommRingCat.of k) n).X) (i : Fin n) :
    (VectorGroup.coordinates (CommRingCat.of K) n T
      (scalarVectorPointsEquiv n T x)).toAdd i =
        (VectorGroup.coordinates (CommRingCat.of k) n
          ((Over.map (algebraBaseMap k K)).obj T) x).toAdd i := by
  exact congrArg (fun y => y.toAdd i)
    ((VectorGroup.coordinates (CommRingCat.of K) n T).apply_symm_apply _)

/-- Evaluating mapped coefficients preserves the pointwise kernel condition. -/
theorem scalarVectorPointsEquiv_mem_kernel
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (T : Over (Spec (CommRingCat.of K)))
    (x : ((Over.map (algebraBaseMap k K)).obj T) ⟶
      (VectorGroup.groupScheme (CommRingCat.of k) n).X) :
    scalarVectorPointsEquiv n T x ≫
      (polynomialRow (fun i => (f i).map (algebraMap k K))
        (fun i => (hf i).map_algebraMap)).hom.hom = 1 ↔
      x ≫ (polynomialRow f hf).hom.hom = 1 := by
  rw [comp_polynomialRow_eq_one_iff, comp_polynomialRow_eq_one_iff]
  simp only [scalarVectorPointsEquiv_coord, eval₂_map, structureMap_map_algebraBaseMap]

/-- The scalar coordinate comparison is natural in every relative scheme test. -/
theorem scalarVectorPointsEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : ((Over.map (algebraBaseMap k K)).obj T) ⟶
      (VectorGroup.groupScheme (CommRingCat.of k) n).X) :
    scalarVectorPointsEquiv n T' ((Over.map (algebraBaseMap k K)).map a ≫ x) =
      a ≫ scalarVectorPointsEquiv n T x := by
  apply VectorGroup.points_ext
  intro i
  simp only [scalarVectorPointsEquiv_coord, VectorGroup.coordinates_comp]
  rfl

/-- Scalar comparison restricted to the actual pointwise polynomial kernels. -/
def scalarKernelPointsEquiv
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (T : Over (Spec (CommRingCat.of K))) :
    (((yonedaGrp.map (polynomialRow f hf)).app
      (.op ((Over.map (algebraBaseMap k K)).obj T))).hom.ker) ≃*
        (((yonedaGrp.map (polynomialRow (fun i => (f i).map (algebraMap k K))
          (fun i => (hf i).map_algebraMap))).app (.op T)).hom.ker) where
  toFun x := ⟨scalarVectorPointsEquiv n T x.val,
    (scalarVectorPointsEquiv_mem_kernel f hf T x.val).mpr x.property⟩
  invFun x := ⟨(scalarVectorPointsEquiv n T).symm x.val, by
    apply (scalarVectorPointsEquiv_mem_kernel f hf T _).mp
    rw [MulEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext ((scalarVectorPointsEquiv n T).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((scalarVectorPointsEquiv n T).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((scalarVectorPointsEquiv n T).map_mul x.val y.val)

/-- Naturality of the scalar comparison on pointwise polynomial kernels. -/
theorem scalarKernelPointsEquiv_naturality
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : (((yonedaGrp.map (polynomialRow f hf)).app
      (.op ((Over.map (algebraBaseMap k K)).obj T))).hom.ker)) :
    scalarKernelPointsEquiv f hf T'
      (kernelPointsRestrict (polynomialRow f hf) ((Over.map (algebraBaseMap k K)).map a) x) =
      kernelPointsRestrict
        (polynomialRow (fun i => (f i).map (algebraMap k K))
          (fun i => (hf i).map_algebraMap)) a (scalarKernelPointsEquiv f hf T x) :=
  Subtype.ext (scalarVectorPointsEquiv_naturality a x.val)

/-- Comparison of actual base-changed kernel points with the kernel of the
coefficientwise extended polynomial row. -/
def polynomialKernelBaseChangePointsEquiv
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ ((Over.pullback (algebraBaseMap k K)).mapGrp.obj
      (kernel (polynomialRow f hf))).X) ≃*
        (T ⟶ (kernel (polynomialRow (fun i => (f i).map (algebraMap k K))
          (fun i => (hf i).map_algebraMap))).X) :=
  (baseChangePointsEquiv (algebraBaseMap k K) (kernel (polynomialRow f hf)) T).trans
    ((kernelPointsEquiv (polynomialRow f hf)
      ((Over.map (algebraBaseMap k K)).obj T)).trans
        ((scalarKernelPointsEquiv f hf T).trans
          (kernelPointsEquiv (polynomialRow (fun i => (f i).map (algebraMap k K))
            (fun i => (hf i).map_algebraMap)) T).symm))

/-- The comparison of actual points respects their canonical kernel coordinates. -/
theorem polynomialKernelBaseChangePointsEquiv_kernelPoints
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ ((Over.pullback (algebraBaseMap k K)).mapGrp.obj
      (kernel (polynomialRow f hf))).X) :
    kernelPointsEquiv (polynomialRow (fun i => (f i).map (algebraMap k K))
      (fun i => (hf i).map_algebraMap)) T
        (polynomialKernelBaseChangePointsEquiv f hf T x) =
      scalarKernelPointsEquiv f hf T
        (kernelPointsEquiv (polynomialRow f hf) ((Over.map (algebraBaseMap k K)).obj T)
          (baseChangePointsEquiv (algebraBaseMap k K) (kernel (polynomialRow f hf)) T x)) :=
  (kernelPointsEquiv (polynomialRow (fun i => (f i).map (algebraMap k K))
    (fun i => (hf i).map_algebraMap)) T).apply_symm_apply _

/-- The actual polynomial-kernel comparison is natural in every test scheme. -/
theorem polynomialKernelBaseChangePointsEquiv_naturality
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ ((Over.pullback (algebraBaseMap k K)).mapGrp.obj
      (kernel (polynomialRow f hf))).X) :
    polynomialKernelBaseChangePointsEquiv f hf T' (a ≫ x) =
      a ≫ polynomialKernelBaseChangePointsEquiv f hf T x := by
  apply (kernelPointsEquiv (polynomialRow (fun i => (f i).map (algebraMap k K))
    (fun i => (hf i).map_algebraMap)) T').injective
  rw [polynomialKernelBaseChangePointsEquiv_kernelPoints,
    kernelPointsEquiv_naturality, polynomialKernelBaseChangePointsEquiv_kernelPoints]
  rw [baseChangePointsEquiv_naturality, kernelPointsEquiv_naturality,
    scalarKernelPointsEquiv_naturality]

/-- Base change of an actual additive polynomial kernel is the actual kernel
of the coefficientwise extended row. -/
def polynomialKernelBaseChangeIso
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i)) :
    (Over.pullback (algebraBaseMap k K)).mapGrp.obj (kernel (polynomialRow f hf)) ≅
      kernel (polynomialRow (fun i => (f i).map (algebraMap k K))
        (fun i => (hf i).map_algebraMap)) :=
  isoOfPoints (polynomialKernelBaseChangePointsEquiv f hf)
    (polynomialKernelBaseChangePointsEquiv_naturality f hf)

/-- The comparison isomorphism induces the constructed point equivalence. -/
@[simp]
theorem comp_polynomialKernelBaseChangeIso_hom
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i))
    (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ ((Over.pullback (algebraBaseMap k K)).mapGrp.obj
      (kernel (polynomialRow f hf))).X) :
    x ≫ (polynomialKernelBaseChangeIso f hf).hom.hom.hom =
      polynomialKernelBaseChangePointsEquiv f hf T x :=
  comp_isoOfPoints_hom _ _ T x

/-- Actual affine-line constancy for a polynomial kernel is invariant under
actual scheme base change along any algebraic Galois field extension. -/
theorem hasConstantAffineLineMaps_baseChange_polynomialKernel_iff [IsGalois k K]
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i)) :
    HasConstantAffineLineMaps
      ((Over.pullback (algebraBaseMap k K)).mapGrp.obj (kernel (polynomialRow f hf))) ↔
        HasConstantAffineLineMaps (kernel (polynomialRow f hf)) := by
  let e := polynomialKernelBaseChangeIso (K := K) f hf
  constructor
  · intro h
    apply (hasConstantAffineLineMaps_polynomialKernel_iff_of_isGalois (K := K) f hf).mp
    exact h.of_mono e.inv.hom.hom
  · intro h
    have hK := (hasConstantAffineLineMaps_polynomialKernel_iff_of_isGalois
      (K := K) f hf).mpr h
    exact hK.of_mono e.hom.hom.hom

/-- The constant complement in the iterated vector-factor decomposition remains
constant after actual base change to the separable closure. -/
theorem exists_polynomialKernelVectorFactor_separableClosure (n : ℕ)
    (f : Fin n → k[X]) (hf : ∀ i, IsAdditive (f i)) :
    ∃ (r m : ℕ) (g : Fin m → k[X]) (hg : ∀ i, IsAdditive (g i)),
      r + m = n ∧ HasConstantAffineLineMaps (kernel (polynomialRow g hg)) ∧
        HasConstantAffineLineMaps
          ((Over.pullback (algebraBaseMap k (SeparableClosure k))).mapGrp.obj
            (kernel (polynomialRow g hg))) ∧
        Nonempty (kernel (polynomialRow f hf) ≅
          VectorGroup.groupScheme (CommRingCat.of k) r ⊗
            kernel (polynomialRow g hg)) := by
  obtain ⟨r, m, g, hg, hrm, hc, he⟩ := exists_polynomialKernelVectorFactor n f hf
  exact ⟨r, m, g, hg, hrm, hc,
    (hasConstantAffineLineMaps_baseChange_polynomialKernel_iff g hg).mpr hc, he⟩

end Langlands.GroupScheme.Unipotent
