import Langlands.GroupScheme.Quaternionic.ScalarMatrixCoordinates
import Langlands.GroupScheme.Rational.SimplyConnectedHasseAlmostSimple
import Langlands.LinearAlgebra.NumberFieldQuadraticIsometryProof
import Langlands.LinearAlgebra.QuadraticReflectionGeneration

/-! # The Hasse kernel of a scalar special orthogonal group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Matrix
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open Quaternionic GaloisPoint

namespace OrthogonalMatrix

open Langlands.LinearAlgebra.OrthogonalCocycleDescent

variable {F : Type u} [Field F] {n : ℕ} [NeZero n]
  (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))

local notation "τ" => FirstKindInvolution.scalar F
local notation "O" => FirstKindInvolution.isometryGroup τ q
local notation "SO" => FirstKindInvolution.normOneIsometryGroup τ q
local notation "A" => Matrix (Fin n) (Fin n) F
local notation "Rₐ" R => CommAlgCat.of F R
local notation "j" => FirstKindInvolution.normOneIsometryGroupι τ q
local notation "detPoint[" R "]" => GeneralLinearGroup.det.comp (scalarMatrixPoint q R)

set_option maxHeartbeats 800000 in
/-- The actual norm-one inclusion has the determinant-one image on affine tests. -/
theorem mem_range_scalarNormOne_affine_iff (R : CommAlgCat.{u} (CommRingCat.of F))
    (x : (O).affinePoints R) :
    x ∈ (SubgroupFunctor.range j).carrier ((algSpec (CommRingCat.of F)).obj (op R)) ↔
      detPoint[R] x = 1 := by
  let T := (algSpec (CommRingCat.of F)).obj (op R)
  let E := Gm.affinePointsEquiv T.hom
  let z := x ≫ ((τ).isometryGroupι q).hom.hom
  let r := CentralSimpleUnits.reducedNormHom F A
  have h := CentralSimpleUnits.reducedNormHom_affine_points F A R z
  change E (z ≫ r.hom.hom) =
    Langlands.CentralSimple.reducedNormUnits F A R ((τ).isometryAffineUnitsOver q R x) at h
  have hmatrix : (scalarMatrixPoint q R x : Matrix (Fin n) (Fin n) R) =
      ScalarMatrixCoordinates.matrixEquiv F R ((τ).isometryAffineUnitsOver q R x : R ⊗[F] A) := by
    change chart F (Fin n) R (OrthogonalMorita.isometryAffineUnitsEquiv τ q R x).val = _
    rw [OrthogonalMorita.coe_isometryAffineUnitsEquiv]
    rfl
  have hd : E (z ≫ r.hom.hom) = detPoint[R] x := by
    rw [h]
    apply Units.ext
    change Langlands.CentralSimple.reducedNorm F A R ((τ).isometryAffineUnitsOver q R x : R ⊗[F] A) =
      (scalarMatrixPoint q R x : Matrix (Fin n) (Fin n) R).det
    rw [ScalarMatrixCoordinates.reducedNorm_eq_det, hmatrix]
  rw [FirstKindInvolution.mem_range_normOneIsometryGroupι_iff, ← hd]
  change z ≫ r.hom.hom = 1 ↔ E (z ≫ r.hom.hom) = 1
  exact ⟨fun e => (congrArg E e).trans E.map_one, fun e => E.injective (e.trans E.map_one.symm)⟩

variable [CharZero F]

private theorem exists_affinePoint_det_neg_one (hq : (τ).IsNondegenerateQuadratic q) :
    ∃ x : (O).affinePoints (Rₐ F), detPoint[Rₐ F] x = -1 := by
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  let B := (τ).polar q
  have hB : Bᵀ = B := scalar_polar_transpose q
  let Q := B.toQuadraticForm'
  have hQ : Q.polarBilin.Nondegenerate := polar_nondegenerate_of_symmetric_unit hB hq
  obtain ⟨z, hz⟩ : ∃ z, Q z ≠ 0 := by
    by_contra! h
    obtain ⟨z, hz⟩ := exists_ne (0 : Fin n → F)
    exact hz (hQ.1 z (fun w => by
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h, sub_zero]))
  let e := Langlands.QuadraticForm.reflection Q z hz
  let M := LinearMap.toMatrix' e.toLinearEquiv.toLinearMap
  have hM : IsUnit M := LinearMap.isUnit_toMatrix'_iff.mpr
    ((Module.End.isUnit_iff _).mpr e.toLinearEquiv.bijective)
  let P := ((Matrix.isUnit_transpose M).mpr hM).unit
  have hP : (P : A) = Mᵀ := ((Matrix.isUnit_transpose M).mpr hM).unit_spec
  have hcomp : Q.comp e.toLinearEquiv.toLinearMap = Q := QuadraticMap.ext e.map_app
  have hm := congrArg QuadraticForm.toMatrix' hcomp
  change QuadraticForm.toMatrix' (B.toQuadraticForm'.comp e.toLinearEquiv.toLinearMap) =
    B.toQuadraticForm'.toMatrix' at hm
  rw [QuadraticForm.toMatrix'_comp, toMatrix_toQuadraticForm_of_symm hB] at hm
  have hPB : gramTransform P B = B := by
    simpa only [gramTransform, hP, transpose_transpose, M] using hm
  obtain ⟨x, hx⟩ := exists_scalarMatrixPoint_eq q (Rₐ F) P (by simpa [B] using hPB)
  refine ⟨x, Units.ext ?_⟩
  change (scalarMatrixPoint q (Rₐ F) x : A).det = -1
  rw [hx, hP, det_transpose]
  change (LinearMap.toMatrix' e.toLinearEquiv.toLinearMap).det = -1
  rw [LinearMap.det_toMatrix', Langlands.QuadraticForm.det_reflection]

variable {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

omit [FiniteDimensional F L] [IsGalois F L] in
private theorem exists_detPoint_eq (hq : (τ).IsNondegenerateQuadratic q)
    (b : (O).affinePoints (Rₐ L)) :
    ∃ a : (O).affinePoints (Rₐ F), detPoint[Rₐ L] (extend F L O a) = detPoint[Rₐ L] b := by
  let P : Matrix (Fin n) (Fin n) L := ((τ).polar q).map (algebraMap F L)
  let g := scalarMatrixPoint q (Rₐ L) b
  have h := congrArg Matrix.det (scalarMatrixPoint_preserves q (Rₐ L) b)
  change ((g : Matrix (Fin n) (Fin n) L) * P * (g : Matrix (Fin n) (Fin n) L)ᵀ).det = P.det at h
  rw [det_mul, det_mul, det_transpose] at h
  have hP : P.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det P).mp
    (hq.map (algebraMap F L).mapMatrix)).ne_zero
  have hsq : (g : Matrix (Fin n) (Fin n) L).det ^ 2 = 1 ^ 2 := by
    apply mul_right_cancel₀ hP
    calc
      _ = (g : Matrix (Fin n) (Fin n) L).det * P.det * (g : Matrix (Fin n) (Fin n) L).det := by ring
      _ = P.det := h
      _ = _ := by simp
  have hg : detPoint[Rₐ L] b = 1 ∨ detPoint[Rₐ L] b = -1 :=
    (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).imp (fun h => Units.ext h) (fun h => Units.ext h)
  rcases hg with hg | hg
  · exact ⟨1, by rw [map_one, map_one, hg]⟩
  · obtain ⟨a, ha⟩ := exists_affinePoint_det_neg_one q hq
    refine ⟨a, Units.ext ?_⟩
    change (scalarMatrixPoint q (Rₐ L) (extend F L O a) : Matrix (Fin n) (Fin n) L).det = _
    have he := scalarMatrixPoint_naturality q (CommAlgCat.ofHom (Algebra.ofId F L)) a
    change scalarMatrixPoint q (Rₐ L) (extend F L O a) = _ at he
    rw [he, hg]
    change ((algebraMap F L).mapMatrix (scalarMatrixPoint q (Rₐ F) a : A)).det = -1
    rw [← RingHom.map_det]
    have hdet : (scalarMatrixPoint q (Rₐ F) a : A).det = -1 := congrArg Units.val ha
    rw [hdet, map_neg, map_one]

/-- Triviality of a determinant-one cocycle is reflected by the full isometry group. -/
theorem isTrivial_scalarNormOne_of_map (hq : (τ).IsNondegenerateQuadratic q)
    (ξ : Cocycle SO (GaloisCocycle.cover F L)) (h : (ξ.map j).IsTrivial) : ξ.IsTrivial := by
  obtain ⟨b, hb⟩ := (GaloisCocycle.isTrivial_iff (ξ.map j)).mp h
  obtain ⟨a, ha⟩ := exists_detPoint_eq q hq b
  let r := extend F L O a
  let t := b * r⁻¹
  have ht : detPoint[Rₐ L] t = 1 := by
    change detPoint[Rₐ L] (b * r⁻¹) = _
    rw [map_mul, map_inv, show detPoint[Rₐ L] r = detPoint[Rₐ L] b from ha, mul_inv_cancel]
  obtain ⟨f, hf⟩ := SubgroupFunctor.mem_range.mp ((mem_range_scalarNormOne_affine_iff q _ t).mpr ht)
  refine (GaloisCocycle.isTrivial_iff ξ).mpr ⟨f, fun s => ?_⟩
  have : Mono (j).hom.hom := kernelι_mono _
  apply (cancel_mono (j).hom.hom).mp
  let J := (SO).affinePointsTarget j (Rₐ L)
  change J (GaloisCocycle.value ξ s) = J (f * (conjugate F L SO s f)⁻¹)
  have Jf : J f = t := hf
  have hj : J (conjugate F L SO s f) = conjugate F L O s (J f) := by
    change (GaloisCocycle.arrow F L s ≫ f) ≫ (j).hom.hom =
      GaloisCocycle.arrow F L s ≫ (f ≫ (j).hom.hom)
    exact Category.assoc _ _ _
  have hbs := hb s
  change J (GaloisCocycle.value ξ s) = _ at hbs
  rw [hbs, map_mul, map_inv, hj, Jf]
  change b * (conjugate F L O s b)⁻¹ = (b * r⁻¹) * (conjugate F L O s (b * r⁻¹))⁻¹
  rw [map_mul, map_inv, show conjugate F L O s r = r from conjugate_extend F L O s a]
  group

end OrthogonalMatrix

/-- Local triviality of a scalar determinant-one cocycle over a number field implies global
triviality on the original finite Galois cover. -/
def NumberFieldSpecialOrthogonalGaloisHasseKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ) [NeZero n]
    (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n)),
    (FirstKindInvolution.scalar F).IsNondegenerateQuadratic q →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle ((FirstKindInvolution.scalar F).normOneIsometryGroup q) (GaloisCocycle.cover F L)),
      ξ.LocallyTrivial → ξ.IsTrivial

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem numberFieldSpecialOrthogonalGaloisHasseKernel :
    NumberFieldSpecialOrthogonalGaloisHasseKernelStatement.{u} := by
  intro F _ _ n _ q hq L _ _ _ _ ξ hlocal
  let O := (FirstKindInvolution.scalar F).isometryGroup q
  let p := (FirstKindInvolution.scalar F).normOneIsometryGroupι q
  let U := GaloisCocycle.cover F L
  let α : Cocycle O U := Cocycle.coboundary (1 : U ⟶ O.X)
  let β : Cocycle O U := ξ.map p
  have hα : ∀ {Z : Over (Spec (CommRingCat.of F))} (a b : Z ⟶ U), α.toFun a b = 1 := by
    intro Z a b
    simp [α, Cocycle.coboundary, MonObj.comp_one]
  have hl : α.LocallyCohomologous β := by
    intro v
    let b := algebraBaseMap F (Global.placeCompletion F v)
    let r := (Over.mapPullbackAdj b).counit.app U
    obtain ⟨f, hf⟩ := (hlocal.map p) v
    refine ⟨f⁻¹, fun x y => ?_⟩
    have hα' : (α.baseChange b _ r).toFun x y = 1 := by
      apply (baseChangePointsEquiv b O _).injective
      rw [Cocycle.baseChange_toFun, hα, map_one]
    rw [hf]
    change x ≫ f * (y ≫ f)⁻¹ =
      (x ≫ f⁻¹)⁻¹ * (α.baseChange b _ r).toFun x y * (y ≫ f⁻¹)
    simp only [hα', GrpObj.comp_inv, inv_inv, mul_one]
  obtain ⟨f, hf⟩ := numberFieldOrthogonalGaloisHasse_of_quadratic numberFieldQuadraticIsometry
    F O ⟨n, q, hq, ⟨Iso.refl _⟩⟩ L α β hl
  apply OrthogonalMatrix.isTrivial_scalarNormOne_of_map q hq ξ
  refine ⟨f⁻¹, fun x y => ?_⟩
  rw [hf]
  change (x ≫ f)⁻¹ * α.toFun x y * (y ≫ f) = (x ≫ f⁻¹) * (y ≫ f⁻¹)⁻¹
  simp only [hα, GrpObj.comp_inv, mul_one, inv_inv]

end Langlands.GroupScheme
