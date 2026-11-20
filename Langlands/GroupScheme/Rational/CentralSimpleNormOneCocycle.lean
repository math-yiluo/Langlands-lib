import Langlands.Algebra.GaloisUnitHilbert90
import Langlands.GroupScheme.CentralSimpleNormOne
import Langlands.GroupScheme.CocycleBaseChangeTriviality
import Langlands.GroupScheme.GaloisCocycleLocalTrivialization

/-! # Reduced-norm obstructions for the actual norm-one group -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.CentralSimpleUnits

open GaloisPoint Langlands.CentralSimple

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {F A : Type u} [Field F] [Ring A] [Algebra F A]
  [FiniteDimensional F A] [Algebra.IsCentral F A] [IsSimpleRing A]

local notation "U" => groupScheme F A
local notation "N" => normOne F A
local notation "Rₐ" R => CommAlgCat.of F R
local notation "ι" => normOneι F A
local notation "jₐ" => affinePointsTarget (normOne F A) (normOneι F A)

/-- The reduced norm on affine coefficient points of the unit group. -/
def affineReducedNorm (R : CommAlgCat.{u} (CommRingCat.of F)) :
    (U).affinePoints R →* Rˣ :=
  (reducedNormUnits F A R).comp (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A) R)

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]

/-- The affine reduced norm respects the original coefficient maps. -/
theorem affineReducedNorm_naturality (f : R →ₐ[F] S) (x : (U).affinePoints (Rₐ R)) :
    affineReducedNorm (Rₐ S) ((U).affinePointMap (CommAlgCat.ofHom f) x) =
      Units.map f.toMonoidHom (affineReducedNorm (Rₐ R) x) := by
  change reducedNormUnits F A S
    (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A) (Rₐ S)
      (((algSpec (CommRingCat.of F)).map (CommAlgCat.ofHom f).op) ≫ x)) = _
  rw [FiniteAlgebraUnits.affinePointsEquiv_naturality, reducedNormUnits_naturality]
  rfl

@[simp] theorem affineReducedNorm_normOneι (x : (N).affinePoints (Rₐ R)) :
    affineReducedNorm (Rₐ R) (jₐ (Rₐ R) x) = 1 :=
  (normOneAffinePointsEquiv F A (Rₐ R) x).property

private theorem exists_includePoint_of_affineReducedNorm_one (x : (U).affinePoints (Rₐ R))
    (h : affineReducedNorm (Rₐ R) x = 1) : ∃ y, jₐ (Rₐ R) y = x := by
  let e := FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A) (Rₐ R)
  let p : reducedNormOne F A R := ⟨e x, h⟩
  let q := normOneAffinePointsEquiv F A (Rₐ R)
  refine ⟨q.symm p, e.injective ?_⟩
  exact congrArg Subtype.val (q.apply_symm_apply p)

section Galois

variable {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

private def tensorAut : (L ≃ₐ[F] L) →* RingAut (L ⊗[F] A) where
  toFun σ := (Algebra.TensorProduct.congr σ (AlgEquiv.refl : A ≃ₐ[F] A)).toRingEquiv
  map_one' := by
    change (Algebra.TensorProduct.congr AlgEquiv.refl AlgEquiv.refl).toRingEquiv = _
    rw [Algebra.TensorProduct.congr_refl]
    rfl
  map_mul' σ τ := by
    change (Algebra.TensorProduct.congr (τ.trans σ) (AlgEquiv.refl : A ≃ₐ[F] A)).toRingEquiv = _
    rw [show (AlgEquiv.refl : A ≃ₐ[F] A) = AlgEquiv.refl.trans AlgEquiv.refl from rfl,
      Algebra.TensorProduct.congr_trans]
    rfl

omit [FiniteDimensional F A] [Algebra.IsCentral F A] [IsSimpleRing A]
  [FiniteDimensional F L] [IsGalois F L] in
private theorem tensorAut_smul (σ : L ≃ₐ[F] L) (a : L) (x : L ⊗[F] A) :
    tensorAut σ (a • x) = σ a • tensorAut σ x := by
  induction x using TensorProduct.inductionOn with
  | tmul y z =>
      change (Algebra.TensorProduct.congr σ (AlgEquiv.refl : A ≃ₐ[F] A))
        (a • y ⊗ₜ[F] z) = σ a • (σ y ⊗ₜ[F] z)
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
      simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
        AlgEquiv.coe_toAlgHom, smul_eq_mul, map_mul]
      rfl
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

omit [Algebra.IsCentral F A] [IsSimpleRing A] [IsGalois F L] in
private theorem exists_unitPoint_coboundary [Infinite F] (ξ : Cocycle U (GaloisCocycle.cover F L)) :
    ∃ b : (U).affinePoints (Rₐ L), ∀ σ : L ≃ₐ[F] L,
      GaloisCocycle.value ξ σ = b * (conjugate F L U σ b)⁻¹ := by
  let E := FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A) (Rₐ L)
  let c (σ : L ≃ₐ[F] L) := E (GaloisCocycle.value ξ σ)
  let H : Subgroup (L ≃ₐ[F] L) := ⊤
  have hact (σ : L ≃ₐ[F] L) (x : (U).affinePoints (Rₐ L)) :
      E (conjugate F L U σ x) = Units.map (tensorAut σ).toMonoidHom (E x) :=
    FiniteAlgebraUnits.affinePointsEquiv_naturality _ (CommAlgCat.ofHom σ.toAlgHom) x
  have hc₁ : c 1 = 1 := by
    have h := GaloisCocycle.value_mul ξ 1 1
    rw [one_mul, conjugate_one] at h
    have h₁ := mul_left_cancel (h.symm.trans (mul_one _).symm)
    exact (congrArg E h₁).trans E.map_one
  have hc (σ τ : L ≃ₐ[F] L) : c (σ * τ) = c σ * Units.map (tensorAut σ).toMonoidHom (c τ) := by
    change E (GaloisCocycle.value ξ (σ * τ)) = _
    rw [GaloisCocycle.value_mul, map_mul, hact]
  obtain ⟨b, hb⟩ := Langlands.Algebra.exists_unit_coboundary H
    (tensorAut.comp H.subtype) (fun σ => tensorAut_smul σ.val) (fun σ => c σ.val) hc₁
    (fun σ τ => hc σ.val τ.val)
  refine ⟨E.symm b, fun σ => ?_⟩
  apply E.injective
  rw [map_mul, map_inv, hact, MulEquiv.apply_symm_apply]
  exact eq_mul_inv_of_mul_eq (hb ⟨σ, Subgroup.mem_top σ⟩)

/-- A norm-one cocycle has a primitive in the unit group whose reduced norm comes from the base. -/
theorem exists_cocycle_primitive [Infinite F] (ξ : Cocycle N (GaloisCocycle.cover F L)) :
    ∃ (b : (U).affinePoints (Rₐ L)) (a : Fˣ),
      (∀ σ : L ≃ₐ[F] L, jₐ (Rₐ L) (GaloisCocycle.value ξ σ) =
        b * (conjugate F L U σ b)⁻¹) ∧
      affineReducedNorm (Rₐ L) b = Units.map (algebraMap F L) a := by
  obtain ⟨b, hb⟩ := exists_unitPoint_coboundary (ξ.map ι)
  change ∀ σ, jₐ (Rₐ L) (GaloisCocycle.value ξ σ) = _ at hb
  let p := affineReducedNorm (F := F) (A := A) (Rₐ L)
  have hfix (σ : L ≃ₐ[F] L) : σ (p b : L) = p b := by
    have h := congrArg p (hb σ)
    have hs : p (conjugate F L U σ b) = Units.map σ.toMonoidHom (p b) :=
      affineReducedNorm_naturality σ.toAlgHom b
    rw [affineReducedNorm_normOneι, map_mul, map_inv, hs] at h
    exact congrArg Units.val (eq_of_mul_inv_eq_one h.symm).symm
  obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (p b : L)).2 hfix
  have ha₀ : a ≠ 0 := by
    intro h
    exact (p b).ne_zero (by rw [← ha, h, map_zero])
  exact ⟨b, Units.mk0 a ha₀, hb, Units.ext ha.symm⟩

/-- If the descended reduced norm is attained over the ground field, a unit primitive
can be corrected on the original Galois cover to take values in the norm-one scheme. -/
theorem isTrivial_of_primitive_norm (ξ : Cocycle N (GaloisCocycle.cover F L))
    (b : (U).affinePoints (Rₐ L)) (r : (U).affinePoints (Rₐ F))
    (hb : ∀ σ : L ≃ₐ[F] L, jₐ (Rₐ L) (GaloisCocycle.value ξ σ) =
      b * (conjugate F L U σ b)⁻¹)
    (hr : affineReducedNorm (Rₐ L) b =
      Units.map (algebraMap F L) (affineReducedNorm (Rₐ F) r)) : ξ.IsTrivial := by
  let q := extend F L U r
  have hq : affineReducedNorm (Rₐ L) q = affineReducedNorm (Rₐ L) b :=
    (affineReducedNorm_naturality (Algebra.ofId F L) r).trans hr.symm
  obtain ⟨f, hf⟩ := exists_includePoint_of_affineReducedNorm_one (b * q⁻¹)
    (by rw [map_mul, map_inv, hq, mul_inv_cancel])
  refine (GaloisCocycle.isTrivial_iff ξ).2 ⟨f, fun σ => ?_⟩
  apply (cancel_mono (kernelι (reducedNormHom F A)).hom.hom).mp
  change jₐ (Rₐ L) (GaloisCocycle.value ξ σ) =
    jₐ (Rₐ L) (f * (conjugate F L N σ f)⁻¹)
  have he : jₐ (Rₐ L) (conjugate F L N σ f) =
      conjugate F L U σ (jₐ (Rₐ L) f) := by
    change (GaloisCocycle.arrow F L σ ≫ f) ≫ (ι).hom.hom =
      GaloisCocycle.arrow F L σ ≫ (f ≫ (ι).hom.hom)
    exact Category.assoc _ _ _
  rw [hb, map_mul, map_inv, he, hf, map_mul, map_inv]
  rw [show conjugate F L U σ q = q from conjugate_extend F L U σ r]
  group

variable {K : Type u} [Field K] [Algebra F K]

omit [FiniteDimensional F L] in
/-- A trivialization on the actual pullback to `K` makes the descended reduced
norm of any unit primitive a reduced norm over `K`. -/
theorem exists_affineReducedNorm_of_baseChange_isTrivial
    (M : Type u) [Field M] [Algebra F M] [Algebra K M] [Algebra L M]
    [IsScalarTower F K M] [IsScalarTower F L M] [FiniteDimensional K M] [IsGalois K M]
    (ξ : Cocycle N (GaloisCocycle.cover F L)) (b : (U).affinePoints (Rₐ L)) (a : Fˣ)
    (hb : ∀ σ : L ≃ₐ[F] L, jₐ (Rₐ L) (GaloisCocycle.value ξ σ) =
      b * (conjugate F L U σ b)⁻¹)
    (ha : affineReducedNorm (Rₐ L) b = Units.map (algebraMap F L) a)
    (h : (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    ∃ r : (U).affinePoints (Rₐ K), affineReducedNorm (Rₐ K) r = Units.map (algebraMap F K) a := by
  obtain ⟨y, hy⟩ := GaloisCocycle.exists_galois_coboundary_of_baseChange_isTrivial
    (K := K) (M := M) ξ h
  let B := relativeExtend F L M U b
  let Y := jₐ (Rₐ M) y
  let act := relativeConjugate F K M U
  have hfix (σ : M ≃ₐ[K] M) : act σ (Y⁻¹ * B) = Y⁻¹ * B := by
    let s := σ.restrictScalars F
    let t := s.restrictNormal L
    let v := GaloisCocycle.value ξ t
    have h₁ : jₐ (Rₐ M) (relativeExtend F L M N v) =
        relativeExtend F L M U (jₐ (Rₐ L) v) := by
      change (GaloisCocycle.coverMap F L M ≫ v) ≫ (ι).hom.hom =
        GaloisCocycle.coverMap F L M ≫ (v ≫ (ι).hom.hom)
      exact Category.assoc _ _ _
    have h₂ : jₐ (Rₐ M) (conjugate F M N s y) = act σ Y := by
      change (GaloisCocycle.arrow F M s ≫ y) ≫ (ι).hom.hom =
        GaloisCocycle.arrow F M s ≫ (y ≫ (ι).hom.hom)
      exact Category.assoc _ _ _
    have h₃ : relativeExtend F L M U (conjugate F L U t b) = act σ B := by
      change (GaloisCocycle.coverMap F L M ≫ GaloisCocycle.arrow F L t ≫ b) =
        GaloisCocycle.arrow F M s ≫ GaloisCocycle.coverMap F L M ≫ b
      rw [← Category.assoc, ← Category.assoc, GaloisCocycle.arrow_coverMap]
    have he := congrArg (jₐ (Rₐ M)) (hy σ)
    change jₐ (Rₐ M) (relativeExtend F L M N v) =
      jₐ (Rₐ M) (y * (conjugate F M N s y)⁻¹) at he
    rw [h₁, hb t, map_mul, map_inv, h₃, map_mul, map_inv, h₂] at he
    rw [map_mul, map_inv]
    have he' := congrArg (fun z => Y⁻¹ * z * act σ B) he
    change Y⁻¹ * (B * (act σ B)⁻¹) * act σ B =
      Y⁻¹ * (Y * (act σ Y)⁻¹) * act σ B at he'
    group at he'
    simpa only [zpow_neg_one] using he'.symm
  let D : relativeFixedSubgroup F K M U := ⟨Y⁻¹ * B, hfix⟩
  let r := (relativeFixedEquiv F K M U).symm D
  have hr : relativeExtend F K M U r = Y⁻¹ * B := relativeExtend_descend F K M U D
  have hnorm : Units.map (algebraMap K M).toMonoidHom (affineReducedNorm (Rₐ K) r) =
      Units.map (algebraMap K M).toMonoidHom (Units.map (algebraMap F K).toMonoidHom a) := calc
    _ = affineReducedNorm (Rₐ M) (relativeExtend F K M U r) :=
      (affineReducedNorm_naturality (IsScalarTower.toAlgHom F K M) r).symm
    _ = affineReducedNorm (Rₐ M) B := by
      rw [hr, map_mul, map_inv, show affineReducedNorm (Rₐ M) Y = 1 from
        affineReducedNorm_normOneι y, inv_one, one_mul]
    _ = Units.map (algebraMap L M).toMonoidHom (affineReducedNorm (Rₐ L) b) :=
      affineReducedNorm_naturality (IsScalarTower.toAlgHom F L M) b
    _ = _ := by
      rw [ha]
      apply Units.ext
      exact (IsScalarTower.algebraMap_apply F L M (a : F)).symm.trans
        (IsScalarTower.algebraMap_apply F K M (a : F))
  exact ⟨r, Units.ext ((algebraMap K M).injective (congrArg Units.val hnorm))⟩

end Galois

end Langlands.GroupScheme.CentralSimpleUnits
