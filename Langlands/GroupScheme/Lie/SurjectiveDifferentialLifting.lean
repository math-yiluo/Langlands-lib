import Langlands.GroupScheme.Lie.SurjectiveDifferentialStatement
import Langlands.GroupScheme.Lie.ScalarExtension
import Langlands.GroupScheme.Lie.SubgroupEqualityProof
import Langlands.GroupScheme.Torus.FixedSubgroupSmoothAlgebraBridge
import Mathlib.LinearAlgebra.Projection

/-! # Square-zero lifting from a surjective actual differential -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

section Coefficients

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType H.X.hom] [LocallyOfFiniteType G.X.hom]
  (f : H ⟶ G) (A : Type u) [CommRing A] [Algebra k A]

/-- The actual differential commutes with scalar extension of its source and target. -/
theorem targetMapLinear_kernelScalarExtension
    (x : A ⊗[k] Additive (lieKernel H k)) :
    targetMapLinear f A (kernelScalarExtension H A x) =
      kernelScalarExtension G A ((targetMapLinear f k).baseChange A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [kernelScalarExtension_tmul, LinearMap.baseChange_tmul,
      map_smul, lieKernelTargetLinear_map]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Surjectivity at the ground field extends to every coefficient algebra. -/
theorem targetMapLinear_surjective_coefficients
    (hf : Function.Surjective (targetMapLinear f k)) :
    Function.Surjective (targetMapLinear f A) := by
  intro x
  obtain ⟨y, hy⟩ := LinearMap.lTensor_surjective A hf ((kernelScalarExtension G A).symm x)
  refine ⟨kernelScalarExtension H A y, ?_⟩
  change (targetMapLinear f k).baseChange A y = _ at hy
  rw [targetMapLinear_kernelScalarExtension, hy, LinearEquiv.apply_symm_apply]

end Coefficients

section SquareZeroAlgebra

variable {k C B : Type u} [Field k] [CommRing C] [CommRing B]
  [Algebra k C] [Algebra k B]

/-- Adding a square-zero-valued identity derivation to an augmentation gives an algebra map. -/
def squareZeroPoint (ε : C →ₐ[k] k) (d : C →ₗ[k] B)
    (hd : ∀ a b, d (a * b) = ε a • d b + ε b • d a)
    (I : Ideal B) (hI : I ^ 2 = ⊥) (hdI : ∀ a, d a ∈ I) : C →ₐ[k] B where
  toFun a := algebraMap k B (ε a) + d a
  map_zero' := by simp
  map_one' := by
    have h := hd 1 1
    simp only [map_one, one_mul, one_smul] at h
    have hd1 : d 1 = 0 := by linear_combination -h
    simp [hd1]
  map_add' a b := by simp only [map_add]; abel
  map_mul' a b := by
    have hz : d a * d b = 0 := by
      have hm := Ideal.mul_mem_mul (hdI a) (hdI b)
      rw [← pow_two, hI] at hm
      exact hm
    simp only [map_mul, hd, Algebra.smul_def]
    linear_combination -hz
  commutes' r := by
    have h := hd 1 1
    simp only [map_one, one_mul, one_smul] at h
    have hd1 : d 1 = 0 := by linear_combination -h
    have hdr : d (algebraMap k C r) = 0 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hd1, smul_zero]
    simp [hdr]

/-- The difference from an augmentation satisfies Leibniz in a square-zero kernel. -/
theorem augmentationDifference_leibniz (ε : C →ₐ[k] k) (x : C →ₐ[k] B)
    (I : Ideal B) (hI : I ^ 2 = ⊥)
    (hx : ∀ a, x a - algebraMap k B (ε a) ∈ I) (a b : C) :
    (x.toLinearMap - ((Algebra.ofId k B).comp ε).toLinearMap) (a * b) =
      ε a • (x.toLinearMap - ((Algebra.ofId k B).comp ε).toLinearMap) b +
      ε b • (x.toLinearMap - ((Algebra.ofId k B).comp ε).toLinearMap) a := by
  have hz : (x a - algebraMap k B (ε a)) * (x b - algebraMap k B (ε b)) = 0 := by
    have hm := Ideal.mul_mem_mul (hx a) (hx b)
    rw [← pow_two, hI] at hm
    exact hm
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
    Algebra.ofId_apply, map_mul, Algebra.smul_def]
  linear_combination hz

end SquareZeroAlgebra

section SquareZeroGroups

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType H.X.hom] [LocallyOfFiniteType G.X.hom]
  (f : H ⟶ G) (B : Type u) [CommRing B] [Algebra k B]

attribute [local instance] coordinateOriginAlgebra

/-- Surjectivity of the actual differential lifts derivations at the augmentation. -/
theorem exists_identityDerivation_lift
    (hf : Function.Surjective (targetMapLinear f k)) (d : IdentityDerivation G (A := B)) :
    ∃ e : IdentityDerivation H (A := B), ∀ a, e (restrictionMap f a) = d a := by
  obtain ⟨y, hy⟩ := targetMapLinear_surjective_coefficients f B hf
    ((kernelDerivationLinearEquiv G).symm d)
  refine ⟨kernelDerivationLinearEquiv H y, fun a => ?_⟩
  have h := congrArg (fun z => kernelDerivationLinearEquiv G z a) hy
  rw [LinearEquiv.apply_symm_apply] at h
  change (pointCoordinates G (y.toMul.val ≫ f.hom.hom) a).snd = d a at h
  rw [pointCoordinates_comp_hom] at h
  exact h

/-- Identity-kernel points lift across a square-zero ideal when the differential is onto. -/
theorem exists_squareZeroKernel_lift
    (hf : Function.Surjective (targetMapLinear f k)) (I : Ideal B) (hI : I ^ 2 = ⊥)
    (x : AffinePoints G B) (hx : affineMap G (Ideal.Quotient.mkₐ k I) x = 1) :
    ∃ y : AffinePoints H B,
      y ≫ f.hom.hom = x ∧ affineMap H (Ideal.Quotient.mkₐ k I) y = 1 := by
  let ε := coordinateOrigin G
  let X := pointCoordinates G x
  have hxI : ∀ a, X a - algebraMap k B (ε a) ∈ I := by
    intro a
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := congrArg (fun z => pointCoordinates G z a) hx
    rw [pointCoordinates_naturality, pointCoordinates_one] at h
    change Ideal.Quotient.mk I (X a) = algebraMap k (B ⧸ I) (ε a) at h
    simpa only [map_sub, Ideal.Quotient.mk_algebraMap, sub_eq_zero] using h
  let d : IdentityDerivation G (A := B) := Derivation.mk'
    (X.toLinearMap - ((Algebra.ofId (CommRingCat.of k) B).comp ε).toLinearMap)
    (by
      intro a b
      change _ = algebraMap k B (ε a) * _ + algebraMap k B (ε b) * _
      simpa only [Algebra.smul_def] using augmentationDifference_leibniz ε X I hI hxI a b)
  obtain ⟨e, he⟩ := exists_identityDerivation_lift f B hf d
  let V := I.restrictScalars k
  obtain ⟨W, hW⟩ := V.exists_isCompl
  let p : B →ₗ[k] B := V.projection W hW
  let e' : coordinateAlgebra H →ₗ[k] B := p.comp e.toLinearMap
  have he' : ∀ a b, e' (a * b) = coordinateOrigin H a • e' b +
      coordinateOrigin H b • e' a := by
    intro a b
    change p (e (a * b)) = _
    rw [e.leibniz]
    change p (algebraMap k B (coordinateOrigin H a) * e b +
      algebraMap k B (coordinateOrigin H b) * e a) = _
    simp only [← Algebra.smul_def, map_add, map_smul]
    rfl
  let Y := squareZeroPoint (coordinateOrigin H) e' he' I hI
    (fun a => Submodule.projection_apply_mem hW (e a))
  refine ⟨(pointCoordinates H).symm Y, ?_, ?_⟩
  · apply (pointCoordinates G).injective
    rw [pointCoordinates_comp_hom, Equiv.apply_symm_apply]
    ext a
    change algebraMap k B (coordinateOrigin H (restrictionMap f a)) +
      p (e (restrictionMap f a)) = X a
    rw [he]
    have hε := DFunLike.congr_fun (coordinateOrigin_comp_restrictionMap f) a
    change coordinateOrigin H (restrictionMap f a) = ε a at hε
    rw [hε]
    change algebraMap k B (ε a) + p (X a - algebraMap k B (ε a)) = X a
    rw [Submodule.projection_apply_of_mem_left hW (hxI a)]
    exact add_sub_cancel _ _
  · apply (pointCoordinates H).injective
    rw [pointCoordinates_naturality, Equiv.apply_symm_apply, pointCoordinates_one]
    ext a
    change Ideal.Quotient.mk I (algebraMap k B (coordinateOrigin H a) + e' a) = _
    have heI : e' a ∈ I := Submodule.projection_apply_mem hW (e a)
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr heI, add_zero]
    exact (IsScalarTower.algebraMap_apply k B (B ⧸ I) _).symm

end SquareZeroGroups

section FormalSmoothness

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType H.X.hom] [LocallyOfFiniteType G.X.hom]
  (f : H ⟶ G)

/-- Square-zero group correction proves relative formal smoothness. -/
theorem restrictionMap_formallySmooth_of_surjective_differential
    (hH : Smooth H.X.hom) (hf : Function.Surjective (targetMapLinear f k)) :
    RingHom.FormallySmooth (restrictionMap f).toRingHom := by
  let : Algebra (coordinateAlgebra G) (coordinateAlgebra H) :=
    (restrictionMap f).toRingHom.toAlgebra
  let : IsScalarTower k (coordinateAlgebra G) (coordinateAlgebra H) :=
    IsScalarTower.of_algHom (restrictionMap f)
  let := hH
  let : Algebra.Smooth k (coordinateAlgebra H) :=
    Diagonalizable.FixedSubgroupSmoothAlgebraBridge.coordinateAlgebra_smooth H
  change Algebra.FormallySmooth (coordinateAlgebra G) (coordinateAlgebra H)
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ I hI z => ?_
  algebraize [(algebraMap (coordinateAlgebra G) B).comp (algebraMap k (coordinateAlgebra G))]
  let q := Ideal.Quotient.mkₐ k I
  obtain ⟨w, hw⟩ := Algebra.FormallySmooth.comp_surjective k (coordinateAlgebra H) I hI
    (z.restrictScalars k)
  let y : AffinePoints H B := (pointCoordinates H).symm w
  let x : AffinePoints G B := (pointCoordinates G).symm
    (IsScalarTower.toAlgHom k (coordinateAlgebra G) B)
  have hred : affineMap G q x = affineMap G q (y ≫ f.hom.hom) := by
    apply (pointCoordinates G).injective
    rw [pointCoordinates_naturality, pointCoordinates_naturality,
      pointCoordinates_comp_hom]
    dsimp only [x, y]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← AlgHom.comp_assoc]
    change q.comp (IsScalarTower.toAlgHom k (coordinateAlgebra G) B) =
      (q.comp w).comp (restrictionMap f)
    change q.comp w = z.restrictScalars k at hw
    rw [hw]
    ext a
    exact (z.commutes a).symm
  obtain ⟨v, hv, hv0⟩ := exists_squareZeroKernel_lift f B hf I hI
    (x * (y ≫ f.hom.hom)⁻¹) (by rw [map_mul, map_inv, hred, mul_inv_cancel])
  change affineMap H q v = 1 at hv0
  let t := v * y
  have ht : t ≫ f.hom.hom = x := by
    dsimp only [t]
    rw [mul_comp_hom, hv, inv_mul_cancel_right]
  have ht0 : affineMap H q t = affineMap H q y := by
    simp only [t, map_mul, hv0, one_mul]
  let w' := pointCoordinates H t
  have hw' : w'.comp (restrictionMap f) = IsScalarTower.toAlgHom k (coordinateAlgebra G) B := by
    dsimp only [w']
    rw [← pointCoordinates_comp_hom f t, ht]
    exact Equiv.apply_symm_apply _ _
  let z' : coordinateAlgebra H →ₐ[coordinateAlgebra G] B :=
    { w'.toRingHom with commutes' := fun a => DFunLike.congr_fun hw' a }
  refine ⟨z', ?_⟩
  ext a
  have h := congrArg (fun z => pointCoordinates H z a) ht0
  rw [pointCoordinates_naturality, pointCoordinates_naturality,
    Equiv.apply_symm_apply, hw] at h
  exact h

/-- Finite presentation promotes the lifting result to actual scheme smoothness. -/
theorem smooth_of_surjective_differential
    (hH : Smooth H.X.hom) (hf : Function.Surjective (targetMapLinear f k)) :
    Smooth f.hom.hom.left := by
  let : Algebra (coordinateAlgebra G) (coordinateAlgebra H) :=
    (restrictionMap f).toRingHom.toAlgebra
  let : IsScalarTower k (coordinateAlgebra G) (coordinateAlgebra H) :=
    IsScalarTower.of_algHom (restrictionMap f)
  let : Algebra.FiniteType k (coordinateAlgebra G) := coordinateAlgebraFiniteType G
  let : Algebra.FiniteType k (coordinateAlgebra H) := coordinateAlgebraFiniteType H
  let : IsNoetherianRing (coordinateAlgebra G) :=
    Algebra.FiniteType.isNoetherianRing k (coordinateAlgebra G)
  let : Algebra.FiniteType (coordinateAlgebra G) (coordinateAlgebra H) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (coordinateAlgebra G) (coordinateAlgebra H)
  let : Algebra.FinitePresentation (coordinateAlgebra G) (coordinateAlgebra H) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.FormallySmooth (coordinateAlgebra G) (coordinateAlgebra H) :=
    restrictionMap_formallySmooth_of_surjective_differential f hH hf
  let : Algebra.Smooth (coordinateAlgebra G) (coordinateAlgebra H) := {}
  have hφ : RingHom.Smooth (restrictionMap f).toRingHom :=
    (inferInstance : Algebra.Smooth (coordinateAlgebra G) (coordinateAlgebra H))
  have hs : Smooth ((algSpec (CommRingCat.of k)).map
      (CommAlgCat.ofHom (restrictionMap f)).op).left := by
    change Smooth (Spec.map (CommRingCat.ofHom (restrictionMap f).toRingHom))
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr hφ
  let := hs
  have : IsIso (coordinateIso H).inv.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (coordinateIso H).inv))
  have : IsIso (coordinateIso G).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (coordinateIso G).hom))
  have h : f.hom.hom = (coordinateIso H).inv ≫
      (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (restrictionMap f)).op ≫
        (coordinateIso G).hom := by
    rw [restrictionMap_spec, Iso.inv_hom_id_assoc]
  have h' : f.hom.hom.left = (coordinateIso H).inv.left ≫
      ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (restrictionMap f)).op).left ≫
        (coordinateIso G).hom.left := congrArg Over.Hom.left h
  rw [h']
  infer_instance

end FormalSmoothness

end Langlands.GroupScheme.Lie
