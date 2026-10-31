import Langlands.AlgebraicGeometry.TangentKernelCotangentSurjectivityStatement
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Trivial rational tangent kernel and actual stalk cotangents -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The actual dual-number tangent kernel detects surjectivity of the actual
stalk cotangent map, without a finiteness hypothesis. -/
theorem tangentKernel_cotangentSurjectivity :
    TangentKernelCotangentSurjectivityStatement.{u} := by
  intro K _ X Y p q f h x hx hker
  let z := x (IsLocalRing.closedPoint K)
  let := Picard.stalkAlgebraOver p z
  let := Picard.stalkAlgebraOver q (f z)
  let r := Picard.rationalStalkAugmentation p x hx
  let a := Picard.stalkMapAlgHomOver p q f h z
  change Function.Surjective (augmentationCotangentMap r a)
  apply LinearMap.dualMap_injective_iff.mp
  apply (injective_iff_map_eq_zero _).mpr
  intro ell hell
  have Halg : (cotangentDualNumberLift r ell).comp a =
      (TrivSqZeroExt.inlAlgHom K K K).comp (r.comp a) :=
    (cotangentDualNumberLift_comp_eq_constant_iff r ell a).mpr hell
  let t := Picard.rationalStalkTangentMap p x hx
    ⟨cotangentDualNumberLift r ell, cotangentDualNumberLift_projection r ell⟩
  have Hr : Spec.map (CommRingCat.ofHom (r.comp a).toRingHom) ≫
      Y.fromSpecStalk (f z) = x ≫ f := by
    change Spec.map (CommRingCat.ofHom
      ((Picard.rationalStalkAugmentation p x hx).comp
        (Picard.stalkMapAlgHomOver p q f h z)).toRingHom) ≫ _ = _
    rw [Picard.rationalStalkAugmentation_comp_stalkMapAlgHomOver]
    exact Picard.rationalStalkAugmentation_spec_comp q (x ≫ f)
      (Picard.isRationalPoint_comp_over p q f h x hx)
  have Htf : t.val ≫ f = (Picard.dualNumberProjection K ≫ x) ≫ f := by
    calc
      t.val ≫ f = Spec.map (CommRingCat.ofHom
          ((cotangentDualNumberLift r ell).comp a).toRingHom) ≫
          Y.fromSpecStalk (f z) :=
        (Picard.spec_stalkMapAlgHomOver_comp p q f h z
          (cotangentDualNumberLift r ell)).symm
      _ = (Picard.dualNumberProjection K ≫
          Spec.map (CommRingCat.ofHom (r.comp a).toRingHom)) ≫
          Y.fromSpecStalk (f z) := by
        rw [(Picard.spec_map_eq_constant_tangent_iff (r.comp a)
          ((cotangentDualNumberLift r ell).comp a)).mpr Halg]
      _ = (Picard.dualNumberProjection K ≫ x) ≫ f := by
        rw [Category.assoc, Hr, ← Category.assoc]
  have Ht : t.val = Picard.dualNumberProjection K ≫ x := hker t.val t.property Htf
  exact (cotangentDualNumberLift_eq_constant_iff r ell).mp
    ((Picard.rationalStalkTangentMap_eq_constant_iff p x hx _).mp Ht)

end Langlands.AlgebraicGeometry
