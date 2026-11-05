import Langlands.GroupScheme.Rational.CommutativePTorsionEmbeddingStatement
import Langlands.GroupScheme.CentralIsogeny.KernelTorsion
import Langlands.GroupScheme.Absolute.BorelFieldExtensionDescent

/-! # Cocommutativity and torsion in affine Hopf coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineCoordinates

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- Coordinate algebra maps are actual points of the affine group scheme. -/
def coordinatePointEquiv (B : Type u) [CommRing B] [Algebra k B] :
    WithConv (hopfAlgebra G →ₐ[k] B) ≃*
      ((Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of k)) ⟶ G.X) :=
  (Spec.mapMulEquiv (R := k) (S := hopfAlgebra G) (T := B)).trans
    ((yonedaGrp.mapIso (hopfSpecIso G)).app
      (op ((Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of k))))).groupIsoToMulEquiv

/-- A scalar-extended coordinate point, regarded as an actual `Spec L` point of `G`. -/
def baseChangePointHom (L : Type u) [Field L] [Algebra k L] :
    WithConv (L ⊗[k] hopfAlgebra G →ₐ[L] L) →*
      ((Spec (CommRingCat.of L)).asOver (Spec (CommRingCat.of k)) ⟶ G.X) :=
  (coordinatePointEquiv G L).toMonoidHom.comp
    (BorelFieldExtension.res k L (hopfAlgebra G) L)

/-- Scalar-extended coordinate points are determined by their actual scheme point. -/
theorem baseChangePointHom_injective (L : Type u) [Field L] [Algebra k L] :
    Function.Injective (baseChangePointHom G L) :=
  (coordinatePointEquiv G L).injective.comp BorelFieldExtension.res_injective

/-- The coordinate Hopf algebra of a commutative affine group is cocommutative. -/
theorem hopfAlgebra_isCocomm [IsCommMonObj G.X] :
    Coalgebra.IsCocomm k (hopfAlgebra G) := by
  let A := hopfAlgebra G
  let e := hopfSpecIso G
  let Y := (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k))
  let f : Y ⟶ G.X := e.hom.hom.hom
  have : IsMonHom f := e.hom.hom.isMonHom_hom
  have hgf : e.inv.hom.hom ≫ f = 𝟙 G.X := congrArg (fun φ => φ.hom.hom) e.inv_hom_id
  have hfg : f ≫ e.inv.hom.hom = 𝟙 Y := congrArg (fun φ => φ.hom.hom) e.hom_inv_id
  have : IsIso f := ⟨e.inv.hom.hom, hfg, hgf⟩
  exact isCocomm_of_commute A fun a b => by
    apply (cancel_mono f).1
    rw [MonObj.mul_comp, MonObj.mul_comp, mul_comm]

/-- An exponent on all relative tests kills the convolution power of every
algebra-valued coordinate point. -/
theorem convPow_algHom_eq_one_of_uniformExponent {n : ℕ}
    (hG : HasUniformPowerExponent G n) (B : Type u) [CommRing B] [Algebra k B]
    (φ : hopfAlgebra G →ₐ[k] B) : toConv φ ^ n = 1 := by
  let A := hopfAlgebra G
  let e := hopfSpecIso G
  let Y := (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of k))
  let f : Y ⟶ G.X := e.hom.hom.hom
  have : IsMonHom f := e.hom.hom.isMonHom_hom
  have hgf : e.inv.hom.hom ≫ f = 𝟙 G.X := congrArg (fun ψ => ψ.hom.hom) e.inv_hom_id
  have hfg : f ≫ e.inv.hom.hom = 𝟙 Y := congrArg (fun ψ => ψ.hom.hom) e.hom_inv_id
  have : IsIso f := ⟨e.inv.hom.hom, hfg, hgf⟩
  have hx : Spec.mapMulEquiv (R := k) (S := A) (T := B) (toConv φ ^ n) = 1 := by
    rw [map_pow]
    apply (cancel_mono f).1
    rw [MonObj.pow_comp, hG, MonObj.one_comp]
  exact (Spec.mapMulEquiv (R := k) (S := A) (T := B)).injective
    (by rw [hx, map_one])

/-- Restriction of scalar-extended coordinate points preserves the uniform
exponent. This uses the given exponent on the original `Spec L` test. -/
theorem convPow_baseChange_algHom_eq_one_of_uniformExponent {n : ℕ}
    (hG : HasUniformPowerExponent G n) (L : Type u) [Field L] [Algebra k L]
    (φ : L ⊗[k] hopfAlgebra G →ₐ[L] L) : toConv φ ^ n = 1 := by
  apply BorelFieldExtension.res_injective (k := k) (K := L)
    (H := hopfAlgebra G) (C := L)
  rw [map_pow, map_one]
  exact convPow_algHom_eq_one_of_uniformExponent G hG L (BorelFieldExtension.resFun φ)

/-- The corresponding power of the scalar-extended point as a linear functional
is the convolution identity, as required by primitive-generation descent. -/
theorem convPow_baseChange_linearMap_eq_one_of_uniformExponent {n : ℕ}
    (hG : HasUniformPowerExponent G n) (L : Type u) [Field L] [Algebra k L]
    (φ : L ⊗[k] hopfAlgebra G →ₐ[L] L) : toConv φ.toLinearMap ^ n = 1 := by
  have hp := convPow_baseChange_algHom_eq_one_of_uniformExponent G hG L φ
  have h := AlgHom.toLinearMap_convPow (toConv φ) n
  rw [hp, AlgHom.toLinearMap_convOne] at h
  exact h.symm

end Langlands.GroupScheme.AffineCoordinates
