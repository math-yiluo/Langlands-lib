import Langlands.Geometry.Building.AdjointTranslation

/-! # The same valuation apartment as an affine space under the adjoint torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Geometry.Building Langlands.GroupScheme.RealTorusSpace

namespace Langlands.GroupScheme.IsAdjointSplitTorusImage

variable {k : Type u} [Field k]
variable {G A : GroupScheme (Spec (CommRingCat.of k))}
variable {T T_ad : CommGroupScheme (Spec (CommRingCat.of k))}
variable {q : G ⟶ A} {i : T.toGrp ⟶ G} {j : T_ad.toGrp ⟶ A} {p : T ⟶ T_ad}
variable (h : IsAdjointSplitTorusImage q i j p)
variable [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
variable {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Translation of the original valuation apartment by an actual adjoint torus vector. -/
def adjointTranslate (v : V T_ad) (x : D.Apartment) : D.Apartment :=
  h.translationEquiv.symm v +ᵥ x

/-- The actual torus map gives precisely the original translation on valuations. -/
theorem adjointTranslate_cocharacterMapReal (v : V T) (x : D.Apartment) :
    h.adjointTranslate D (cocharacterMapReal p v) x =
      (Submodule.Quotient.mk v : TranslationSpace i) +ᵥ x := by
  rw [adjointTranslate, ← h.translationEquiv_mk, LinearEquiv.symm_apply_apply]

/-- The same type of valuations is an affine torsor under the actual adjoint
torus vector space. This is explicit data, rather than a global instance. -/
@[instance_reducible]
def adjointAddTorsor : AddTorsor (V T_ad) D.Apartment where
  vadd := h.adjointTranslate D
  zero_vadd x := by
    change h.translationEquiv.symm 0 +ᵥ x = x
    rw [map_zero, zero_vadd]
  add_vadd v w x := by
    change h.translationEquiv.symm (v + w) +ᵥ x =
      h.translationEquiv.symm v +ᵥ (h.translationEquiv.symm w +ᵥ x)
    rw [map_add, add_vadd]
  vsub := h.adjointDisplacement D
  vsub_vadd' x y := by
    change h.translationEquiv.symm (h.translationEquiv (x -ᵥ y)) +ᵥ y = x
    rw [LinearEquiv.symm_apply_apply, vsub_vadd]
  vadd_vsub' v x := by
    change h.translationEquiv ((h.translationEquiv.symm v +ᵥ x) -ᵥ x) = v
    rw [vadd_vsub, LinearEquiv.apply_symm_apply]

/-- In the adjoint torsor the addition is the translated original action. -/
theorem adjointAddTorsor_vadd (v : V T_ad) (x : D.Apartment) :
    letI := h.adjointAddTorsor D
    v +ᵥ x = h.adjointTranslate D v x :=
  rfl

/-- In the adjoint torsor subtraction is the constructed adjoint displacement. -/
theorem adjointAddTorsor_vsub (x y : D.Apartment) :
    letI := h.adjointAddTorsor D
    letI := (h.adjointAddTorsor D).toVSub
    (x -ᵥ y : V T_ad) = h.adjointDisplacement D x y :=
  rfl

variable [Mono j.hom.hom.left]

/-- The inverse coordinate map also intertwines the actual linear actions. -/
theorem translationEquiv_symm_normalizerAction (n : normalizerPoints i) (v : V T_ad) :
    h.translationEquiv.symm (normalizerAction j (h.normalizerPointsMap n) v) =
      translationAction i n (h.translationEquiv.symm v) := by
  apply h.translationEquiv.injective
  rw [LinearEquiv.apply_symm_apply, h.translationEquiv_translationAction,
    LinearEquiv.apply_symm_apply]

/-- The original normalizer action is affine for the actual adjoint translations. -/
theorem smul_adjointTranslate (n : normalizerPoints i) (v : V T_ad) (x : D.Apartment) :
    n • h.adjointTranslate D v x =
      h.adjointTranslate D (normalizerAction j (h.normalizerPointsMap n) v) (n • x) := by
  rw [adjointTranslate, adjointTranslate, D.smul_vadd,
    h.translationEquiv_symm_normalizerAction]

/-- Package the original action on the same valuation points as affine
automorphisms with its actual adjoint normalizer linear part. -/
def adjointNormalizerAffineEquiv :
    letI := h.adjointAddTorsor D
    normalizerPoints i →* (D.Apartment ≃ᵃ[ℝ] D.Apartment) :=
  letI := h.adjointAddTorsor D
  { toFun n :=
      { toFun := fun x => n • x
        invFun := fun x => n⁻¹ • x
        left_inv := fun x => inv_smul_smul n x
        right_inv := fun x => smul_inv_smul n x
        linear := normalizerAction j (h.normalizerPointsMap n)
        map_vadd' := fun x v => h.smul_adjointTranslate D n v x }
    map_one' := AffineEquiv.ext fun x => one_smul (normalizerPoints i) x
    map_mul' n m := AffineEquiv.ext fun x => mul_smul n m x }

/-- The adjoint affine action has the original normalizer action on valuation points. -/
theorem adjointNormalizerAffineEquiv_apply (n : normalizerPoints i) (x : D.Apartment) :
    letI := h.adjointAddTorsor D
    h.adjointNormalizerAffineEquiv D n x = n • x :=
  rfl

/-- Its derivative is the actual action of the actual image normalizer point. -/
theorem adjointNormalizerAffineEquiv_linear (n : normalizerPoints i) :
    letI := h.adjointAddTorsor D
    (h.adjointNormalizerAffineEquiv D n).linear =
      normalizerAction j (h.normalizerPointsMap n) :=
  rfl

end Langlands.GroupScheme.IsAdjointSplitTorusImage
