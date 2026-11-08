import Langlands.GroupScheme.Examples.HermitianRootModelRadicalGeneration
import Langlands.GroupScheme.Examples.HermitianRootReductive

/-! # Rational parabolic radical generation for the actual Hermitian models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HermitianRoot.SchemeModel

open SU3Root

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (fieldInvolution k L) Middle)
  (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)
  {A : GroupScheme (Spec (CommRingCat.of k))}

/-- Connected reductivity follows from an actual isomorphism to the Hermitian model. -/
theorem isConnectedReductive_of_model_iso (e : A ≅ groupScheme k L H w hw) :
    IsConnectedReductive A := by
  have h := isConnectedReductive k L H w hw
  have he := isIso_left_of_iso e
  have hwA : A.X.hom = e.hom.hom.hom.left ≫ (groupScheme k L H w hw).X.hom :=
    (Over.w e.hom.hom.hom).symm
  have := h.smooth
  have := h.isAffineHom
  have := h.connectedSpace
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hwA]
    infer_instance
  · rw [hwA]
    infer_instance
  · let φ := Scheme.homeoOfIso (asIso e.hom.hom.hom.left)
    exact φ.symm.surjective.connectedSpace φ.symm.continuous
  · exact HasTrivialUnipotentRadical.of_iso
      ((GroupScheme.baseChange (toAlgebraicClosure k)).mapIso e)
      h.hasTrivialGeometricUnipotentRadical

/-- Rational parabolic radicals generate every actual anisotropic-middle Hermitian model. -/
theorem parabolicElementarySubgroup_eq_top (hH : H.IsAnisotropic) :
    parabolicElementarySubgroup (groupScheme k L H w hw) = ⊤ :=
  parabolicElementarySubgroup_eq_top_of_iso k L H w hw hH
    (isConnectedReductive k L H w hw) (Iso.refl _)

/-- A specified model isomorphism suffices for generation; reductivity is proved here. -/
theorem parabolicElementarySubgroup_eq_top_of_model_iso (hH : H.IsAnisotropic)
    (e : A ≅ groupScheme k L H w hw) : parabolicElementarySubgroup A = ⊤ :=
  parabolicElementarySubgroup_eq_top_of_iso k L H w hw hH
    (isConnectedReductive_of_model_iso k L H w hw e) e

/-- The actual rational group is its actual parabolic elementary subgroup. -/
def rationalPointsEquivParabolicElementarySubgroup (hH : H.IsAnisotropic) :
    rationalPoints (groupScheme k L H w hw) ≃*
      parabolicElementarySubgroup (groupScheme k L H w hw) :=
  Subgroup.topEquiv.symm.trans
    (MulEquiv.subgroupCongr (parabolicElementarySubgroup_eq_top k L H w hw hH).symm)

@[simp] theorem rationalPointsEquivParabolicElementarySubgroup_apply_coe
    (hH : H.IsAnisotropic) (x : rationalPoints (groupScheme k L H w hw)) :
    (rationalPointsEquivParabolicElementarySubgroup k L H w hw hH x :
      rationalPoints (groupScheme k L H w hw)) = x := rfl

/-- Containing every rational parabolic radical of a group with this model
forces an arbitrary subgroup to be the whole rational group. -/
theorem eq_top_of_parabolic_radicals_of_model_iso (hH : H.IsAnisotropic)
    (e : A ≅ groupScheme k L H w hw) (N : Subgroup (rationalPoints A))
    (hrad : ∀ (P U : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ A) (r : U ⟶ P),
      IsParabolicSubgroup p → LeviSubgroup.IsGeometricUnipotentRadical r →
        (rationalPoints.map (r ≫ p)).range ≤ N) : N = ⊤ :=
  eq_top_of_parabolic_radicals_of_iso k L H w hw hH
    (isConnectedReductive_of_model_iso k L H w hw e) e N hrad

end Langlands.GroupScheme.HermitianRoot.SchemeModel
