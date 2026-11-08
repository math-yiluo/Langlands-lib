import Langlands.GroupScheme.Examples.HermitianRootGroupScheme
import Langlands.GroupScheme.Examples.HermitianRootGeneration
import Langlands.GroupScheme.Examples.SU3RationalPoints

/-! # Rational points and generation of the weighted Hermitian scheme model -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HermitianRoot.SchemeModel

open SU3Root
open SU3Root.SchemeModel (baseAffineTest rationalCoefficientEquiv rationalCoefficientEquiv_bar)

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Middle : Type} [Fintype Middle] [DecidableEq Middle]
  (H : DiagonalForm (fieldInvolution k L) Middle)
  (w : Middle → Lˣ) (hw : ∀ i, (w i : L) = H.weight i)

omit [Fintype Middle] [DecidableEq Middle] in
/-- Actual base-section evaluation returns the original included middle weights. -/
theorem rationalCoefficientEquiv_weight (i : Middle) :
    rationalCoefficientEquiv k L ((tensorForm k L H (baseAffineTest k)).weight i) =
      H.weight i :=
  (rationalCoefficientEquiv k L).commutes (H.weight i)

/-- Rational points of the actual scheme are the original determinant-one isometries over L. -/
def rationalMatrixEquiv :
    rationalPoints (groupScheme k L H w hw) ≃* specialUnitarySubgroup H :=
  ((GaloisPointComparison.rationalCoeffEquiv k (groupScheme k L H w hw)).trans
    (pointsEquiv k L H w hw (baseAffineTest k))).trans
      (specialUnitaryRingEquiv (rationalCoefficientEquiv k L).toRingEquiv
        (rationalCoefficientEquiv_bar k L) (rationalCoefficientEquiv_weight k L H))

/-- The rational matrix evaluates the actual tensor matrix of the ambient inclusion. -/
theorem rationalMatrixEquiv_val (x : rationalPoints (groupScheme k L H w hw)) :
    ((rationalMatrixEquiv k L H w hw x).1 : Matrix (Index Middle) (Index Middle) L) =
      (SpecialLinear.WeilRoot.tensorMatrixEquiv k L (baseAffineTest k)
        (GaloisPointComparison.rationalCoeffEquiv k (groupScheme k L H w hw) x ≫
          (inclusion k L H w hw).hom.hom) : Matrix (Index Middle) (Index Middle)
            (SpecialLinear.WeilRoot.tensorAlgebra k L (baseAffineTest k))).map
              (rationalCoefficientEquiv k L) := by
  unfold rationalMatrixEquiv
  simp only [MulEquiv.trans_apply]
  rw [specialUnitaryRingEquiv_val, pointsEquiv_val]
  rfl

/-- The actual original upper root matrix, as a rational point of the scheme model. -/
def rationalUpper : Parameters H →* rationalPoints (groupScheme k L H w hw) :=
  (rationalMatrixEquiv k L H w hw).symm.toMonoidHom.comp
    ((Parameters.embedding H).codRestrict (specialUnitarySubgroup H)
      (embedding_mem_specialUnitarySubgroup H))

/-- The actual original opposite root matrix, as a rational point of the scheme model. -/
def rationalLower : Parameters H →* rationalPoints (groupScheme k L H w hw) :=
  (rationalMatrixEquiv k L H w hw).symm.toMonoidHom.comp
    ((oppositeEmbedding H).codRestrict (specialUnitarySubgroup H)
      (oppositeEmbedding_mem_specialUnitarySubgroup H))

@[simp] theorem rationalMatrixEquiv_upper (x : Parameters H) :
    (rationalMatrixEquiv k L H w hw (rationalUpper k L H w hw x)).1 =
      Parameters.embedding H x :=
  congrArg Subtype.val ((rationalMatrixEquiv k L H w hw).apply_symm_apply _)

@[simp] theorem rationalMatrixEquiv_lower (x : Parameters H) :
    (rationalMatrixEquiv k L H w hw (rationalLower k L H w hw x)).1 =
      oppositeEmbedding H x :=
  congrArg Subtype.val ((rationalMatrixEquiv k L H w hw).apply_symm_apply _)

theorem rationalUpper_injective : Function.Injective (rationalUpper k L H w hw) := by
  intro x y h
  apply Parameters.embedding_injective
  simpa only [rationalMatrixEquiv_upper] using
    congrArg (fun z => (rationalMatrixEquiv k L H w hw z).1) h

theorem rationalLower_injective : Function.Injective (rationalLower k L H w hw) := by
  intro x y h
  apply oppositeEmbedding_injective H
  simpa only [rationalMatrixEquiv_lower] using
    congrArg (fun z => (rationalMatrixEquiv k L H w hw z).1) h

/-- With anisotropic middle form, any subgroup containing both actual rational root
images is the whole rational-point group. -/
theorem eq_top_of_rational_roots (hH : H.IsAnisotropic)
    (N : Subgroup (rationalPoints (groupScheme k L H w hw)))
    (hupper : (rationalUpper k L H w hw).range ≤ N)
    (hlower : (rationalLower k L H w hw).range ≤ N) : N = ⊤ := by
  let f := (specialUnitarySubgroup H).subtype.comp
    (rationalMatrixEquiv k L H w hw).toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp
    (rationalMatrixEquiv k L H w hw).injective
  have hroot : elementarySubgroup H ≤ N.map f := by
    apply sup_le
    · rintro _ ⟨x, rfl⟩
      exact ⟨rationalUpper k L H w hw x, hupper ⟨x, rfl⟩,
        rationalMatrixEquiv_upper k L H w hw x⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨rationalLower k L H w hw x, hlower ⟨x, rfl⟩,
        rationalMatrixEquiv_lower k L H w hw x⟩
  apply top_unique
  intro x _
  have hx : f x ∈ elementarySubgroup H := by
    rw [elementarySubgroup_eq_specialUnitarySubgroup hH (fieldInvolution_exists_nonfixed k L)]
    exact (rationalMatrixEquiv k L H w hw x).2
  obtain ⟨y, hy, hyx⟩ := hroot hx
  exact hf hyx ▸ hy

/-- The original upper and opposite root images generate all actual rational points. -/
theorem rational_root_ranges_eq_top (hH : H.IsAnisotropic) :
    (rationalUpper k L H w hw).range ⊔ (rationalLower k L H w hw).range = ⊤ :=
  eq_top_of_rational_roots k L H w hw hH _ le_sup_left le_sup_right

end Langlands.GroupScheme.HermitianRoot.SchemeModel
