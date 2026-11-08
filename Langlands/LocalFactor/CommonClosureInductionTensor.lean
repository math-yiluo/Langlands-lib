import Langlands.LocalFactor.CommonClosureInductionTwist
import Langlands.VirtualRepresentation.ExactTensor
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The projection formula for tensor products and induction

For a finite-index subgroup `S` of `G`, a representation `A` of `G` and a
representation `B` of `S`, the actual equivariant-function model satisfies
`A ⊗ Ind_S B ≅ Ind_S (A|_S ⊗ B)`, by `a ⊗ f ↦ (g ↦ A(g) a ⊗ f(g))`.
This descends to the actual exact virtual groups, and on the common-closure
exact virtual groups gives
`w ⊗ induce x = induce (w|_{W_L} ⊗ x)`.
-/

noncomputable section

open scoped TensorProduct

universe uK uG uH uJ uV uW uF

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G]

/-- The action of a group element as a linear automorphism. -/
def actionLinearEquiv (A : FiniteRepresentation.{uK, uG, uW} K G) (g : G) : A ≃ₗ[K] A :=
  LinearEquiv.ofLinearMap (A.representation g) (A.representation g⁻¹)
    (by ext x; exact A.representation.self_inv_apply g x)
    (by ext x; exact A.representation.inv_self_apply g x)

variable (S : Subgroup G) [S.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The linear equivalence of the projection formula, built from coset coordinates:
`A ⊗ (Cosets → B) ≅ Cosets → A ⊗ B`, twisted at each coset by its representative. -/
def induceTensorLinearEquiv (φ : S →* G)
    (A : FiniteRepresentation.{uK, uG, uW} K G)
    (B : FiniteRepresentation.{uK, uG, uV} K S) :
    tensor A (induce S B) ≃ₗ[K] induce S (tensor (restrict φ A) B) := by
  classical
  exact (TensorProduct.congr (LinearEquiv.refl K A) (Induction.coordinates S B)) ≪≫ₗ
      TensorProduct.piRight K K A (fun _ : Induction.Cosets S => B) ≪≫ₗ
      LinearEquiv.piCongrRight (fun q => TensorProduct.congr
        (actionLinearEquiv A q.out) (LinearEquiv.refl K B)) ≪≫ₗ
      (Induction.coordinates S (tensor (restrict φ A) B)).symm

theorem induceTensorLinearEquiv_tmul (φ : S →* G) (hφ : ∀ s : S, φ s = s)
    (A : FiniteRepresentation.{uK, uG, uW} K G)
    (B : FiniteRepresentation.{uK, uG, uV} K S)
    (a : A) (f : Representation.coindV S.subtype B.representation) (g : G) :
    (induceTensorLinearEquiv S φ A B (a ⊗ₜ f)).val g =
      A.representation g a ⊗ₜ f.val g := by
  have hf := f.property (Induction.factor S g) (Induction.coset S g).out
  change f.val ((Induction.factor S g : G) * (Induction.coset S g).out) = _ at hf
  have h1 : A.representation (φ (Induction.factor S g))
      (A.representation (Induction.coset S g).out a) = A.representation g a := by
    rw [hφ, ← Module.End.mul_apply, ← map_mul, Induction.factor_mul_out]
  have h2 : B.representation (Induction.factor S g) (f.val (Induction.coset S g).out) =
      f.val g := by
    rw [← hf, Induction.factor_mul_out]
  classical
  change A.representation (φ (Induction.factor S g))
      (A.representation (Induction.coset S g).out a) ⊗ₜ[K]
    B.representation (Induction.factor S g) (f.val (Induction.coset S g).out) = _
  rw [h1, h2]
  rfl

/-- The projection formula `A ⊗ Ind_S B ≅ Ind_S (A|_S ⊗ B)` on the actual
equivariant-function model, for any restriction along a map acting as the inclusion. -/
def induceTensorEquiv (φ : S →* G) (hφ : ∀ s : S, φ s = s)
    (A : FiniteRepresentation.{uK, uG, uW} K G)
    (B : FiniteRepresentation.{uK, uG, uV} K S) :
    Equiv (tensor A (induce S B)) (induce S (tensor (restrict φ A) B)) :=
  Representation.Equiv.mk (induceTensorLinearEquiv S φ A B) (by
    intro h
    apply TensorProduct.ext'
    intro a f
    apply Subtype.ext
    funext g
    change (induceTensorLinearEquiv S φ A B (A.representation h a ⊗ₜ
        Representation.coind S.subtype B.representation h f)).val g =
      (induceTensorLinearEquiv S φ A B (a ⊗ₜ f)).val (g * h)
    refine (induceTensorLinearEquiv_tmul S φ hφ A B _ _ g).trans
      (Eq.trans ?_ (induceTensorLinearEquiv_tmul S φ hφ A B a f (g * h)).symm)
    change A.representation g (A.representation h a) ⊗ₜ[K] f.val (g * h) =
      A.representation (g * h) a ⊗ₜ[K] f.val (g * h)
    rw [map_mul, Module.End.mul_apply])

end Langlands.FiniteRepresentation

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} {H : Type uH} {J : Type uJ} [Field K]
  [Monoid G] [Monoid H] [Monoid J]

/-- Restriction of a tensor product with a restricted left factor, rebracketed. -/
def restrictTensorEquiv (ψ : H →* G) (φ : J →* H)
    (A : FiniteRepresentation.{uK, uG, uW} K G)
    (B : FiniteRepresentation.{uK, uH, uV} K H) :
    Equiv (tensor (restrict (ψ.comp φ) A) (restrict φ B))
      (restrict φ (tensor (restrict ψ A) B)) :=
  Representation.Equiv.mk (LinearEquiv.refl K _) (fun _ => rfl)

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The projection formula on actual continuous exact virtual groups:
`w ⊗ Ind_S x = Ind_S (w|_S ⊗ x)`. -/
theorem continuousTensor_continuousInduce (S : Subgroup G) [S.FiniteIndex]
    (hS : IsOpen (S : Set G)) (w : Continuous.{uG, uW} G)
    (x : Continuous.{uG, uV} S) :
    continuousTensor w (continuousInduce S hS x) =
      continuousInduce S hS
        (continuousTensor (continuousRestrict ⟨S.subtype, continuous_subtype_val⟩ w) x) := by
  have hgen : ∀ (A : {A : FiniteRepresentation.{0, uG, uW} ℂ G // A.IsContinuous})
      (B : {B : FiniteRepresentation.{0, uG, uV} ℂ S // B.IsContinuous}),
      continuousTensor (ofRepresentation _ A) (continuousInduce S hS (ofRepresentation _ B)) =
        continuousInduce S hS (continuousTensor
          (continuousRestrict ⟨S.subtype, continuous_subtype_val⟩ (ofRepresentation _ A))
          (ofRepresentation _ B)) := by
    intro A B
    unfold continuousInduce continuousRestrict
    rw [induce_ofRepresentation, restrict_ofRepresentation]
    erw [continuousTensor_ofRepresentation, continuousTensor_ofRepresentation]
    rw [induce_ofRepresentation]
    exact ofRepresentation_eq_of_equiv _
      (induceTensorEquiv S S.subtype (fun _ => rfl) A.val B.val)
  have hw : ∀ B : {B : FiniteRepresentation.{0, uG, uV} ℂ S // B.IsContinuous},
      (continuousTensor.flip (continuousInduce S hS (ofRepresentation _ B)) :
          Continuous.{uG, uW} G →ₗ[ℤ] _) =
        (continuousInduce S hS).comp ((continuousTensor.flip (ofRepresentation _ B)).comp
          (continuousRestrict ⟨S.subtype, continuous_subtype_val⟩)) := by
    intro B
    apply hom_ext _
    intro c
    induction c using Quotient.inductionOn with
    | h A => exact hgen A B
  have hx : (continuousTensor w).comp (continuousInduce S hS) =
      (continuousInduce S hS).comp
        (continuousTensor (continuousRestrict ⟨S.subtype, continuous_subtype_val⟩ w)) := by
    apply hom_ext _
    intro c
    induction c using Quotient.inductionOn with
    | h B => exact LinearMap.congr_fun (hw B) w
  exact LinearMap.congr_fun hx x

end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.LocalFactor.CommonClosure

open VirtualRepresentation FiniteRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The common-closure projection formula on actual exact virtual groups:
tensoring an induced class by `w` is inducing the class tensored by the
restriction of `w`. -/
theorem continuousTensorSame_induce (E L : Extension F) (h : E.field ≤ L.field)
    (w : Virtual.{uF, uV} F E) (x : Virtual.{uF, uV} F L) :
    ExactGrothendieckGroup.continuousTensorSame w (induce F E L h x) =
      induce F E L h (ExactGrothendieckGroup.continuousTensorSame
        (ExactGrothendieckGroup.continuousRestrict (weilInclusion F E L h) w) x) := by
  have hgen : ∀ (A : {A : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F E) //
        ContinuousPredicate F E A})
      (B : {B : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F L) //
        ContinuousPredicate F L B}),
      ExactGrothendieckGroup.continuousTensorSame
          (ExactGrothendieckGroup.ofRepresentation _ A)
          (induce F E L h (ExactGrothendieckGroup.ofRepresentation _ B)) =
        induce F E L h (ExactGrothendieckGroup.continuousTensorSame
          (ExactGrothendieckGroup.continuousRestrict (weilInclusion F E L h)
            (ExactGrothendieckGroup.ofRepresentation _ A))
          (ExactGrothendieckGroup.ofRepresentation _ B)) := by
    intro A B
    change ExactGrothendieckGroup.continuousTensorSame _
        (ExactGrothendieckGroup.induce _ _ _ _
          (ExactGrothendieckGroup.restrict _ _ _ _
            (ExactGrothendieckGroup.ofRepresentation _ B))) =
      ExactGrothendieckGroup.induce _ _ _ _
        (ExactGrothendieckGroup.restrict _ _ _ _
          (ExactGrothendieckGroup.continuousTensorSame
            (ExactGrothendieckGroup.restrict _ _ _ _
              (ExactGrothendieckGroup.ofRepresentation _ A))
            (ExactGrothendieckGroup.ofRepresentation _ B)))
    rw [ExactGrothendieckGroup.restrict_ofRepresentation,
      ExactGrothendieckGroup.induce_ofRepresentation,
      ExactGrothendieckGroup.restrict_ofRepresentation]
    erw [ExactGrothendieckGroup.continuousTensor_ofRepresentation,
      ExactGrothendieckGroup.continuousTensor_ofRepresentation]
    rw [ExactGrothendieckGroup.restrict_ofRepresentation,
      ExactGrothendieckGroup.induce_ofRepresentation]
    apply ExactGrothendieckGroup.ofRepresentation_eq_of_equiv
    exact (induceTensorEquiv _ _ (fun _ => rfl) A.val _).trans
      (induceEquiv _ (restrictTensorEquiv _ _ A.val B.val))
  have hw : ∀ B : {B : FiniteRepresentation.{0, uF, max uF uV} ℂ (weilSubgroup F L) //
        ContinuousPredicate F L B},
      (ExactGrothendieckGroup.continuousTensorSame.flip
          (induce F E L h (ExactGrothendieckGroup.ofRepresentation _ B)) :
          Virtual.{uF, uV} F E →ₗ[ℤ] Virtual.{uF, uV} F E) =
        (induce F E L h).comp
          ((ExactGrothendieckGroup.continuousTensorSame.flip
              (ExactGrothendieckGroup.ofRepresentation _ B)).comp
            (ExactGrothendieckGroup.continuousRestrict (weilInclusion F E L h))) := by
    intro B
    apply ExactGrothendieckGroup.hom_ext _
    intro c
    induction c using Quotient.inductionOn with
    | h A => exact hgen A B
  have hx : (ExactGrothendieckGroup.continuousTensorSame w).comp (induce F E L h) =
      (induce F E L h).comp (ExactGrothendieckGroup.continuousTensorSame
        (ExactGrothendieckGroup.continuousRestrict (weilInclusion F E L h) w)) := by
    apply ExactGrothendieckGroup.hom_ext _
    intro c
    induction c using Quotient.inductionOn with
    | h B => exact LinearMap.congr_fun (hw B) w
  exact LinearMap.congr_fun hx x

end Langlands.LocalFactor.CommonClosure
