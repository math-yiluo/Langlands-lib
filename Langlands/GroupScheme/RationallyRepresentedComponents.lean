import Langlands.GroupScheme.IdentityComponentGaloisComparison
import Mathlib.Algebra.Group.TransferInstance

/-! # The finite group of rationally represented scheme components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

variable {k : Type u} [Field k]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- The actual scheme components containing a rational section. -/
def RationallyRepresentedComponents :=
  Set.range (rationalComponentEmbedding H)

/-- The ordinary rational-component quotient parametrizes precisely this subtype. -/
def representedComponentEquiv :
    RationalComponentQuotient H ≃ RationallyRepresentedComponents H :=
  Equiv.ofInjective (rationalComponentEmbedding H) (rationalComponentEmbedding H).injective

instance : Group (RationallyRepresentedComponents H) :=
  (representedComponentEquiv H).symm.group

instance : Finite (RationallyRepresentedComponents H) :=
  Finite.of_injective (representedComponentEquiv H).symm
    (representedComponentEquiv H).symm.injective

/-- The canonical group comparison with the ordinary quotient. -/
def representedComponentMulEquiv :
    RationalComponentQuotient H ≃* RationallyRepresentedComponents H :=
  ((representedComponentEquiv H).symm.mulEquiv).symm

@[simp]
theorem representedComponentMulEquiv_val (c : RationalComponentQuotient H) :
    (representedComponentMulEquiv H c).val = rationalComponentEmbedding H c :=
  rfl

@[simp]
theorem representedComponentMulEquiv_symm_embedding
    (c : RationallyRepresentedComponents H) :
    rationalComponentEmbedding H ((representedComponentMulEquiv H).symm c) = c.val :=
  congrArg Subtype.val ((representedComponentMulEquiv H).apply_symm_apply c)

/-- A rational section determines a component in the represented-component group. -/
def representedComponentOfPoint :
    rationalPoints H →* RationallyRepresentedComponents H :=
  (representedComponentMulEquiv H).toMonoidHom.comp (rationalComponentProjection H)

@[simp]
theorem representedComponentOfPoint_val
    (x : rationalPoints H) :
    (representedComponentOfPoint H x).val = pointComponent H x :=
  rfl

/-- Multiplication is induced by multiplication of actual rational sections. -/
theorem representedComponentOfPoint_mul_val
    (x y : rationalPoints H) :
    (representedComponentOfPoint H x * representedComponentOfPoint H y).val =
      pointComponent H (x * y) := by
  rw [← map_mul]
  rfl

@[simp]
theorem representedComponent_one_val :
    (1 : RationallyRepresentedComponents H).val = pointComponent H 1 := by
  rw [← map_one (representedComponentOfPoint H)]
  rfl

variable {H}
  {H' H'' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]
  [Smooth H''.X.hom] [IsAffineHom H''.X.hom]

/-- An actual group-scheme homomorphism induces a map of represented components. -/
def representedComponentMap (f : H ⟶ H') :
    RationallyRepresentedComponents H →* RationallyRepresentedComponents H' :=
  (representedComponentMulEquiv H').toMonoidHom.comp
    ((rationalComponentMap f).comp (representedComponentMulEquiv H).symm.toMonoidHom)

@[simp]
theorem representedComponentMap_equiv (f : H ⟶ H')
    (c : RationalComponentQuotient H) :
    representedComponentMap f (representedComponentMulEquiv H c) =
      representedComponentMulEquiv H' (rationalComponentMap f c) := by
  change representedComponentMulEquiv H'
      (rationalComponentMap f ((representedComponentMulEquiv H).symm
        (representedComponentMulEquiv H c))) = _
  rw [MulEquiv.symm_apply_apply]

/-- This map is the restriction of the actual continuous map on scheme components. -/
theorem representedComponentMap_val (f : H ⟶ H')
    (c : RationallyRepresentedComponents H) :
    (representedComponentMap f c).val =
      f.hom.hom.left.continuous.connectedComponentsMap c.val := by
  change rationalComponentEmbedding H'
      (rationalComponentMap f ((representedComponentMulEquiv H).symm c)) = _
  rw [rationalComponentEmbedding_naturality,
    representedComponentMulEquiv_symm_embedding]

@[simp]
theorem representedComponentMap_id :
    representedComponentMap (𝟙 H) = MonoidHom.id (RationallyRepresentedComponents H) := by
  ext c
  obtain ⟨q, rfl⟩ := (representedComponentMulEquiv H).surjective c
  simp

@[simp]
theorem representedComponentMap_comp (f : H ⟶ H') (g : H' ⟶ H'') :
    representedComponentMap (f ≫ g) =
      (representedComponentMap g).comp (representedComponentMap f) := by
  ext c
  obtain ⟨q, rfl⟩ := (representedComponentMulEquiv H).surjective c
  simp

end Langlands.GroupScheme.IdentityComponent

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- Coefficient conjugation as a group automorphism of represented scheme components. -/
def representedComponentConjugate (σ : L ≃ₐ[k] L) :
    MulAut (RationallyRepresentedComponents (baseChanged k L H)) :=
  ((representedComponentMulEquiv (baseChanged k L H)).symm.trans
    (rationalComponentConjugate k L H σ)).trans
      (representedComponentMulEquiv (baseChanged k L H))

@[simp]
theorem representedComponentConjugate_equiv (σ : L ≃ₐ[k] L)
    (c : RationalComponentQuotient (baseChanged k L H)) :
    representedComponentConjugate k L H σ
        (representedComponentMulEquiv (baseChanged k L H) c) =
      representedComponentMulEquiv (baseChanged k L H)
        (rationalComponentConjugate k L H σ c) := by
  change representedComponentMulEquiv _
      (rationalComponentConjugate k L H σ
        ((representedComponentMulEquiv _).symm (representedComponentMulEquiv _ c))) = _
  rw [MulEquiv.symm_apply_apply]

/-- Its underlying component is the published actual scheme-component permutation. -/
theorem representedComponentConjugate_val (σ : L ≃ₐ[k] L)
    (c : RationallyRepresentedComponents (baseChanged k L H)) :
    (representedComponentConjugate k L H σ c).val =
      coefficientComponents k L H σ c.val := by
  change rationalComponentEmbedding _
      (rationalComponentConjugate k L H σ
        ((representedComponentMulEquiv _).symm c)) = _
  rw [rationalComponentEmbedding_conjugate,
    representedComponentMulEquiv_symm_embedding]

@[simp]
theorem representedComponentConjugate_one :
    representedComponentConjugate k L H 1 = 1 := by
  ext c
  obtain ⟨q, rfl⟩ := (representedComponentMulEquiv (baseChanged k L H)).surjective c
  simp

theorem representedComponentConjugate_mul (σ τ : L ≃ₐ[k] L) :
    representedComponentConjugate k L H (σ * τ) =
      representedComponentConjugate k L H σ * representedComponentConjugate k L H τ := by
  ext c
  obtain ⟨q, rfl⟩ := (representedComponentMulEquiv (baseChanged k L H)).surjective c
  simp only [MulAut.mul_apply, representedComponentConjugate_equiv,
    rationalComponentConjugate_mul]

/-- The coefficient action by automorphisms of the finite represented-component group. -/
def representedComponentGaloisAction :
    (L ≃ₐ[k] L) →* MulAut (RationallyRepresentedComponents (baseChanged k L H)) where
  toFun := representedComponentConjugate k L H
  map_one' := representedComponentConjugate_one k L H
  map_mul' := representedComponentConjugate_mul k L H

/-- The subgroup fixed by every coefficient automorphism. -/
def representedComponentFixedSubgroup :
    Subgroup (RationallyRepresentedComponents (baseChanged k L H)) where
  carrier := {c | ∀ σ : L ≃ₐ[k] L, representedComponentConjugate k L H σ c = c}
  one_mem' σ := map_one _
  mul_mem' hc hd σ := by rw [map_mul, hc σ, hd σ]
  inv_mem' hc σ := by rw [map_inv, hc σ]

/-- Fixedness in the group is exactly fixedness of the underlying actual component. -/
theorem mem_representedComponentFixedSubgroup_iff
    (c : RationallyRepresentedComponents (baseChanged k L H)) :
    c ∈ representedComponentFixedSubgroup k L H ↔
      ∀ σ : L ≃ₐ[k] L, coefficientComponents k L H σ c.val = c.val := by
  constructor
  · intro hc σ
    rw [← representedComponentConjugate_val, hc σ]
  · intro hc σ
    apply Subtype.ext
    rw [representedComponentConjugate_val, hc σ]

/-- The quotient comparison identifies the two fixed subgroups as groups. -/
def representedComponentFixedEquiv :
    rationalComponentFixedSubgroup k L H ≃* representedComponentFixedSubgroup k L H where
  toFun c := ⟨representedComponentMulEquiv _ c, by
    intro σ
    rw [representedComponentConjugate_equiv, c.property σ]⟩
  invFun c := ⟨(representedComponentMulEquiv _).symm c, by
    intro σ
    apply (representedComponentMulEquiv _).injective
    rw [← representedComponentConjugate_equiv, MulEquiv.apply_symm_apply]
    exact c.property σ⟩
  left_inv c := by
    apply Subtype.ext
    exact (representedComponentMulEquiv (baseChanged k L H)).symm_apply_apply
      (c : RationalComponentQuotient (baseChanged k L H))
  right_inv c := by
    apply Subtype.ext
    exact (representedComponentMulEquiv (baseChanged k L H)).apply_symm_apply
      (c : RationallyRepresentedComponents (baseChanged k L H))
  map_mul' c d := by
    apply Subtype.ext
    exact (representedComponentMulEquiv (baseChanged k L H)).map_mul
      (c : RationalComponentQuotient (baseChanged k L H))
      (d : RationalComponentQuotient (baseChanged k L H))

/-- Extension of represented base-field components factors through the fixed subgroup. -/
def representedComponentBaseChangeToFixed :
    RationallyRepresentedComponents H →* representedComponentFixedSubgroup k L H :=
  (representedComponentFixedEquiv k L H).toMonoidHom.comp
    ((rationalComponentBaseChangeToFixed k L H).comp
      (representedComponentMulEquiv H).symm.toMonoidHom)

theorem representedComponentBaseChangeToFixed_injective :
    Function.Injective (representedComponentBaseChangeToFixed k L H) :=
  (representedComponentFixedEquiv k L H).injective.comp
    ((rationalComponentBaseChangeToFixed_injective k L H).comp
      (representedComponentMulEquiv H).symm.injective)

@[simp]
theorem representedComponentBaseChangeToFixed_val
    (c : RationallyRepresentedComponents H) :
    (representedComponentBaseChangeToFixed k L H c).val.val =
      rationalComponentEmbedding (baseChanged k L H)
        (rationalComponentBaseChange H (algebraMap k L)
          ((representedComponentMulEquiv H).symm c)) := by
  change (representedComponentMulEquiv (baseChanged k L H)
    (rationalComponentBaseChangeToFixed k L H
      ((representedComponentMulEquiv H).symm c))).val = _
  rw [representedComponentMulEquiv_val, rationalComponentBaseChangeToFixed_val]

variable {H}
  {H' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]

/-- Maps defined over the base field respect the coefficient group actions. -/
theorem representedComponentConjugate_naturality (f : H ⟶ H') (σ : L ≃ₐ[k] L)
    (c : RationallyRepresentedComponents (baseChanged k L H)) :
    representedComponentConjugate k L H' σ
        (representedComponentMap ((GroupScheme.baseChange (baseMap k L)).map f) c) =
      representedComponentMap ((GroupScheme.baseChange (baseMap k L)).map f)
        (representedComponentConjugate k L H σ c) := by
  obtain ⟨q, rfl⟩ := (representedComponentMulEquiv (baseChanged k L H)).surjective c
  simp only [representedComponentMap_equiv, representedComponentConjugate_equiv,
    rationalComponentConjugate_naturality]

end Langlands.GroupScheme.IdentityComponent
