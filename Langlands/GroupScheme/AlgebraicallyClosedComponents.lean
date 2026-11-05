import Langlands.GroupScheme.AlgebraicallyClosedComponentProof
import Langlands.GroupScheme.RationallyRepresentedComponents

/-! # The finite group on all actual components over an algebraically closed field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

variable {k : Type u} [Field k]
  (H : GroupScheme (Spec (CommRingCat.of k)))

/-- All connected components of the actual underlying scheme.
The group structure below requires an algebraically closed field and a smooth
affine group scheme. -/
def AlgebraicallyClosedComponents :=
  _root_.ConnectedComponents H.X.left

variable [IsAlgClosed k] [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- Over an algebraically closed field, forgetting rational representability
is an equivalence onto all actual components. -/
def allComponentEquiv :
    RationallyRepresentedComponents H ≃ AlgebraicallyClosedComponents H :=
  Equiv.ofBijective Subtype.val ⟨Subtype.val_injective, by
    intro c
    obtain ⟨q, hq⟩ := (rationalComponentEmbedding_bijective_of_isAlgClosed H).surjective c
    exact ⟨⟨c, ⟨q, hq⟩⟩, rfl⟩⟩

instance : Group (AlgebraicallyClosedComponents H) :=
  (allComponentEquiv H).symm.group

instance : Finite (AlgebraicallyClosedComponents H) :=
  Finite.of_injective (allComponentEquiv H).symm
    (allComponentEquiv H).symm.injective

/-- The group equivalence from represented components to all components. -/
def allComponentMulEquiv :
    RationallyRepresentedComponents H ≃* AlgebraicallyClosedComponents H :=
  ((allComponentEquiv H).symm.mulEquiv).symm

@[simp]
theorem allComponentMulEquiv_apply (c : RationallyRepresentedComponents H) :
    allComponentMulEquiv H c = c.val :=
  rfl

@[simp]
theorem allComponentMulEquiv_symm_val (c : AlgebraicallyClosedComponents H) :
    ((allComponentMulEquiv H).symm c).val = c :=
  (allComponentMulEquiv H).apply_symm_apply c

/-- The ordinary rational-point quotient is the finite group of all actual
scheme components over an algebraically closed field. -/
def allComponentQuotientEquiv :
    RationalComponentQuotient H ≃* AlgebraicallyClosedComponents H :=
  (representedComponentMulEquiv H).trans (allComponentMulEquiv H)

@[simp]
theorem allComponentQuotientEquiv_apply (c : RationalComponentQuotient H) :
    allComponentQuotientEquiv H c = rationalComponentEmbedding H c :=
  rfl

/-- A rational section maps to its actual scheme component. -/
def allComponentOfPoint :
    rationalPoints H →* AlgebraicallyClosedComponents H :=
  (allComponentMulEquiv H).toMonoidHom.comp (representedComponentOfPoint H)

@[simp]
theorem allComponentOfPoint_apply (x : rationalPoints H) :
    allComponentOfPoint H x = pointComponent H x :=
  rfl

theorem allComponentOfPoint_surjective :
    Function.Surjective (allComponentOfPoint H) :=
  pointComponent_surjective_of_isAlgClosed H

/-- The component-group multiplication is computed by multiplying actual sections. -/
theorem allComponentOfPoint_mul (x y : rationalPoints H) :
    allComponentOfPoint H x * allComponentOfPoint H y = pointComponent H (x * y) :=
  (allComponentOfPoint H).map_mul x y |>.symm

@[simp]
theorem allComponent_one :
    (1 : AlgebraicallyClosedComponents H) = pointComponent H 1 :=
  (allComponentOfPoint H).map_one.symm

theorem allComponentOfPoint_inv (x : rationalPoints H) :
    (allComponentOfPoint H x)⁻¹ = pointComponent H x⁻¹ :=
  (allComponentOfPoint H).map_inv x |>.symm

variable {H}
  {H' H'' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]
  [Smooth H''.X.hom] [IsAffineHom H''.X.hom]

/-- A group-scheme homomorphism induces a homomorphism on all actual components. -/
def allComponentMap (f : H ⟶ H') :
    AlgebraicallyClosedComponents H →* AlgebraicallyClosedComponents H' :=
  (allComponentMulEquiv H').toMonoidHom.comp
    ((representedComponentMap f).comp (allComponentMulEquiv H).symm.toMonoidHom)

@[simp]
theorem allComponentMap_equiv (f : H ⟶ H')
    (c : RationallyRepresentedComponents H) :
    allComponentMap f (allComponentMulEquiv H c) =
      allComponentMulEquiv H' (representedComponentMap f c) := by
  change allComponentMulEquiv H'
      (representedComponentMap f ((allComponentMulEquiv H).symm
        (allComponentMulEquiv H c))) = _
  rw [MulEquiv.symm_apply_apply]

/-- The constructed group homomorphism is the actual continuous map on components. -/
theorem allComponentMap_apply (f : H ⟶ H') (c : AlgebraicallyClosedComponents H) :
    allComponentMap f c = f.hom.hom.left.continuous.connectedComponentsMap c := by
  change (representedComponentMap f ((allComponentMulEquiv H).symm c)).val = _
  rw [representedComponentMap_val, allComponentMulEquiv_symm_val]

@[simp]
theorem allComponentMap_id :
    allComponentMap (𝟙 H) = MonoidHom.id (AlgebraicallyClosedComponents H) := by
  ext c
  obtain ⟨r, rfl⟩ := (allComponentMulEquiv H).surjective c
  change allComponentMap (𝟙 H) (allComponentMulEquiv H r) = allComponentMulEquiv H r
  rw [allComponentMap_equiv, representedComponentMap_id, MonoidHom.id_apply]

@[simp]
theorem allComponentMap_comp (f : H ⟶ H') (g : H' ⟶ H'') :
    allComponentMap (f ≫ g) = (allComponentMap g).comp (allComponentMap f) := by
  ext c
  obtain ⟨r, rfl⟩ := (allComponentMulEquiv H).surjective c
  change allComponentMap (f ≫ g) (allComponentMulEquiv H r) =
    allComponentMap g (allComponentMap f (allComponentMulEquiv H r))
  rw [allComponentMap_equiv, allComponentMap_equiv, allComponentMap_equiv,
    representedComponentMap_comp, MonoidHom.comp_apply]

end Langlands.GroupScheme.IdentityComponent

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [IsAlgClosed L]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- Coefficient conjugation is an automorphism of the group of all actual
components of the base change to an algebraically closed field. -/
def allComponentConjugate (σ : L ≃ₐ[k] L) :
    MulAut (AlgebraicallyClosedComponents (baseChanged k L H)) :=
  ((allComponentMulEquiv (baseChanged k L H)).symm.trans
    (representedComponentConjugate k L H σ)).trans
      (allComponentMulEquiv (baseChanged k L H))

@[simp]
theorem allComponentConjugate_equiv (σ : L ≃ₐ[k] L)
    (c : RationallyRepresentedComponents (baseChanged k L H)) :
    allComponentConjugate k L H σ
        (allComponentMulEquiv (baseChanged k L H) c) =
      allComponentMulEquiv (baseChanged k L H)
        (representedComponentConjugate k L H σ c) := by
  change allComponentMulEquiv _
      (representedComponentConjugate k L H σ
        ((allComponentMulEquiv _).symm (allComponentMulEquiv _ c))) = _
  rw [MulEquiv.symm_apply_apply]

/-- Its underlying function is exactly the actual semilinear scheme-component
permutation, now on the entire component group. -/
theorem allComponentConjugate_apply (σ : L ≃ₐ[k] L)
    (c : AlgebraicallyClosedComponents (baseChanged k L H)) :
    allComponentConjugate k L H σ c = coefficientComponents k L H σ c := by
  change (representedComponentConjugate k L H σ
    ((allComponentMulEquiv _).symm c)).val = _
  rw [representedComponentConjugate_val, allComponentMulEquiv_symm_val]

@[simp]
theorem allComponentConjugate_one :
    allComponentConjugate k L H 1 = 1 := by
  ext c
  obtain ⟨r, rfl⟩ := (allComponentMulEquiv (baseChanged k L H)).surjective c
  simp only [allComponentConjugate_equiv, representedComponentConjugate_one,
    MulAut.one_apply]

theorem allComponentConjugate_mul (σ τ : L ≃ₐ[k] L) :
    allComponentConjugate k L H (σ * τ) =
      allComponentConjugate k L H σ * allComponentConjugate k L H τ := by
  ext c
  obtain ⟨r, rfl⟩ := (allComponentMulEquiv (baseChanged k L H)).surjective c
  simp only [MulAut.mul_apply, allComponentConjugate_equiv,
    representedComponentConjugate_mul]

/-- The coefficient action by group automorphisms of all actual components. -/
def allComponentGaloisAction :
    (L ≃ₐ[k] L) →* MulAut (AlgebraicallyClosedComponents (baseChanged k L H)) where
  toFun := allComponentConjugate k L H
  map_one' := allComponentConjugate_one k L H
  map_mul' := allComponentConjugate_mul k L H

/-- Components fixed by all coefficient automorphisms form a subgroup. -/
def allComponentFixedSubgroup :
    Subgroup (AlgebraicallyClosedComponents (baseChanged k L H)) where
  carrier := {c | ∀ σ : L ≃ₐ[k] L, allComponentConjugate k L H σ c = c}
  one_mem' σ := map_one _
  mul_mem' hc hd σ := by rw [map_mul, hc σ, hd σ]
  inv_mem' hc σ := by rw [map_inv, hc σ]

/-- Membership is fixedness of the actual scheme component. -/
theorem mem_allComponentFixedSubgroup_iff
    (c : AlgebraicallyClosedComponents (baseChanged k L H)) :
    c ∈ allComponentFixedSubgroup k L H ↔
      ∀ σ : L ≃ₐ[k] L, coefficientComponents k L H σ c = c := by
  change (∀ σ : L ≃ₐ[k] L, allComponentConjugate k L H σ c = c) ↔ _
  simp only [allComponentConjugate_apply]
  rfl

/-- Forgetting rational representability identifies the fixed subgroups. -/
def allComponentFixedEquiv :
    representedComponentFixedSubgroup k L H ≃* allComponentFixedSubgroup k L H where
  toFun c := ⟨allComponentMulEquiv _ c, by
    intro σ
    rw [allComponentConjugate_equiv, c.property σ]⟩
  invFun c := ⟨(allComponentMulEquiv _).symm c, by
    intro σ
    apply (allComponentMulEquiv _).injective
    rw [← allComponentConjugate_equiv, MulEquiv.apply_symm_apply]
    exact c.property σ⟩
  left_inv c := by
    apply Subtype.ext
    exact (allComponentMulEquiv (baseChanged k L H)).symm_apply_apply
      (c : RationallyRepresentedComponents (baseChanged k L H))
  right_inv c := by
    apply Subtype.ext
    exact (allComponentMulEquiv (baseChanged k L H)).apply_symm_apply
      (c : AlgebraicallyClosedComponents (baseChanged k L H))
  map_mul' c d := by
    apply Subtype.ext
    exact (allComponentMulEquiv (baseChanged k L H)).map_mul
      (c : RationallyRepresentedComponents (baseChanged k L H))
      (d : RationallyRepresentedComponents (baseChanged k L H))

/-- The ordinary rational quotient's fixed subgroup is the fixed subgroup of
the full actual component group over the algebraically closed extension. -/
def allComponentQuotientFixedEquiv :
    rationalComponentFixedSubgroup k L H ≃* allComponentFixedSubgroup k L H :=
  (representedComponentFixedEquiv k L H).trans (allComponentFixedEquiv k L H)

/-- Rationally represented base-field components inject into the full fixed
component group over the algebraically closed extension. -/
def allComponentBaseChangeToFixed :
    RationallyRepresentedComponents H →* allComponentFixedSubgroup k L H :=
  (allComponentFixedEquiv k L H).toMonoidHom.comp
    (representedComponentBaseChangeToFixed k L H)

theorem allComponentBaseChangeToFixed_injective :
    Function.Injective (allComponentBaseChangeToFixed k L H) :=
  (allComponentFixedEquiv k L H).injective.comp
    (representedComponentBaseChangeToFixed_injective k L H)

theorem allComponentBaseChangeToFixed_apply (c : RationallyRepresentedComponents H) :
    (allComponentBaseChangeToFixed k L H c).val =
      rationalComponentEmbedding (baseChanged k L H)
        (rationalComponentBaseChange H (algebraMap k L)
          ((representedComponentMulEquiv H).symm c)) :=
  representedComponentBaseChangeToFixed_val k L H c

variable {H}
  {H' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]

/-- A homomorphism defined over the base field intertwines the full coefficient
actions on the actual component groups. -/
theorem allComponentConjugate_naturality (f : H ⟶ H') (σ : L ≃ₐ[k] L)
    (c : AlgebraicallyClosedComponents (baseChanged k L H)) :
    allComponentConjugate k L H' σ
        (allComponentMap ((GroupScheme.baseChange (baseMap k L)).map f) c) =
      allComponentMap ((GroupScheme.baseChange (baseMap k L)).map f)
        (allComponentConjugate k L H σ c) := by
  obtain ⟨r, rfl⟩ := (allComponentMulEquiv (baseChanged k L H)).surjective c
  simp only [allComponentMap_equiv, allComponentConjugate_equiv,
    representedComponentConjugate_naturality]

end Langlands.GroupScheme.IdentityComponent
