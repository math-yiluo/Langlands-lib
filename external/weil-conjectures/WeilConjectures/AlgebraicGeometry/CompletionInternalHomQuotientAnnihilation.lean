/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-! # Finite-level internal Hom quotient annihilation

Source: Stacks Project, Cohomology of Schemes, Tag 0882, comparison-map construction.
(blueprint: lem-weil-pbc-completion-internal-hom-quotient-annihilation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry


open MonoidalCategory in
private theorem scalar_tensor_eval {C : Type*} [Category C] [MonoidalCategory C]
    [BraidedCategory C] {J G H F : C} (ι : J ⟶ 𝟙_ C) (e : G ⊗ H ⟶ F) :
    G ◁ (ι ▷ H ≫ (λ_ H).hom) ≫ e =
      (α_ G J H).inv ≫ (β_ G J).hom ▷ H ≫ (α_ J G H).hom ≫
        J ◁ e ≫ ι ▷ F ≫ (λ_ F).hom := by
  rw [whisker_exchange_assoc, leftUnitor_naturality]
  rw [← associator_naturality_left_assoc]
  rw [← comp_whiskerRight_assoc, ← BraidedCategory.braiding_naturality_right]
  rw [comp_whiskerRight_assoc, ← associator_inv_naturality_middle_assoc]
  rw [whiskerLeft_comp, Category.assoc]
  congr 1
  rw [← leftUnitor_whiskerRight_assoc,
    ← comp_whiskerRight_assoc, braiding_leftUnitor,
    triangle_assoc_comp_right_assoc]

open MonoidalCategory in
private theorem multiplication_naturality {C : Type*} [Category C] [MonoidalCategory C]
    {J F Q : C} (ι : J ⟶ 𝟙_ C) (f : F ⟶ Q) :
    (ι ▷ F ≫ (λ_ F).hom) ≫ f = J ◁ f ≫ ι ▷ Q ≫ (λ_ Q).hom := by
  rw [Category.assoc, ← leftUnitor_naturality, ← whisker_exchange_assoc]

set_option backward.isDefEq.respectTransparency false in
open MonoidalCategory in
private theorem product_comp_zero_iff {X : Scheme.{u}} {J F Q : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (f : F ⟶ Q) :
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    Scheme.idealModuleProductι ι F ≫ f = 0 ↔
      (ι ▷ F ≫ (λ_ F).hom) ≫ f = 0 := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let a := ι ▷ F ≫ (λ_ F).hom
  change image.ι a ≫ f = 0 ↔ a ≫ f = 0
  rw [← cancel_epi (factorThruImage a)]
  simp only [← Category.assoc, image.fac, comp_zero]

set_option backward.isDefEq.respectTransparency false in
open MonoidalCategory in
private theorem quotient_multiplication_zero {X : Scheme.{u}} {J F : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) :
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    let Q := cokernel (Scheme.idealModuleProductι ι F)
    ι ▷ Q ≫ (λ_ Q).hom = 0 := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let : MonoidalClosed X.Modules := SheafOfModules.monoidalClosed (R := X.sheaf)
  let q := cokernel.π (Scheme.idealModuleProductι ι F)
  have : Epi ((tensorLeft J).map q) := (tensorLeft J).map_epi q
  apply (cancel_epi ((tensorLeft J).map q)).1
  rw [comp_zero]
  change J ◁ q ≫ ι ▷ _ ≫ (λ_ _).hom = 0
  erw [← multiplication_naturality ι q]
  exact (product_comp_zero_iff ι q).mp (cokernel.condition _)

set_option backward.isDefEq.respectTransparency false in
open MonoidalCategory in
private theorem hom_multiplication_zero {X : Scheme.{u}} {J Q : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (G : X.Modules)
    (hz : let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
      ι ▷ Q ≫ (λ_ Q).hom = 0) :
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    let H : X.Modules := SheafOfModules.homObj (R := X.sheaf) G Q
    ι ▷ H ≫ (λ_ H).hom = 0 := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let : SymmetricCategory X.Modules := SheafOfModules.symmetricCategory X.sheaf
  let : MonoidalClosed X.Modules := SheafOfModules.monoidalClosed (R := X.sheaf)
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_eq]
  erw [scalar_tensor_eval ι ((ihom.ev G).app Q)]
  erw [hz]
  simp only [comp_zero, MonoidalClosed.uncurry_eq]
  have hzero : G ◁ (0 : J ⊗ SheafOfModules.homObj (R := X.sheaf) G Q ⟶
      SheafOfModules.homObj (R := X.sheaf) G Q) = 0 :=
    (tensorLeft G).map_zero _ _
  rw [hzero, zero_comp]

/-- Postcomposition with the level-n quotient kills the level-n ideal product
of the internal Hom.

Source: Stacks Project, Cohomology of Schemes, Tag 0882, construction of the
comparison map, and Section 0EHN, equation 0880. The finite-level assertion is
an explicit preliminary argument for that comparison, valid without coherence.
(blueprint: lem-weil-pbc-completion-internal-hom-quotient-annihilation).

Proof: Put J = I^n and Q = F/JF, the cokernel of the product inclusion.
The product JF is the image of multiplication J tensor F → F. Its sections
are locally finite sums of products ax. The cokernel projection kills this
image. Sections of Q locally lift to F, so multiplication by J on Q vanishes
locally and hence vanishes as a sheaf morphism. For a local section a of J
and a local linear map t : G → F, postcomposition sends at to the map
x ↦ a times the class of t(x) in Q. This is zero by the preceding annihilation.
Sections of J Hom(G,F) are locally finite sums of such products. Their images
are therefore locally zero, hence zero. This proves the displayed composite
vanishes. The argument uses local lifts, not surjectivity on all open sections. -/
theorem completion_internal_hom_quotient_annihilation {X : Scheme.{u}}
    (I : X.IdealSheafData) (F G : X.Modules) (n : ℕ) :
    Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι n).2
        (SheafOfModules.homObj (R := X.toRingedSpace.sheaf) G F) ≫
      SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
        (𝟙 G) (formalModuleQuotientπ I n F) = 0 := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let ι := (Scheme.idealSheafPower I.toModulesι n).2
  let q := formalModuleQuotientπ I n F
  have hz := quotient_multiplication_zero (F := F) ι
  have hh := hom_multiplication_zero ι G hz
  apply (product_comp_zero_iff ι _).mpr
  erw [multiplication_naturality ι
    (SheafOfModules.homObjMap (R := X.sheaf) (𝟙 G) q)]
  rw [← Category.assoc]
  change _ ≫ (MonoidalCategoryStruct.whiskerRight ι _ ≫
    (MonoidalCategoryStruct.leftUnitor _).hom) = 0
  erw [hh]
  exact comp_zero

end AlgebraicGeometry
