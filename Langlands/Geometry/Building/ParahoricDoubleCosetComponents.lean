import Langlands.Geometry.Building.IwahoriDoubleCosetComponents
import Langlands.Geometry.Building.IwahoriWeylStatement
import Langlands.Group.TitsSystemParabolicComponents

/-!
# Actual parahoric double cosets from a Tits system in `G(F)^0`

Conditional adapters from a Tits system whose ambient group is `P.zeroSubgroup` and whose
Weyl group is `P.affinePart` to the fixed-data conclusions `P.IwahoriDoubleCosetBijection C`
and `P.ParahoricDoubleCosetBijection F₁ F₂`. The Tits system, the Iwahori containment, the
chamber component surjectivity and the facet-parabolic comparisons remain explicit inputs.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Group.TitsSystem

variable {G : Type*} [Group G] {W : Type*} [Group W] {Γ : Type*} [Group Γ]
  {B N : Subgroup G} {π : N →* W} {q : G →* Γ} {c : W →* Γ}
  {hcompat : ∀ n : N, c (π n) = q (n : G)}

/-- A Tits system in a subgroup equal to `q.ker`, with Weyl group a subgroup equal to `c.ker`
and projection compatible with `π`, is the kernel Tits system of `kernelProjection` with the
same generators. -/
theorem isTitsSystem_kernelProjection_of_eq {K : Subgroup G} (hK : q.ker = K)
    {W₀ : Subgroup W} (hW : c.ker = W₀) {π₀ : N.subgroupOf K →* W₀}
    (hπ₀ : ∀ n : N.subgroupOf K, (π₀ n : W) = π ⟨((n : K) : G), n.property⟩)
    {S₀ : Set W₀} (h : IsTitsSystem (B.subgroupOf K) (N.subgroupOf K) π₀ S₀) :
    IsTitsSystem (B.subgroupOf q.ker) (N.subgroupOf q.ker)
      (kernelProjection (π := π) (q := q) (c := c) (hcompat := hcompat))
      (c.ker.subtype ⁻¹' (W₀.subtype '' S₀)) := by
  subst hK hW
  have hπ : kernelProjection (π := π) (q := q) (c := c) (hcompat := hcompat) = π₀ :=
    MonoidHom.ext fun n => Subtype.ext (hπ₀ n).symm
  rw [hπ, Set.preimage_image_eq _ (Subgroup.subtype_injective _)]
  exact h

end Langlands.Group.TitsSystem

namespace Langlands.Geometry.Building.ParahoricBuildingData

open Langlands.Group Langlands.Group.TitsSystem

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G) [P.normalizerZero.Normal] [P.zeroSubgroup.Normal]

/-- The chamber splitting of KP 7.8.2 supplies the chamber component surjectivity. -/
theorem chamberStabilizer_toComponents_surjective_of_splitting {C : Set P.Apartment}
    (hC : P.IwahoriWeylChamberSplitting C) :
    Function.Surjective (P.toComponents.comp (P.chamberStabilizer C).subtype) := by
  obtain ⟨_, _, _, _, hb⟩ := hC
  exact hb.2

variable (C : Set P.Apartment) (hI : P.parahoric C ≤ P.zeroSubgroup)
  {π₀ : (normalizerPoints P.i).subgroupOf P.zeroSubgroup →* P.affinePart}
  (hπ₀ : ∀ n : (normalizerPoints P.i).subgroupOf P.zeroSubgroup,
    (π₀ n : P.IwahoriWeylGroup) =
      QuotientGroup.mk' P.normalizerZero
        ⟨((n : P.zeroSubgroup) : rationalPoints G), n.property⟩)
  {S : Set P.affinePart}
  (hTits : IsTitsSystem ((P.parahoric C).subgroupOf P.zeroSubgroup)
    ((normalizerPoints P.i).subgroupOf P.zeroSubgroup) π₀ S)
  (hsurj : Function.Surjective (P.toComponents.comp (P.chamberStabilizer C).subtype))

include hπ₀ hTits in
/-- A Tits system in `G(F)^0` with Weyl group `P.affinePart` is the kernel Tits system used by
the component Bruhat construction. -/
theorem isTitsSystem_kernel_of_zeroSubgroup :
    IsTitsSystem
      ((P.parahoric C).subgroupOf (QuotientGroup.mk' P.zeroSubgroup).ker)
      ((normalizerPoints P.i).subgroupOf (QuotientGroup.mk' P.zeroSubgroup).ker)
      (kernelProjection (π := QuotientGroup.mk' P.normalizerZero)
        (q := QuotientGroup.mk' P.zeroSubgroup) (c := P.toComponents)
        (hcompat := fun n => P.toComponents_mk n))
      (P.toComponents.ker.subtype ⁻¹' (P.affinePart.subtype '' S)) :=
  isTitsSystem_kernelProjection_of_eq (QuotientGroup.ker_mk' _)
    P.toComponents_ker_eq_affinePart hπ₀ hTits

omit [P.normalizerZero.Normal] in
include hI in
/-- The Iwahori containment in the kernel form of `G(F)^0`. -/
theorem parahoric_le_ker_mk'_zeroSubgroup :
    P.parahoric C ≤ (QuotientGroup.mk' P.zeroSubgroup).ker := by
  rw [QuotientGroup.ker_mk']
  exact hI

/-- Conditional actual Iwahori Bruhat equivalence from a Tits system in `G(F)^0`. -/
def iwahoriDoubleCosetEquivOfZeroTits :
    P.IwahoriWeylGroup ≃
      DoubleCoset.Quotient (P.parahoric C : Set (rationalPoints G)) (P.parahoric C) :=
  P.iwahoriDoubleCosetEquivOfKernelTits C (P.parahoric_le_ker_mk'_zeroSubgroup C hI)
    (P.isTitsSystem_kernel_of_zeroSubgroup C hπ₀ hTits) hsurj

/-- The conditional equivalence has the required value on every actual normalizer
representative. -/
theorem iwahoriDoubleCosetEquivOfZeroTits_apply (n : normalizerPoints P.i) :
    P.iwahoriDoubleCosetEquivOfZeroTits C hI hπ₀ hTits hsurj (QuotientGroup.mk n) =
      DoubleCoset.mk (P.parahoric C) (P.parahoric C) (n : rationalPoints G) :=
  P.iwahoriDoubleCosetEquivOfKernelTits_apply C _ _ hsurj n

include hI hπ₀ hTits hsurj in
/-- The fixed-data conclusion of KP Theorem 7.8.1(2) from a Tits system in `G(F)^0`. -/
theorem iwahoriDoubleCosetBijection_of_zeroTits : P.IwahoriDoubleCosetBijection C :=
  ⟨P.iwahoriDoubleCosetEquivOfZeroTits C hI hπ₀ hTits hsurj,
    P.iwahoriDoubleCosetEquivOfZeroTits_apply C hI hπ₀ hTits hsurj⟩

variable {F₁ F₂ : Set P.Apartment} {X Y : Set P.affinePart} (hX : X ⊆ S) (hY : Y ⊆ S)
  (hV₁ : P.affineFacetStabilizer F₁ = (Subgroup.closure X).map P.affinePart.subtype)
  (hV₂ : P.affineFacetStabilizer F₂ = (Subgroup.closure Y).map P.affinePart.subtype)

section FullGroup

variable
  (hP₁ : (P.parahoric F₁ : Set (rationalPoints G)) =
    standardParabolic (P.parahoric C) (QuotientGroup.mk' P.normalizerZero)
      (P.affinePart.subtype '' X))
  (hP₂ : (P.parahoric F₂ : Set (rationalPoints G)) =
    standardParabolic (P.parahoric C) (QuotientGroup.mk' P.normalizerZero)
      (P.affinePart.subtype '' Y))

/-- Conditional actual parahoric double-coset equivalence, from a Tits system in `G(F)^0`
and full-group facet-parabolic comparisons. -/
def parahoricDoubleCosetEquivOfZeroTits :
    DoubleCoset.Quotient (P.affineFacetStabilizer F₁ : Set P.IwahoriWeylGroup)
        (P.affineFacetStabilizer F₂) ≃
      DoubleCoset.Quotient (P.parahoric F₁ : Set (rationalPoints G)) (P.parahoric F₂) :=
  subgroupParabolicDoubleCosetEquiv (π := QuotientGroup.mk' P.normalizerZero)
    (K := P.zeroSubgroup) (W₀ := P.affinePart)
    (P.iwahoriDoubleCosetEquivOfZeroTits C hI hπ₀ hTits hsurj)
    (P.iwahoriDoubleCosetEquivOfZeroTits_apply C hI hπ₀ hTits hsurj) hI hπ₀ hTits
    (P.exists_normalizing_zeroSubgroup_rep C hsurj) (QuotientGroup.mk'_surjective _)
    hX hY hV₁ hV₂ hP₁ hP₂

/-- The conditional parahoric equivalence has the required value on every actual normalizer
representative. -/
theorem parahoricDoubleCosetEquivOfZeroTits_apply (n : normalizerPoints P.i) :
    P.parahoricDoubleCosetEquivOfZeroTits C hI hπ₀ hTits hsurj hX hY hV₁ hV₂ hP₁ hP₂
        (DoubleCoset.mk (P.affineFacetStabilizer F₁) (P.affineFacetStabilizer F₂)
          (QuotientGroup.mk n)) =
      DoubleCoset.mk (P.parahoric F₁) (P.parahoric F₂) (n : rationalPoints G) :=
  subgroupParabolicDoubleCosetEquiv_apply (π := QuotientGroup.mk' P.normalizerZero)
    (K := P.zeroSubgroup) (W₀ := P.affinePart)
    (P.iwahoriDoubleCosetEquivOfZeroTits C hI hπ₀ hTits hsurj)
    (P.iwahoriDoubleCosetEquivOfZeroTits_apply C hI hπ₀ hTits hsurj) hI hπ₀ hTits
    (P.exists_normalizing_zeroSubgroup_rep C hsurj) (QuotientGroup.mk'_surjective _)
    hX hY hV₁ hV₂ hP₁ hP₂ n

include hI hπ₀ hTits hsurj hX hY hV₁ hV₂ hP₁ hP₂ in
/-- The fixed-data conclusion of KP Theorem 7.8.1(3) from a Tits system in `G(F)^0` and
full-group facet-parabolic comparisons. -/
theorem parahoricDoubleCosetBijection_of_zeroTits : P.ParahoricDoubleCosetBijection F₁ F₂ :=
  ⟨inferInstance, P.parahoricDoubleCosetEquivOfZeroTits C hI hπ₀ hTits hsurj hX hY hV₁ hV₂ hP₁ hP₂,
    P.parahoricDoubleCosetEquivOfZeroTits_apply C hI hπ₀ hTits hsurj hX hY hV₁ hV₂ hP₁ hP₂⟩

end FullGroup

section Subgroup

variable (hPK₁ : P.parahoric F₁ ≤ P.zeroSubgroup) (hPK₂ : P.parahoric F₂ ≤ P.zeroSubgroup)
  (hP₁ : ((P.parahoric F₁).subgroupOf P.zeroSubgroup : Set P.zeroSubgroup) =
    standardParabolic ((P.parahoric C).subgroupOf P.zeroSubgroup) π₀ X)
  (hP₂ : ((P.parahoric F₂).subgroupOf P.zeroSubgroup : Set P.zeroSubgroup) =
    standardParabolic ((P.parahoric C).subgroupOf P.zeroSubgroup) π₀ Y)

include hI hπ₀ hTits hsurj hPK₁ hP₁ in
/-- A facet-parabolic comparison inside `G(F)^0` gives the full-group comparison. -/
theorem coe_parahoric_eq_standardParabolic_of_zeroSubgroup :
    (P.parahoric F₁ : Set (rationalPoints G)) =
      standardParabolic (P.parahoric C) (QuotientGroup.mk' P.normalizerZero)
        (P.affinePart.subtype '' X) :=
  coe_eq_standardParabolic_of_subgroup (π := QuotientGroup.mk' P.normalizerZero)
    (K := P.zeroSubgroup) (W₀ := P.affinePart)
    (P.iwahoriDoubleCosetEquivOfZeroTits C hI hπ₀ hTits hsurj)
    (P.iwahoriDoubleCosetEquivOfZeroTits_apply C hI hπ₀ hTits hsurj) hI hπ₀ hTits hPK₁ hP₁

include hI hπ₀ hTits hsurj hX hY hV₁ hV₂ hPK₁ hPK₂ hP₁ hP₂ in
/-- The fixed-data conclusion of KP Theorem 7.8.1(3) from a Tits system in `G(F)^0` and
facet-parabolic comparisons inside `G(F)^0`. -/
theorem parahoricDoubleCosetBijection_of_zeroTits_subgroupOf :
    P.ParahoricDoubleCosetBijection F₁ F₂ :=
  P.parahoricDoubleCosetBijection_of_zeroTits C hI hπ₀ hTits hsurj hX hY hV₁ hV₂
    (P.coe_parahoric_eq_standardParabolic_of_zeroSubgroup C hI hπ₀ hTits hsurj hPK₁ hP₁)
    (P.coe_parahoric_eq_standardParabolic_of_zeroSubgroup C hI hπ₀ hTits hsurj hPK₂ hP₂)

end Subgroup

end Langlands.Geometry.Building.ParahoricBuildingData
