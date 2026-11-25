/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import WeilConjectures.Algebra.Homology.PoincareDuality.TensorTrilinearUniversal
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-! # Coherence of sheaf scalar extension

Source: Stacks Project, Modules on Sites, Section 03EK, Tags 03CY and 0GMW.
(blueprint: lem-pd-sheaf-scalar-extension-constraint-coherence)

All section formulas explicitly apply the module sheafification unit. Pure tensors
in a monoidal tensor object are transported by `tensorObjIsoSheafification`.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC w

open CategoryTheory MonoidalCategory
open scoped ChangeOfRings

namespace SheafOfModules

attribute [local instance 2000] hasSheafify_coefficientUniverse
  wEqualsLocallyBijective_coefficientUniverse

attribute [local irreducible] tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction
attribute [local irreducible] Localization.Monoidal.tensorBifunctor

/-- Transparent notation for the existing modules on the ringed site.
Source: Stacks Project, Modules on Sites, Tag 03DD.
(blueprint: lem-pd-sheaf-scalar-extension-constraint-coherence) -/
abbrev ScalarExtensionConstraintModules
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{w} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf J CommRingCat.{w}) :=
  ringedSiteModules.{w, w, vC, uC}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)

/-- The image of a local pure tensor in the existing localization tensor.
Source: Stacks Project, Modules on Sites, Tags 03EK and 03CY.
(blueprint: lem-pd-sheaf-scalar-extension-constraint-coherence)
This helper only spells out the module-sheafification unit and its canonical
comparison with the tensor object; it introduces no new tensor construction. -/
noncomputable def scalarExtensionConstraintPureTensor
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{w} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf J CommRingCat.{w})
    (M N : ScalarExtensionConstraintModules.{uC, vC, w} R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) : (M ⊗ N).val.obj U :=
  (tensorObjIsoSheafification.{vC, uC, w} M N).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction.{w}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj
          R).obj)).unit.app
        (M.val ⊗ N.val)).app U (x ⊗ₜ[R.obj.obj U] y))

/-- The image of `s tensor h` in the existing scalar extension sheaf.
Source: Stacks Project, Modules on Sites, Tags 03EK and 03CY.
(blueprint: lem-pd-sheaf-scalar-extension-constraint-coherence)
This only names the module sheafification unit of `changeOfRingsPresheaf`;
it does not choose or reconstruct a module sheaf. -/
noncomputable def scalarExtensionConstraintTmul
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{w} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {A S : Sheaf J CommRingCat.{w}} (α : A ⟶ S)
    (H : ScalarExtensionConstraintModules.{uC, vC, w} A)
    (U : Cᵒᵖ) (h : H.val.obj U) (s : S.obj.obj U) :
    (changeOfRings.{vC, uC, w} α H).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{w}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj
        S).obj)).unit.app
      (changeOfRingsPresheaf.{vC, uC, w} α H)).app U
        (s ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] h))

attribute [local irreducible] changeOfRings changeOfRingsHom
  scalarExtensionConstraintTmul scalarExtensionConstraintPureTensor

/-- The tensor and unit isomorphisms, with their prescribed section formulas and coherences.
This is a package of the conclusions of the theorem, with no chosen comparison data.
Source: Stacks Project, Modules on Sites, Section 03EK, Tags 03CY and 0GMW.
(blueprint: lem-pd-sheaf-scalar-extension-constraint-coherence) -/
structure ScalarExtensionConstraintData
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{w} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (A S : Sheaf J CommRingCat.{w}) (α : A ⟶ S) where
  /-- The tensor comparison is an isomorphism of S-module sheaves. -/
  tensorIso : ∀ H K : ScalarExtensionConstraintModules.{uC, vC, w} A,
    changeOfRings.{vC, uC, w} α (H ⊗ K) ≅ changeOfRings.{vC, uC, w} α H ⊗
        changeOfRings.{vC, uC, w} α K
  /-- The unit comparison is an isomorphism of S-module sheaves. -/
  unitIso : changeOfRings.{vC, uC, w} α (𝟙_ (ScalarExtensionConstraintModules.{uC, vC, w}
      A)) ≅ 𝟙_ (ScalarExtensionConstraintModules.{uC, vC, w} S)
  /-- Insertion of one determines the tensor comparison on local pure tensors. -/
  insertion : ∀ (H K : ScalarExtensionConstraintModules.{uC, vC, w} A) (U : Cᵒᵖ)
      (h : H.val.obj U) (k : K.val.obj U),
    (tensorIso H K).hom.val.app U
        (scalarExtensionConstraintTmul.{uC, vC, w} α (H ⊗ K) U
            (scalarExtensionConstraintPureTensor.{uC, vC, w}
            A H K U h k) 1) =
      scalarExtensionConstraintPureTensor.{uC, vC, w} S (changeOfRings.{vC, uC, w} α H)
          (changeOfRings.{vC, uC, w} α K) U
        (scalarExtensionConstraintTmul.{uC, vC, w} α H U h 1) (scalarExtensionConstraintTmul.{uC,
            vC, w} α K U k 1)
  /-- Uniqueness among all S-linear sheaf maps satisfying the insertion formula. -/
  unique : ∀ (H K : ScalarExtensionConstraintModules.{uC, vC, w} A)
      (d : changeOfRings.{vC, uC, w} α (H ⊗ K) ⟶ changeOfRings.{vC, uC, w} α H
          ⊗ changeOfRings.{vC, uC, w}
        α K),
    (∀ (U : Cᵒᵖ) (h : H.val.obj U) (k : K.val.obj U),
      d.val.app U
          (scalarExtensionConstraintTmul.{uC, vC, w} α (H ⊗ K) U
              (scalarExtensionConstraintPureTensor.{uC, vC,
              w} A H K U h k) 1) =
        scalarExtensionConstraintPureTensor.{uC, vC, w} S (changeOfRings.{vC, uC, w} α H)
            (changeOfRings.{vC, uC, w} α K) U
          (scalarExtensionConstraintTmul.{uC, vC, w} α H U h 1) (scalarExtensionConstraintTmul.{uC,
              vC, w} α K U k 1)) →
      d = (tensorIso H K).hom
  /-- Naturality in the two arbitrary module sheaves. -/
  natural : ∀ (H K H₁ K₁ : ScalarExtensionConstraintModules.{uC, vC, w} A) (f : H ⟶ H₁) (g : K ⟶
      K₁),
    changeOfRingsHom.{vC, uC, w} α (H ⊗ K) (f ⊗ₘ g) ≫ (tensorIso H₁ K₁).hom =
      (tensorIso H K).hom ≫ (changeOfRingsHom.{vC, uC, w} α H f ⊗ₘ changeOfRingsHom.{vC,
          uC, w} α K g)
  /-- The unit comparison is scalar multiplication. -/
  unit_hom : ∀ (U : Cᵒᵖ) (s : S.obj.obj U) (a : A.obj.obj U),
    unitIso.hom.val.app U
        (scalarExtensionConstraintTmul.{uC, vC, w} α (𝟙_ (ScalarExtensionConstraintModules.{uC, vC,
            w} A)) U a
            s) =
      s * α.hom.app U a
  /-- The inverse unit comparison inserts one. -/
  unit_inv : ∀ (U : Cᵒᵖ) (s : S.obj.obj U),
    unitIso.inv.val.app U s =
      scalarExtensionConstraintTmul.{uC, vC, w} α (𝟙_ (ScalarExtensionConstraintModules.{uC, vC, w}
          A)) U (1 :
          A.obj.obj U) s
  /-- The forward comparison distributes the first scalar into the first factor. -/
  tensor_hom : ∀ (H K : ScalarExtensionConstraintModules.{uC, vC, w} A) (U : Cᵒᵖ)
      (h : H.val.obj U) (k : K.val.obj U) (s : S.obj.obj U),
    (tensorIso H K).hom.val.app U
        (scalarExtensionConstraintTmul.{uC, vC, w} α (H ⊗ K) U
            (scalarExtensionConstraintPureTensor.{uC, vC, w}
            A H K U h k) s) =
      scalarExtensionConstraintPureTensor.{uC, vC, w} S (changeOfRings.{vC, uC, w} α H)
          (changeOfRings.{vC, uC, w} α K) U
        (scalarExtensionConstraintTmul.{uC, vC, w} α H U h s) (scalarExtensionConstraintTmul.{uC,
            vC, w} α K U k 1)
  /-- The inverse tensor comparison multiplies the two scalar factors. -/
  tensor_inv : ∀ (H K : ScalarExtensionConstraintModules.{uC, vC, w} A) (U : Cᵒᵖ)
      (h : H.val.obj U) (k : K.val.obj U) (s t : S.obj.obj U),
    (tensorIso H K).inv.val.app U
        (scalarExtensionConstraintPureTensor.{uC, vC, w} S (changeOfRings.{vC, uC, w} α
            H) (changeOfRings.{vC, uC, w} α K) U
          (scalarExtensionConstraintTmul.{uC, vC, w} α H U h s) (scalarExtensionConstraintTmul.{uC,
              vC, w} α K U k t)) =
      scalarExtensionConstraintTmul.{uC, vC, w} α (H ⊗ K) U
          (scalarExtensionConstraintPureTensor.{uC, vC, w} A
          H K U h k) (s * t)
  /-- Oplax associativity with the canonical associators. -/
  oplax_associativity : ∀ H K L : ScalarExtensionConstraintModules.{uC, vC, w} A,
    changeOfRingsHom.{vC, uC, w} α ((H ⊗ K) ⊗ L) (α_ H K L).hom ≫
        (tensorIso H (K ⊗ L)).hom ≫ (changeOfRings.{vC, uC, w} α H ◁ (tensorIso K L).hom)
            =
      (tensorIso (H ⊗ K) L).hom ≫ ((tensorIso H K).hom ▷ changeOfRings.{vC, uC, w} α L) ≫
        (α_ (changeOfRings.{vC, uC, w} α H) (changeOfRings.{vC, uC, w} α K)
            (changeOfRings.{vC, uC, w} α
        L)).hom
  /-- Oplax left unit with the canonical unitor. -/
  oplax_left_unit : ∀ H : ScalarExtensionConstraintModules.{uC, vC, w} A,
    (tensorIso (𝟙_ (ScalarExtensionConstraintModules.{uC, vC, w} A)) H).hom ≫
        (unitIso.hom ▷ changeOfRings.{vC, uC, w} α H) ≫ (λ_ (changeOfRings.{vC, uC, w} α H)).hom =
      changeOfRingsHom.{vC, uC, w} α ((𝟙_ (ScalarExtensionConstraintModules.{uC, vC, w}
          A)) ⊗ H) (λ_ H).hom
  /-- Oplax right unit with the canonical unitor. -/
  oplax_right_unit : ∀ H : ScalarExtensionConstraintModules.{uC, vC, w} A,
    (tensorIso H (𝟙_ (ScalarExtensionConstraintModules.{uC, vC, w} A))).hom ≫
        (changeOfRings.{vC, uC, w} α H ◁ unitIso.hom) ≫ (ρ_ (changeOfRings.{vC, uC, w} α H)).hom =
      changeOfRingsHom.{vC, uC, w} α (H ⊗ (𝟙_ (ScalarExtensionConstraintModules.{uC, vC,
          w} A))) (ρ_ H).hom
  /-- Lax associativity for the inverse constraints. -/
  lax_associativity : ∀ H K L : ScalarExtensionConstraintModules.{uC, vC, w} A,
    ((tensorIso H K).inv ▷ changeOfRings.{vC, uC, w} α L) ≫ (tensorIso (H ⊗ K) L).inv ≫
        changeOfRingsHom.{vC, uC, w} α ((H ⊗ K) ⊗ L) (α_ H K L).hom =
      (α_ (changeOfRings.{vC, uC, w} α H) (changeOfRings.{vC, uC, w} α K)
          (changeOfRings.{vC, uC, w} α
        L)).hom ≫
        (changeOfRings.{vC, uC, w} α H ◁ (tensorIso K L).inv) ≫ (tensorIso H (K ⊗ L)).inv
  /-- Lax left unit for the inverse constraints. -/
  lax_left_unit : ∀ H : ScalarExtensionConstraintModules.{uC, vC, w} A,
    (unitIso.inv ▷ changeOfRings.{vC, uC, w} α H) ≫ (tensorIso (𝟙_
        (ScalarExtensionConstraintModules.{uC, vC, w} A)) H).inv ≫
        changeOfRingsHom.{vC, uC, w} α ((𝟙_ (ScalarExtensionConstraintModules.{uC, vC, w}
            A)) ⊗ H) (λ_ H).hom =
      (λ_ (changeOfRings.{vC, uC, w} α H)).hom
  /-- Lax right unit for the inverse constraints. -/
  lax_right_unit : ∀ H : ScalarExtensionConstraintModules.{uC, vC, w} A,
    (changeOfRings.{vC, uC, w} α H ◁ unitIso.inv) ≫ (tensorIso H (𝟙_
        (ScalarExtensionConstraintModules.{uC, vC, w} A))).inv ≫
        changeOfRingsHom.{vC, uC, w} α (H ⊗ (𝟙_ (ScalarExtensionConstraintModules.{uC,
            vC, w} A))) (ρ_ H).hom =
      (ρ_ (changeOfRings.{vC, uC, w} α H)).hom

section Construction

set_option backward.defeqAttrib.useBackward true

attribute [local semireducible] changeOfRings changeOfRingsHom
  scalarExtensionConstraintTmul

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

private abbrev SR (R : Sheaf J CommRingCat.{w}) :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R

private noncomputable abbrev SF (R : Sheaf J CommRingCat.{w}) :=
  PresheafOfModules.sheafification.{w} (𝟙 (SR (J := J) R).obj)

private noncomputable def SA (R : Sheaf J CommRingCat.{w}) :
    SF (J := J) R ⊣ forget (SR (J := J) R) :=
  PresheafOfModules.sheafificationAdjunction.{w} (𝟙 (SR (J := J) R).obj)

attribute [local irreducible] monoidalCategory

private noncomputable def tensorUnitMap (R : Sheaf J CommRingCat.{w})
    (M N : ScalarExtensionConstraintModules (J := J) R) : M.val ⊗ N.val ⟶ (M ⊗ N).val :=
  (SA (J := J) R).unit.app (M.val ⊗ N.val) ≫ (tensorObjIsoSheafification M N).inv.val

private theorem tensorUnitMap_apply (R : Sheaf J CommRingCat.{w})
    (M N : ScalarExtensionConstraintModules (J := J) R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (tensorUnitMap (J := J) R M N).app U (x ⊗ₜ[R.obj.obj U] y) =
      scalarExtensionConstraintPureTensor (J := J) R M N U x y := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) R) :=
    cochainModulesMonoidal (J := J) R
  unfold scalarExtensionConstraintPureTensor tensorUnitMap
  rfl

private theorem tensor_ext (R : Sheaf J CommRingCat.{w})
    (M N P : ScalarExtensionConstraintModules (J := J) R) (f g : M ⊗ N ⟶ P)
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      f.val.app U (scalarExtensionConstraintPureTensor (J := J) R M N U x y) =
        g.val.app U (scalarExtensionConstraintPureTensor (J := J) R M N U x y)) : f = g := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) R) :=
    cochainModulesMonoidal (J := J) R
  unfold scalarExtensionConstraintPureTensor at h
  apply (cancel_epi (tensorObjIsoSheafification M N).inv).mp
  apply ((SA (J := J) R).homEquiv (M.val ⊗ N.val) P).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  ext t
  change f.val.app U ((tensorObjIsoSheafification M N).inv.val.app U
      (((SA (J := J) R).unit.app (M.val ⊗ N.val)).app U t)) =
    g.val.app U ((tensorObjIsoSheafification M N).inv.val.app U
      (((SA (J := J) R).unit.app (M.val ⊗ N.val)).app U t))
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact h U x y
  | add x y hx hy => simp only [map_add, hx, hy]

private noncomputable abbrev FG (R : Sheaf J CommRingCat.{w}) :=
  forget (SR (J := J) R)

private noncomputable instance fgLax (R : Sheaf J CommRingCat.{w}) :
    (FG (J := J) R).LaxMonoidal := (SA (J := J) R).rightAdjointLaxMonoidal

private theorem tensorUnitMap_eq_mu (R : Sheaf J CommRingCat.{w})
    (M N : ScalarExtensionConstraintModules (J := J) R) :
    tensorUnitMap (J := J) R M N = Functor.LaxMonoidal.μ (FG (J := J) R) M N := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) R) :=
    cochainModulesMonoidal (J := J) R
  simp only [tensorUnitMap, tensorObjIsoSheafification, Iso.trans_inv,
    Iso.symm_inv, tensorIso_hom, Iso.app_hom, asIso_hom,
    Functor.Monoidal.μIso_inv, Functor.LaxMonoidal.μ, Adjunction.homEquiv_unit]
  rfl

private theorem pure_natural (R : Sheaf J CommRingCat.{w})
    {M M' N N' : ScalarExtensionConstraintModules (J := J) R} (f : M ⟶ M') (g : N ⟶ N')
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (f ⊗ₘ g).val.app U (scalarExtensionConstraintPureTensor (J := J) R M N U x y) =
      scalarExtensionConstraintPureTensor (J := J) R M' N' U (f.val.app U x) (g.val.app U y) := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) R) :=
    cochainModulesMonoidal (J := J) R
  have h := Functor.LaxMonoidal.μ_natural (FG (J := J) R) f g
  simp only [← tensorUnitMap_eq_mu] at h
  have hh := congrArg (fun t ↦ t.app U (x ⊗ₜ[R.obj.obj U] y)) h
  change (tensorUnitMap (J := J) R M' N').app U
      (f.val.app U x ⊗ₜ[R.obj.obj U] g.val.app U y) =
    (f ⊗ₘ g).val.app U ((tensorUnitMap (J := J) R M N).app U
      (x ⊗ₜ[R.obj.obj U] y)) at hh
  simpa only [tensorUnitMap_apply] using hh.symm

private theorem pure_assoc (R : Sheaf J CommRingCat.{w})
    (M N P : ScalarExtensionConstraintModules (J := J) R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) (z : P.val.obj U) :
    (α_ M N P).hom.val.app U
        (scalarExtensionConstraintPureTensor (J := J) R (M ⊗ N) P U
          (scalarExtensionConstraintPureTensor (J := J) R M N U x y) z) =
      scalarExtensionConstraintPureTensor (J := J) R M (N ⊗ P) U x
        (scalarExtensionConstraintPureTensor (J := J) R N P U y z) := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) R) :=
    cochainModulesMonoidal (J := J) R
  have h := Functor.LaxMonoidal.associativity (FG (J := J) R) M N P
  simp only [← tensorUnitMap_eq_mu] at h
  have hh := congrArg (fun t ↦ t.app U ((x ⊗ₜ[R.obj.obj U] y) ⊗ₜ[R.obj.obj U] z)) h
  change (α_ M N P).hom.val.app U
      ((tensorUnitMap (J := J) R (M ⊗ N) P).app U
        ((tensorUnitMap (J := J) R M N).app U (x ⊗ₜ[R.obj.obj U] y) ⊗ₜ[R.obj.obj U] z)) =
    (tensorUnitMap (J := J) R M (N ⊗ P)).app U
      (x ⊗ₜ[R.obj.obj U] (tensorUnitMap (J := J) R N P).app U (y ⊗ₜ[R.obj.obj U] z)) at hh
  simpa only [tensorUnitMap_apply] using hh

private theorem extension_ext {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S)
    (M : ScalarExtensionConstraintModules (J := J) A) (P : ScalarExtensionConstraintModules
      (J := J) S)
    (f g : changeOfRings (J := J) a M ⟶ P)
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U),
      f.val.app U (scalarExtensionConstraintTmul (J := J) a M U x 1) =
        g.val.app U (scalarExtensionConstraintTmul (J := J) a M U x 1)) : f = g := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) A) :=
    cochainModulesMonoidal (J := J) A
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) S) :=
    cochainModulesMonoidal (J := J) S
  unfold changeOfRings at f g
  unfold scalarExtensionConstraintTmul at h
  apply ((SA (J := J) S).homEquiv (changeOfRingsPresheaf (J := J) a M) P).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact h U x

private theorem pure_restrict (R : Sheaf J CommRingCat.{w})
    (M N : ScalarExtensionConstraintModules (J := J) R) {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : M.val.obj U) (y : N.val.obj U) :
    (M ⊗ N).val.map i (scalarExtensionConstraintPureTensor (J := J) R M N U x y) =
      scalarExtensionConstraintPureTensor (J := J) R M N V (M.val.map i x) (N.val.map i y) := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) R) :=
    cochainModulesMonoidal (J := J) R
  have h := (PresheafOfModules.naturality_apply (tensorUnitMap (J := J) R M N) i
    (x ⊗ₜ[R.obj.obj U] y)).symm
  change (M ⊗ N).val.map i ((tensorUnitMap (J := J) R M N).app U
      (x ⊗ₜ[R.obj.obj U] y)) =
    (tensorUnitMap (J := J) R M N).app V (M.val.map i x ⊗ₜ[R.obj.obj V] N.val.map i y) at h
  simpa only [tensorUnitMap_apply] using h

attribute [local semireducible] monoidalCategory

private theorem fg_epsilon (R : Sheaf J CommRingCat.{w}) :
    Functor.LaxMonoidal.ε (FG (J := J) R) = 𝟙 (𝟙_ (PresheafOfModules.{w} (SR (J := J) R).obj)) := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) R) :=
    cochainModulesMonoidal (J := J) R
  change (SA (J := J) R).unit.app _ ≫ (FG (J := J) R).map ((SA (J := J) R).counit.app (unit (SR
    (J := J) R))) = _
  exact (SA (J := J) R).right_triangle_components (unit (SR (J := J) R))

private theorem pure_left_unit (R : Sheaf J CommRingCat.{w})
    (M : ScalarExtensionConstraintModules (J := J) R) (U : Cᵒᵖ)
    (a : R.obj.obj U) (x : M.val.obj U) :
    (λ_ M).hom.val.app U
        (scalarExtensionConstraintPureTensor (J := J) R (𝟙_ (ScalarExtensionConstraintModules
          (J := J) R))
          M U a x) = a • x := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) R) :=
    cochainModulesMonoidal (J := J) R
  have h := Functor.LaxMonoidal.left_unitality (FG (J := J) R) M
  rw [fg_epsilon, id_whiskerRight, Category.id_comp] at h
  rw [← tensorUnitMap_eq_mu] at h
  have hh := (congrArg (fun t ↦ t.app U (a ⊗ₜ[R.obj.obj U] x)) h).symm
  change (λ_ M).hom.val.app U
    ((tensorUnitMap (J := J) R (𝟙_ (ScalarExtensionConstraintModules (J := J) R)) M).app U
      (a ⊗ₜ[R.obj.obj U] x)) = a • x at hh
  simpa only [tensorUnitMap_apply] using hh

private theorem pure_right_unit (R : Sheaf J CommRingCat.{w})
    (M : ScalarExtensionConstraintModules (J := J) R) (U : Cᵒᵖ)
    (x : M.val.obj U) (a : R.obj.obj U) :
    (ρ_ M).hom.val.app U
        (scalarExtensionConstraintPureTensor (J := J) R M
          (𝟙_ (ScalarExtensionConstraintModules (J := J) R)) U x a) = a • x := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) R) :=
    cochainModulesMonoidal (J := J) R
  have h := Functor.LaxMonoidal.right_unitality (FG (J := J) R) M
  rw [fg_epsilon, MonoidalCategory.whiskerLeft_id, Category.id_comp] at h
  rw [← tensorUnitMap_eq_mu] at h
  have hh := (congrArg (fun t ↦ t.app U (x ⊗ₜ[R.obj.obj U] a)) h).symm
  change (ρ_ M).hom.val.app U
    ((tensorUnitMap (J := J) R M (𝟙_ (ScalarExtensionConstraintModules (J := J) R))).app U
      (x ⊗ₜ[R.obj.obj U] a)) = a • x at hh
  simpa only [tensorUnitMap_apply] using hh

attribute [local irreducible] monoidalCategory

private theorem tmul_natural {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S)
    (M : ScalarExtensionConstraintModules (J := J) A) {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : M.val.obj U) (s : S.obj.obj U) :
    (changeOfRings (J := J) a M).val.map i (scalarExtensionConstraintTmul (J := J) a M U x s) =
      scalarExtensionConstraintTmul (J := J) a M V (M.val.map i x) (S.obj.map i s) := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) A) :=
    cochainModulesMonoidal (J := J) A
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) S) :=
    cochainModulesMonoidal (J := J) S
  have h := PresheafOfModules.naturality_apply
    ((SA (J := J) S).unit.app (changeOfRingsPresheaf (J := J) a M)) i
    (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x)
  change (((SA (J := J) S).unit.app (changeOfRingsPresheaf (J := J) a M)).app V)
      ((changeOfRingsPresheaf (J := J) a M).map i
        (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x)) =
    (changeOfRings (J := J) a M).val.map i
      ((((SA (J := J) S).unit.app (changeOfRingsPresheaf (J := J) a M)).app U)
        (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x)) at h
  rw [show (changeOfRingsPresheaf (J := J) a M).map i
      (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x) =
      S.obj.map i s ⊗ₜ[A.obj.obj V, (a.hom.app V).hom] M.val.restrictₛₗ i x from
    Classical.choose_spec (exists_changeOfRingsMap (J := J) a M i) s x] at h
  unfold scalarExtensionConstraintTmul
  exact h.symm

private noncomputable def insertMap {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S)
    (M : ScalarExtensionConstraintModules (J := J) A) :
    M ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj
      (changeOfRings (J := J) a M) := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) A) :=
    cochainModulesMonoidal (J := J) A
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) S) :=
    cochainModulesMonoidal (J := J) S
  exact
    { val :=
        { app := fun U ↦
            ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
              (a.hom.app U).hom (((SA (J := J) S).unit.app (changeOfRingsPresheaf (J := J) a
                M)).app U)
          naturality := by
            intro U V i
            ext x
            change scalarExtensionConstraintTmul (J := J) a M V (M.val.map i x) 1 =
              (changeOfRings (J := J) a M).val.map i (scalarExtensionConstraintTmul (J := J) a M U
                x 1)
            rw [tmul_natural, map_one] } }

private theorem extensionTensor_ext {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S)
    (M N : ScalarExtensionConstraintModules (J := J) A) (P : ScalarExtensionConstraintModules
      (J := J) S)
    (f g : changeOfRings (J := J) a (M ⊗ N) ⟶ P)
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      f.val.app U (scalarExtensionConstraintTmul (J := J) a (M ⊗ N) U
        (scalarExtensionConstraintPureTensor (J := J) A M N U x y) 1) =
      g.val.app U (scalarExtensionConstraintTmul (J := J) a (M ⊗ N) U
        (scalarExtensionConstraintPureTensor (J := J) A M N U x y) 1)) : f = g := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) A) :=
    cochainModulesMonoidal (J := J) A
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) S) :=
    cochainModulesMonoidal (J := J) S
  let F := restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)
  have he : insertMap (J := J) a (M ⊗ N) ≫ F.map f = insertMap (J := J) a (M ⊗ N) ≫ F.map g := by
    apply tensor_ext (J := J) A M N (F.obj P)
    intro U x y
    exact h U x y
  apply extension_ext (J := J) a (M ⊗ N) P f g
  intro U x
  exact congrArg (fun t ↦ t.val.app U x) he

private theorem extension_map_tmul {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S)
    {M N : ScalarExtensionConstraintModules (J := J) A} (f : M ⟶ N) (U : Cᵒᵖ)
    (x : M.val.obj U) (s : S.obj.obj U) :
    (changeOfRingsHom (J := J) a M f).val.app U (scalarExtensionConstraintTmul (J := J) a M U x s) =
      scalarExtensionConstraintTmul (J := J) a N U (f.val.app U x) s := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) A) :=
    cochainModulesMonoidal (J := J) A
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) S) :=
    cochainModulesMonoidal (J := J) S
  let c : changeOfRingsPresheaf (J := J) a M ⟶ changeOfRingsPresheaf (J := J) a N :=
    { app := fun V ↦ (ModuleCat.extendScalars (a.hom.app V).hom).map (f.val.app V)
      naturality := changeOfRingsHom_naturality a M f }
  have h := (SA (J := J) S).unit.naturality c
  have hh := congrArg (fun k ↦ k.app U
    (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x)) h
  change (((SA (J := J) S).unit.app (changeOfRingsPresheaf (J := J) a N)).app U
      ((ModuleCat.extendScalars (a.hom.app U).hom).map (f.val.app U)
        (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x))) =
    (changeOfRingsHom (J := J) a M f).val.app U
      (scalarExtensionConstraintTmul (J := J) a M U x s) at hh
  erw [ModuleCat.ExtendScalars.map_tmul] at hh
  exact hh.symm

private noncomputable def extensionPresheafIso {A S : Sheaf J CommRingCat.{w}}
    (a : A ⟶ S) (M : ScalarExtensionConstraintModules (J := J) A) :
    changeOfRingsPresheaf a M ≅ changeOfRingsPresheafOfUniverses a M :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro U V i
    apply ModuleCat.hom_ext
    ext t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s x =>
      change changeOfRingsMap a M i (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x) =
        changeOfRingsMapOfUniverses a M i (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x)
      exact (Classical.choose_spec (exists_changeOfRingsMap a M i) s x).trans
        (changeOfRingsMap_tmulOfUniverses a M i s x).symm)

private noncomputable def extensionIso {A S : Sheaf J CommRingCat.{w}}
    (a : A ⟶ S) (M : ScalarExtensionConstraintModules (J := J) A) :
    changeOfRings a M ≅ changeOfRingsOfUniverses a M :=
  (SF (J := J) S).mapIso (extensionPresheafIso (J := J) a M)

private theorem extensionIso_tmul {A S : Sheaf J CommRingCat.{w}}
    (a : A ⟶ S) (M : ScalarExtensionConstraintModules (J := J) A)
    (U : Cᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U) :
    (extensionIso (J := J) a M).hom.val.app U
      (scalarExtensionConstraintTmul (J := J) a M U x s) =
      scalarExtensionSection a M U s x := by
  have h := (SA (J := J) S).unit.naturality (extensionPresheafIso (J := J) a M).hom
  have hh := congrArg (fun f ↦ f.app U (s ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x)) h
  exact hh.symm

private theorem extensionIso_inv_tmul {A S : Sheaf J CommRingCat.{w}}
    (a : A ⟶ S) (M : ScalarExtensionConstraintModules (J := J) A)
    (U : Cᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U) :
    (extensionIso (J := J) a M).inv.val.app U (scalarExtensionSection a M U s x) =
      scalarExtensionConstraintTmul (J := J) a M U x s := by
  rw [← extensionIso_tmul (J := J) a M U x s]
  exact congrArg (fun f ↦ f.val.app U (scalarExtensionConstraintTmul (J := J) a M U x s))
    (extensionIso (J := J) a M).hom_inv_id

private noncomputable def tensorIsoSite (A : Sheaf J CommRingCat.{w})
    (M N : ScalarExtensionConstraintModules (J := J) A) :
    M ⊗ N ≅ (siteSheafTensorRight N).obj M :=
  tensorObjIsoSheafification M N ≪≫
    (SF (J := J) A).mapIso ((siteTensorRightIso A N.val).app M.val).symm

private theorem tensorIsoSite_pure (A : Sheaf J CommRingCat.{w})
    (M N : ScalarExtensionConstraintModules (J := J) A) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (tensorIsoSite (J := J) A M N).hom.val.app U
      (scalarExtensionConstraintPureTensor (J := J) A M N U x y) =
      siteSheafTensorTmul M N U x y := by
  let q := ((siteTensorRightIso A N.val).app M.val).inv
  have hn := (SA (J := J) A).unit.naturality q
  have hh := congrArg (fun f ↦ f.app U (x ⊗ₜ[A.obj.obj U] y)) hn
  unfold scalarExtensionConstraintPureTensor tensorIsoSite
  dsimp only [Iso.trans_hom]
  change ((SF (J := J) A).map q).val.app U
    ((tensorObjIsoSheafification M N).hom.val.app U
      ((tensorObjIsoSheafification M N).inv.val.app U
        (((SA (J := J) A).unit.app (M.val ⊗ N.val)).app U
          (x ⊗ₜ[A.obj.obj U] y)))) = _
  have hi := congrArg (fun f ↦ f.val.app U
    (((SA (J := J) A).unit.app (M.val ⊗ N.val)).app U (x ⊗ₜ[A.obj.obj U] y)))
    (tensorObjIsoSheafification M N).inv_hom_id
  change (tensorObjIsoSheafification M N).hom.val.app U
    ((tensorObjIsoSheafification M N).inv.val.app U _) = _ at hi
  rw [hi]
  exact hh.symm

private theorem tensorIsoSite_inv_pure (A : Sheaf J CommRingCat.{w})
    (M N : ScalarExtensionConstraintModules (J := J) A) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (tensorIsoSite (J := J) A M N).inv.val.app U (siteSheafTensorTmul M N U x y) =
      scalarExtensionConstraintPureTensor (J := J) A M N U x y := by
  rw [← tensorIsoSite_pure (J := J) A M N U x y]
  exact congrArg (fun f ↦ f.val.app U
    (scalarExtensionConstraintPureTensor (J := J) A M N U x y))
    (tensorIsoSite (J := J) A M N).hom_inv_id

private noncomputable def extensionFunctor {A S : Sheaf J CommRingCat.{w}}
    (a : A ⟶ S) : ScalarExtensionConstraintModules (J := J) A ⥤
      ScalarExtensionConstraintModules (J := J) S where
  obj M := changeOfRingsOfUniverses a M
  map f := changeOfRingsHomOfUniverses a _ f
  map_id M := scalarExtension_map_id a M
  map_comp f g := scalarExtension_map_comp a f g

private noncomputable def comparisonIso {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S)
    (M N : ScalarExtensionConstraintModules (J := J) A) :
    changeOfRings a (M ⊗ N) ≅ changeOfRings a M ⊗ changeOfRings a N :=
  extensionIso (J := J) a _ ≪≫
    (extensionFunctor (J := J) a).mapIso (tensorIsoSite (J := J) A M N) ≪≫
      scalarTensorBinaryIso a M N ≪≫
        (tensorIsoSite (J := J) S _ _).symm ≪≫
          ((extensionIso (J := J) a M).symm ⊗ᵢ (extensionIso (J := J) a N).symm)

private noncomputable abbrev forwardMap {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S)
    (M N : ScalarExtensionConstraintModules (J := J) A) :=
  (comparisonIso (J := J) a M N).hom

private noncomputable abbrev backwardMap {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S)
    (M N : ScalarExtensionConstraintModules (J := J) A) :=
  (comparisonIso (J := J) a M N).inv

private theorem forwardMap_tmul {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S)
    (M N : ScalarExtensionConstraintModules (J := J) A) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) (s : S.obj.obj U) :
    (forwardMap (J := J) a M N).val.app U
      (scalarExtensionConstraintTmul (J := J) a (M ⊗ N) U
        (scalarExtensionConstraintPureTensor (J := J) A M N U x y) s) =
      scalarExtensionConstraintPureTensor (J := J) S (changeOfRings a M) (changeOfRings a N) U
        (scalarExtensionConstraintTmul (J := J) a M U x s)
        (scalarExtensionConstraintTmul (J := J) a N U y 1) := by
  change (((extensionIso (J := J) a M).inv ⊗ₘ (extensionIso (J := J) a N).inv).val.app U)
    ((tensorIsoSite (J := J) S _ _).inv.val.app U
      ((scalarTensorBinaryForward a M N).val.app U
        ((changeOfRingsHomOfUniverses a _ (tensorIsoSite (J := J) A M N).hom).val.app U
          ((extensionIso (J := J) a _).hom.val.app U _)))) = _
  rw [extensionIso_tmul, scalarExtension_map_tmul, tensorIsoSite_pure,
    scalarTensorBinaryForward_tmul, tensorIsoSite_inv_pure, pure_natural,
    extensionIso_inv_tmul, extensionIso_inv_tmul]

private theorem backwardMap_tmul {A S : Sheaf J CommRingCat.{w}}
    (a : A ⟶ S) (M N : ScalarExtensionConstraintModules (J := J) A) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) (s t : S.obj.obj U) :
    (backwardMap (J := J) a M N).val.app U
      (scalarExtensionConstraintPureTensor (J := J) S (changeOfRings a M) (changeOfRings a N) U
        (scalarExtensionConstraintTmul (J := J) a M U x s)
        (scalarExtensionConstraintTmul (J := J) a N U y t)) =
      scalarExtensionConstraintTmul (J := J) a (M ⊗ N) U
        (scalarExtensionConstraintPureTensor (J := J) A M N U x y) (s * t) := by
  change (extensionIso (J := J) a _).inv.val.app U
    ((changeOfRingsHomOfUniverses a _ (tensorIsoSite (J := J) A M N).inv).val.app U
      ((scalarTensorBinaryInverse a M N).val.app U
        ((tensorIsoSite (J := J) S _ _).hom.val.app U
          (((extensionIso (J := J) a M).hom ⊗ₘ (extensionIso (J := J) a N).hom).val.app U _)))) = _
  rw [pure_natural, extensionIso_tmul, extensionIso_tmul, tensorIsoSite_pure,
    scalarTensorBinaryInverse_tmul, scalarExtension_map_tmul, tensorIsoSite_inv_pure,
    extensionIso_inv_tmul]

attribute [local semireducible] monoidalCategory

private noncomputable def comparisonUnitIso {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S) :
    changeOfRings a (𝟙_ (ScalarExtensionConstraintModules (J := J) A)) ≅
      𝟙_ (ScalarExtensionConstraintModules (J := J) S) :=
  extensionIso (J := J) a _ ≪≫ scalarExtensionUnitIso a

private noncomputable abbrev unitForward {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S) :=
  (comparisonUnitIso (J := J) a).hom

private theorem unitForward_tmul {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S)
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : A.obj.obj U) :
    (unitForward (J := J) a).val.app U
      (scalarExtensionConstraintTmul (J := J) a
        (𝟙_ (ScalarExtensionConstraintModules (J := J) A)) U x s) =
      s * a.hom.app U x := by
  change (scalarExtensionUnitIso a).hom.val.app U
    ((extensionIso (J := J) a _).hom.val.app U _) = _
  erw [extensionIso_tmul, scalarExtensionUnitIso_tmul]

private theorem unitBackward_tmul {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S)
    (U : Cᵒᵖ) (s : S.obj.obj U) :
    (comparisonUnitIso (J := J) a).inv.val.app U s =
      scalarExtensionConstraintTmul (J := J) a
        (𝟙_ (ScalarExtensionConstraintModules (J := J) A)) U (1 : A.obj.obj U) s := by
  have h := unitForward_tmul (J := J) a U s 1
  rw [map_one, mul_one] at h
  have hi := congrArg (fun f ↦ f.val.app U
    (scalarExtensionConstraintTmul (J := J) a
      (𝟙_ (ScalarExtensionConstraintModules (J := J) A)) U (1 : A.obj.obj U) s))
    (comparisonUnitIso (J := J) a).hom_inv_id
  change (comparisonUnitIso (J := J) a).inv.val.app U
    ((unitForward (J := J) a).val.app U _) = _ at hi
  rw [h] at hi
  exact hi

private theorem tensorTriple_ext (R : Sheaf J CommRingCat.{w})
    (M N P T : ScalarExtensionConstraintModules (J := J) R) (f g : (M ⊗ N) ⊗ P ⟶ T)
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) (z : P.val.obj U),
      f.val.app U (scalarExtensionConstraintPureTensor (J := J) R (M ⊗ N) P U
        (scalarExtensionConstraintPureTensor (J := J) R M N U x y) z) =
      g.val.app U (scalarExtensionConstraintPureTensor (J := J) R (M ⊗ N) P U
        (scalarExtensionConstraintPureTensor (J := J) R M N U x y) z)) : f = g  := by
  let e : (siteSheafTensorRight P).obj ((siteSheafTensorRight N).obj M) ≅ (M ⊗ N) ⊗ P :=
    (tensorIsoSite (J := J) R ((siteSheafTensorRight N).obj M) P).symm ≪≫
      ((tensorIsoSite (J := J) R M N).symm ⊗ᵢ Iso.refl P)
  apply (cancel_epi e.hom).mp
  obtain ⟨eqv, hnorm, hnat, hext⟩ := tensor_trilinear_universal (J := J) R
  apply (hext M N P T _ _).mpr
  intro U x y z
  have hp : e.hom.val.app U
      (siteSheafTensorTmul ((siteSheafTensorRight N).obj M) P U
        (siteSheafTensorTmul M N U x y) z) =
      scalarExtensionConstraintPureTensor (J := J) R (M ⊗ N) P U
        (scalarExtensionConstraintPureTensor (J := J) R M N U x y) z := by
    change (((tensorIsoSite (J := J) R M N).inv ⊗ₘ 𝟙 P).val.app U)
      ((tensorIsoSite (J := J) R ((siteSheafTensorRight N).obj M) P).inv.val.app U _) = _
    rw [tensorIsoSite_inv_pure, pure_natural, tensorIsoSite_inv_pure]
    rfl
  change f.val.app U (e.hom.val.app U _) = g.val.app U (e.hom.val.app U _)
  rw [hp]
  exact h U x y z

private theorem extensionTriple_ext {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S)
    (M N P : ScalarExtensionConstraintModules (J := J) A) (T : ScalarExtensionConstraintModules
      (J := J) S)
    (f g : changeOfRings (J := J) a ((M ⊗ N) ⊗ P) ⟶ T)
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) (z : P.val.obj U),
      f.val.app U (scalarExtensionConstraintTmul (J := J) a ((M ⊗ N) ⊗ P) U
        (scalarExtensionConstraintPureTensor (J := J) A (M ⊗ N) P U
          (scalarExtensionConstraintPureTensor (J := J) A M N U x y) z) 1) =
      g.val.app U (scalarExtensionConstraintTmul (J := J) a ((M ⊗ N) ⊗ P) U
        (scalarExtensionConstraintPureTensor (J := J) A (M ⊗ N) P U
          (scalarExtensionConstraintPureTensor (J := J) A M N U x y) z) 1)) : f = g := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) A) :=
    cochainModulesMonoidal (J := J) A
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) S) :=
    cochainModulesMonoidal (J := J) S
  let F := restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)
  have he : insertMap (J := J) a ((M ⊗ N) ⊗ P) ≫ F.map f =
      insertMap (J := J) a ((M ⊗ N) ⊗ P) ≫ F.map g := by
    apply tensorTriple_ext (J := J) A M N P (F.obj T)
    intro U x y z
    exact h U x y z
  apply extension_ext (J := J) a ((M ⊗ N) ⊗ P) T f g
  intro U x
  exact congrArg (fun t ↦ t.val.app U x) he

private theorem pure_whiskerLeft (R : Sheaf J CommRingCat.{w})
    (M : ScalarExtensionConstraintModules (J := J) R) {N N' : ScalarExtensionConstraintModules
      (J := J) R}
    (g : N ⟶ N') (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (M ◁ g).val.app U (scalarExtensionConstraintPureTensor (J := J) R M N U x y) =
      scalarExtensionConstraintPureTensor (J := J) R M N' U x (g.val.app U y) := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) R) :=
    cochainModulesMonoidal (J := J) R
  simpa only [id_tensorHom, id_val, PresheafOfModules.id_app, ModuleCat.id_apply] using
    pure_natural (J := J) R (𝟙 M) g U x y

private theorem pure_whiskerRight (R : Sheaf J CommRingCat.{w})
    {M M' : ScalarExtensionConstraintModules (J := J) R} (f : M ⟶ M')
    (N : ScalarExtensionConstraintModules (J := J) R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (f ▷ N).val.app U (scalarExtensionConstraintPureTensor (J := J) R M N U x y) =
      scalarExtensionConstraintPureTensor (J := J) R M' N U (f.val.app U x) y := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) R) :=
    cochainModulesMonoidal (J := J) R
  simpa only [tensorHom_id, id_val, PresheafOfModules.id_app, ModuleCat.id_apply] using
    pure_natural (J := J) R f (𝟙 N) U x y

private theorem forward_natural {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S)
    {M M' N N' : ScalarExtensionConstraintModules (J := J) A} (f : M ⟶ M') (g : N ⟶ N') :
    changeOfRingsHom (J := J) a (M ⊗ N) (f ⊗ₘ g) ≫ (comparisonIso (J := J) a M' N').hom =
      (comparisonIso (J := J) a M N).hom ≫ (changeOfRingsHom (J := J) a M f ⊗ₘ changeOfRingsHom
        (J := J) a N g) := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) A) :=
    cochainModulesMonoidal (J := J) A
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) S) :=
    cochainModulesMonoidal (J := J) S
  apply extensionTensor_ext (J := J) a M N (changeOfRings (J := J) a M' ⊗ changeOfRings (J := J) a
    N')
  intro U x y
  change (forwardMap (J := J) a M' N').val.app U
      ((changeOfRingsHom (J := J) a (M ⊗ N) (f ⊗ₘ g)).val.app U _) =
    (changeOfRingsHom (J := J) a M f ⊗ₘ changeOfRingsHom (J := J) a N g).val.app U
      ((forwardMap (J := J) a M N).val.app U _)
  rw [extension_map_tmul, pure_natural, forwardMap_tmul, forwardMap_tmul,
    pure_natural, extension_map_tmul, extension_map_tmul]

private theorem forward_associativity {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S)
    (M N P : ScalarExtensionConstraintModules (J := J) A) :
    changeOfRingsHom (J := J) a ((M ⊗ N) ⊗ P) (α_ M N P).hom ≫
        (comparisonIso (J := J) a M (N ⊗ P)).hom ≫
          (changeOfRings (J := J) a M ◁ (comparisonIso (J := J) a N P).hom) =
      (comparisonIso (J := J) a (M ⊗ N) P).hom ≫
        ((comparisonIso (J := J) a M N).hom ▷ changeOfRings (J := J) a P) ≫
          (α_ (changeOfRings (J := J) a M) (changeOfRings (J := J) a N) (changeOfRings (J := J) a
            P)).hom := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) A) :=
    cochainModulesMonoidal (J := J) A
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) S) :=
    cochainModulesMonoidal (J := J) S
  apply extensionTriple_ext (J := J) a M N P _
  intro U x y z
  change (changeOfRings (J := J) a M ◁ (forwardMap (J := J) a N P)).val.app U
      ((forwardMap (J := J) a M (N ⊗ P)).val.app U
        ((changeOfRingsHom (J := J) a ((M ⊗ N) ⊗ P) (α_ M N P).hom).val.app U _)) =
    (α_ (changeOfRings (J := J) a M) (changeOfRings (J := J) a N) (changeOfRings (J := J) a
      P)).hom.val.app U
      ((forwardMap (J := J) a M N ▷ changeOfRings (J := J) a P).val.app U
        ((forwardMap (J := J) a (M ⊗ N) P).val.app U _))
  rw [extension_map_tmul, pure_assoc, forwardMap_tmul, pure_whiskerLeft,
    forwardMap_tmul, forwardMap_tmul, pure_whiskerRight, forwardMap_tmul, pure_assoc]

private theorem forward_left_unit {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S)
    (M : ScalarExtensionConstraintModules (J := J) A) :
    (comparisonIso (J := J) a (𝟙_ (ScalarExtensionConstraintModules (J := J) A)) M).hom ≫
        ((comparisonUnitIso (J := J) a).hom ▷ changeOfRings (J := J) a M) ≫
          (λ_ (changeOfRings (J := J) a M)).hom =
      changeOfRingsHom (J := J) a ((𝟙_ (ScalarExtensionConstraintModules (J := J) A)) ⊗ M) (λ_
        M).hom := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) A) :=
    cochainModulesMonoidal (J := J) A
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) S) :=
    cochainModulesMonoidal (J := J) S
  apply extensionTensor_ext (J := J) a (𝟙_ (ScalarExtensionConstraintModules (J := J) A)) M _
  intro U x y
  change (λ_ (changeOfRings (J := J) a M)).hom.val.app U
      ((unitForward (J := J) a ▷ changeOfRings (J := J) a M).val.app U
        ((forwardMap (J := J) a _ M).val.app U _)) =
    (changeOfRingsHom (J := J) a _ (λ_ M).hom).val.app U _
  rw [forwardMap_tmul, pure_whiskerRight, unitForward_tmul, one_mul,
    pure_left_unit, extension_map_tmul, pure_left_unit]
  exact ((insertMap (J := J) a M).val.app U).hom.map_smul x y |>.symm

private theorem forward_right_unit {A S : Sheaf J CommRingCat.{w}} (a : A ⟶ S)
    (M : ScalarExtensionConstraintModules (J := J) A) :
    (comparisonIso (J := J) a M (𝟙_ (ScalarExtensionConstraintModules (J := J) A))).hom ≫
        (changeOfRings (J := J) a M ◁ (comparisonUnitIso (J := J) a).hom) ≫
          (ρ_ (changeOfRings (J := J) a M)).hom =
      changeOfRingsHom (J := J) a (M ⊗ (𝟙_ (ScalarExtensionConstraintModules (J := J) A))) (ρ_
        M).hom := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) A) :=
    cochainModulesMonoidal (J := J) A
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) S) :=
    cochainModulesMonoidal (J := J) S
  apply extensionTensor_ext (J := J) a M (𝟙_ (ScalarExtensionConstraintModules (J := J) A)) _
  intro U x y
  change (ρ_ (changeOfRings (J := J) a M)).hom.val.app U
      ((changeOfRings (J := J) a M ◁ unitForward (J := J) a).val.app U
        ((forwardMap (J := J) a M _).val.app U _)) =
    (changeOfRingsHom (J := J) a _ (ρ_ M).hom).val.app U _
  rw [forwardMap_tmul, pure_whiskerLeft, unitForward_tmul, one_mul,
    pure_right_unit, extension_map_tmul, pure_right_unit]
  exact ((insertMap (J := J) a M).val.app U).hom.map_smul y x |>.symm

end Construction

attribute [local semireducible] changeOfRings changeOfRingsHom
  scalarExtensionConstraintTmul

/-- The insertion-normalized scalar extension constraints are unique natural
isomorphisms, with the scalar-multiplication inverse formula, and satisfy the
three oplax and three lax coherence equations.

Source: Stacks Project, Modules on Sites, Section 03EK, Tags 03CY and 0GMW;
explicit scalar-extension argument extracted in the DAG node.
(blueprint: lem-pd-sheaf-scalar-extension-constraint-coherence)

Proof:
1. The sheafification adjunction and tensorObjIsoSheafification detect binary
maps on canonical local pure tensors. The induced lax monoidal forgetful
functor gives their naturality, associator and unitor formulas. Transport the
proved trilinear equality criterion along the tensor presentation to detect
maps on canonical local pure triples. No global generation of sheaf sections
is assumed.
2. Identity section maps identify the two scalar-extension presheaves, hence
identify their sheafifications. The proved siteTensorRightIso and the canonical
tensor presentation identify the explicit site tensor with the localization tensor.
Both comparisons preserve the sheafification images of pure tensors.
3. Transport scalarTensorBinaryIso along these comparisons. Its proved forward
formula sends s tensor (x tensor y) to (s tensor x) tensor (1 tensor y), and
its inverse multiplies the two scalar factors. The generator test proves
uniqueness and naturality of the transported comparison.
4. Transport scalarExtensionUnitIso by the scalar-extension identification.
Its generator formula is s tensor a to s alpha(a). The inverse formula follows
from the isomorphism identities by substituting a=1.
5. On pure triples both oplax associativity composites have value
q(x) tensor (q(y) tensor q(z)). The actual associator formula and the
trilinear equality test prove the equation.
6. The two unit diagrams reduce to alpha(a) q(x) = q(a x), by the actual
unitor formulas and A-linearity of insertion.
7. Cancel the invertible forward constraints in these three equations to
obtain the three lax equations. No flatness or nonzero-ring hypothesis enters.

Dependencies: def-weil-presheaf-modules-sheafification,
def-weil-pbc-module-tensor-product, def-pc-sheaf-restrict-scalars,
def-pur-sheaf-tensor-product, lem-sp-scalar-extension-binary-coherence,
lem-weil-pbc-independent-sheaf-tensor-colimits,
lem-pd-sheaf-trilinear-universal. -/
theorem scalarExtension_constraint_coherence
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{w} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (A S : Sheaf J CommRingCat.{w}) (α : A ⟶ S) :
    Nonempty (ScalarExtensionConstraintData.{uC, vC, w} A S α) := by
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) A) :=
    cochainModulesMonoidal (J := J) A
  let : MonoidalCategory (ScalarExtensionConstraintModules (J := J) S) :=
    cochainModulesMonoidal (J := J) S
  let d := comparisonIso (J := J) α
  let e := comparisonUnitIso (J := J) α
  refine ⟨⟨d, e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro H K U h k
    exact forwardMap_tmul (J := J) α H K U h k 1
  · intro H K f hf
    apply extensionTensor_ext (J := J) α H K _
    intro U h k
    exact (hf U h k).trans (forwardMap_tmul (J := J) α H K U h k 1).symm
  · intro H K H' K' f g
    exact forward_natural (J := J) α f g
  · exact unitForward_tmul (J := J) α
  · exact unitBackward_tmul (J := J) α
  · exact forwardMap_tmul (J := J) α
  · exact backwardMap_tmul (J := J) α
  · exact forward_associativity (J := J) α
  · exact forward_left_unit (J := J) α
  · exact forward_right_unit (J := J) α
  · intro H K L
    apply (cancel_mono ((d H (K ⊗ L)).hom ≫
      (changeOfRings (J := J) α H ◁ (d K L).hom))).mp
    simp only [Category.assoc]
    rw [forward_associativity (J := J) α]
    simp only [d, Iso.inv_hom_id_assoc, ← comp_whiskerRight_assoc,
      Iso.inv_hom_id, id_whiskerRight, Category.id_comp,
      ← MonoidalCategory.whiskerLeft_comp, Category.comp_id,
      MonoidalCategory.whiskerLeft_id]
  · intro H
    rw [← forward_left_unit (J := J) α H]
    simp only [d, e, Iso.inv_hom_id_assoc, ← comp_whiskerRight_assoc,
      Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  · intro H
    rw [← forward_right_unit (J := J) α H]
    simp only [d, e, Iso.inv_hom_id_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp]

end SheafOfModules
