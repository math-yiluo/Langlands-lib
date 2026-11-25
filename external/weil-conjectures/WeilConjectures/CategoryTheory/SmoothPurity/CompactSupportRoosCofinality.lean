/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement
public import WeilConjectures.CategoryTheory.StrictTowerArithmetic.StrictTowerArithmeticRestrictionDefs
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Strict.StrictRoosAdditiveComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.StrictTowerArithmetic.StrictTowerArithmeticRestrictionResolution
import Mathlib.CategoryTheory.Limits.Final

/-!
# Cofinality of the arithmetic Roos tower

Source: Stacks Project, Cohomology on Sites, Tag 0941, and Modules on Sites,
Tag 03EK; the explicit finite-block comparison and scalar-extension refinement
in the proof of `lem-pur-compact-support-integral-coefficient-comparison`
(blueprint: lem-pur-compact-support-roos-cofinality).

The category parameter below is instantiated by `Mod (underline A)` for a
small site and its constant ring sheaf.  The recorded arithmetic restriction,
selection and block maps are the canonical constructions from Tags 0H9K and
0941.  The proofs use these constructions before passing to the derived category.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u v uC vC r vA vB w

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic

namespace CategoryTheory

section CofinalityConstruction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {D : Type u} [Category.{v} D] [Abelian D] [HasCountableProducts D]
private noncomputable def rho (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (e : ℕ) (he : 1 ≤ e) :
    strictRoosComplex X ⟶ strictRoosComplex ((complexRestriction D e).obj X) :=
  strictRoosMapOfSquare (X := X) (Y := (complexRestriction D e).obj X)
    (selection e X.asFunctor) (block e X.asFunctor)
    (strictRoosBlock_comm X e he)
private theorem rho_coord (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (e : ℕ) (he : 1 ≤ e)
    (p : ℤ) :
    (rho X e he).f (p + 1) ≫
      (strictRoosCoordinates ((complexRestriction D e).obj X) p).hom =
    (strictRoosCoordinates X p).hom ≫
      biprod.map ((block e X.asFunctor).f p) ((selection e X.asFunctor).f (p + 1)) :=
  strictRoosMapOfSquare_coordinates (X := X)
    (Y := (complexRestriction D e).obj X) _ _ _ _
private theorem coord_ext {Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ}
    {K : CochainComplex D ℤ} {f g : K ⟶ strictRoosComplex Y}
    (h : ∀ p : ℤ, f.f (p + 1) ≫ (strictRoosCoordinates Y p).hom =
      g.f (p + 1) ≫ (strictRoosCoordinates Y p).hom) : f = g := by
  ext k
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  exact (cancel_mono (strictRoosCoordinates Y p).hom).1 (h p)
private theorem selection_nat {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (f : X ⟶ Y)
    (e : ℕ) :
    strictRoosProductMap f ≫ selection e Y.asFunctor =
      selection e X.asFunctor ≫
        strictRoosProductMap ((complexRestriction D e).map f) := by
  let φ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f
  change Limits.Pi.map (fun n : ℕ ↦ φ.app (op n)) ≫ selection e Y.asFunctor =
    selection e X.asFunctor ≫ Limits.Pi.map (fun n : ℕ ↦ φ.app ((index e).obj (op n)))
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc]
  erw [Pi.map_π]
  unfold selection
  erw [Pi.lift_comp_π_assoc, Pi.lift_comp_π, Pi.map_π]
  rfl

private theorem block_nat {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (f : X ⟶ Y)
    (e : ℕ) :
    strictRoosProductMap f ≫ block e Y.asFunctor =
      block e X.asFunctor ≫
        strictRoosProductMap ((complexRestriction D e).map f) := by
  let φ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f
  change Limits.Pi.map (fun n : ℕ ↦ φ.app (op n)) ≫ block e Y.asFunctor =
    block e X.asFunctor ≫ Limits.Pi.map (fun n : ℕ ↦ φ.app ((index e).obj (op n)))
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc]
  erw [Pi.map_π]
  unfold block
  erw [Pi.lift_comp_π_assoc, Pi.lift_comp_π]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro k hk
  erw [Pi.map_π_assoc]
  exact congrArg (fun t ↦ Pi.π _ _ ≫ t)
    ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).naturality _).symm

omit [HasCountableProducts D] in
private theorem biprod_lift_map {P Q P' Q' K : D}
    (a : K ⟶ P) (b : K ⟶ Q) (c : P ⟶ P') (d : Q ⟶ Q') :
    biprod.lift a b ≫ biprod.map c d = biprod.lift (a ≫ c) (b ≫ d) := by
  apply biprod.hom_ext <;> simp

private noncomputable def mu {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (f : X ⟶ Y) :
    strictRoosComplex X ⟶ strictRoosComplex Y :=
  strictRoosMapOfSquare _ _ (strictRoosProductMap_comm f)

private theorem mu_coord {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (f : X ⟶ Y) (p : ℤ) :
    (mu f).f (p + 1) ≫ (strictRoosCoordinates Y p).hom =
      (strictRoosCoordinates X p).hom ≫ biprod.map
        ((strictRoosProductMap f).f p) ((strictRoosProductMap f).f (p + 1)) :=
  strictRoosMapOfSquare_coordinates _ _ _ _

attribute [local irreducible] strictRoosMapOfSquare rho mu
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem rho_nat {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (f : X ⟶ Y)
    (e : ℕ) (he : 1 ≤ e) :
    mu f ≫ rho Y e he = rho X e he ≫ mu ((complexRestriction D e).map f) := by
  unfold mu rho strictRoosMapOfSquare
  rw [← Functor.map_comp, ← Functor.map_comp,
    ← HomologicalComplex.homotopyCofiber.mapArrowHom_comp,
    ← HomologicalComplex.homotopyCofiber.mapArrowHom_comp]
  congr 1
  congr 1
  apply Arrow.hom_ext
  · exact selection_nat f e
  · exact block_nat f e

private theorem roos_coordinates (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (p : ℤ) :
    roosχ X p = strictRoosCoordinates X p := rfl

private noncomputable def augment (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ)
    (P : CochainComplex D ℤ) (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n : ℕ,
      γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n) :
    P ⟶ strictRoosComplex X := by
  exact roosAugment (X := X) (P := P) γ hγ

private theorem augment_coordinates (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ)
    (P : CochainComplex D ℤ) (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n : ℕ,
      γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n) (p : ℤ) :
    (augment X P γ hγ).f (p + 1) ≫ (strictRoosCoordinates X p).hom =
      biprod.lift 0 ((Pi.lift γ).f (p + 1)) := by
  rw [← roos_coordinates]
  exact roosAugment_χ γ hγ p

private theorem square_comp {X Y Z W : CochainComplex (ℕᵒᵖ ⥤ D) ℤ}
    (hZW : Z = W)
    (a b : strictRoosProduct X ⟶ strictRoosProduct Y)
    (c d : strictRoosProduct Y ⟶ strictRoosProduct Z)
    (a' b' : strictRoosProduct X ⟶ strictRoosProduct W)
    (ha : HEq (a ≫ c) a') (hb : HEq (b ≫ d) b')
    (h₁ : a ≫ strictRoosEndomorphism Y = strictRoosEndomorphism X ≫ b)
    (h₂ : c ≫ strictRoosEndomorphism Z = strictRoosEndomorphism Y ≫ d)
    (h₃ : a' ≫ strictRoosEndomorphism W = strictRoosEndomorphism X ≫ b') :
    HEq (strictRoosMapOfSquare a b h₁ ≫ strictRoosMapOfSquare c d h₂)
      (strictRoosMapOfSquare a' b' h₃) := by
  subst W
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hb
  apply heq_of_eq
  unfold strictRoosMapOfSquare
  rw [← Functor.map_comp, ← HomologicalComplex.homotopyCofiber.mapArrowHom_comp]
  rfl

private def ceilIndex (e : ℕ) : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (show ℕ →o ℕ from
    { toFun := fun n ↦ n / e
      monotone' := fun _ _ h ↦ Nat.div_le_div_right h }).monotone.functor.op
private lemma arithmetic_gc (e : ℕ) (he : 1 ≤ e) (i n : ℕ) :
    i / e ≤ n ↔ i ≤ e * (n + 1) - 1 := by
  have hp : 0 < e := he
  rw [Nat.div_le_iff_le_mul_add_pred hp]
  rw [Nat.mul_add, Nat.mul_one]
  omega
private def indexAdjunction (e : ℕ) (he : 1 ≤ e) : index e ⊣ ceilIndex e :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun n i ↦
        { toFun := fun f ↦ (homOfLE ((arithmetic_gc e he i.unop n.unop).2 f.unop.le)).op
          invFun := fun f ↦ (homOfLE ((arithmetic_gc e he i.unop n.unop).1 f.unop.le)).op
          left_inv := fun _ ↦ Subsingleton.elim _ _
          right_inv := fun _ ↦ Subsingleton.elim _ _ } }

private theorem rho_nat_coordinates {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ}
    (f : X ⟶ Y) (e : ℕ) (he : 1 ≤ e)
    (μ : strictRoosComplex X ⟶ strictRoosComplex Y)
    (μe : strictRoosComplex ((complexRestriction D e).obj X) ⟶
      strictRoosComplex ((complexRestriction D e).obj Y))
    (hμ : ∀ p : ℤ, μ.f (p + 1) ≫ (strictRoosCoordinates Y p).hom =
      (strictRoosCoordinates X p).hom ≫ biprod.map
        ((strictRoosProductMap f).f p) ((strictRoosProductMap f).f (p + 1)))
    (hμe : ∀ p : ℤ, μe.f (p + 1) ≫
      (strictRoosCoordinates ((complexRestriction D e).obj Y) p).hom =
      (strictRoosCoordinates ((complexRestriction D e).obj X) p).hom ≫ biprod.map
        ((strictRoosProductMap ((complexRestriction D e).map f)).f p)
        ((strictRoosProductMap ((complexRestriction D e).map f)).f (p + 1))) :
    μ ≫ rho Y e he = rho X e he ≫ μe := by
  have h₁ : μ = mu f := by
    apply coord_ext
    intro p
    rw [hμ, mu_coord]
  have h₂ : μe = mu ((complexRestriction D e).map f) := by
    apply coord_ext
    intro p
    rw [hμe, mu_coord]
  rw [h₁, h₂]
  exact rho_nat f e he

private theorem limit_selection [HasLimitsOfShape ℕᵒᵖ D]
    (I : ℕᵒᵖ ⥤ CochainComplex D ℤ) (e : ℕ) :
    Pi.lift (fun n : ℕ ↦ limit.π I (op n)) ≫ selection e I =
      limit.pre I (index e) ≫
        Pi.lift (f := fun n : ℕ ↦ I.obj ((index e).obj (op n)))
          (fun n : ℕ ↦ limit.π (index e ⋙ I) (op n)) := by
  apply Pi.hom_ext
  intro n
  simp only [selection, Category.assoc, Pi.lift_comp_π, limit.pre_π]
  rfl

attribute [local irreducible] strictRoosComplex strictRoosCoordinates in
private theorem rho_limit_coordinates [HasLimitsOfShape ℕᵒᵖ D]
    (I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (e : ℕ) (he : 1 ≤ e)
    (ι : limit I.asFunctor ⟶ strictRoosComplex I)
    (ιe : limit ((complexRestriction D e).obj I).asFunctor ⟶
      strictRoosComplex ((complexRestriction D e).obj I))
    (hι : ∀ p : ℤ, ι.f (p + 1) ≫ (strictRoosCoordinates I p).hom =
      biprod.lift 0 ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)))
    (hιe : ∀ p : ℤ, ιe.f (p + 1) ≫
      (strictRoosCoordinates ((complexRestriction D e).obj I) p).hom =
      biprod.lift 0 ((Pi.lift (fun n : ℕ ↦
        limit.π ((complexRestriction D e).obj I).asFunctor (op n))).f (p + 1))) :
    ι ≫ rho I e he = limit.pre I.asFunctor (index e) ≫ ιe := by
  apply coord_ext
  intro p
  dsimp only [strictRoosProduct] at hι hιe ⊢
  simp only [HomologicalComplex.comp_f, Category.assoc]
  erw [rho_coord, ← Category.assoc, hι, hιe, biprod_lift_map, zero_comp]
  apply biprod.hom_ext
  · erw [Category.assoc, biprod.lift_fst, biprod.lift_fst, comp_zero]
  · erw [Category.assoc, biprod.lift_snd, biprod.lift_snd]
    change ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n)) ≫
      selection e I.asFunctor).f (p + 1)) =
      (limit.pre I.asFunctor (index e) ≫ Pi.lift (fun n : ℕ ↦
        limit.π (((complexRestriction D e).obj I).asFunctor) (op n))).f (p + 1)
    exact congrArg (fun t ↦ t.f (p + 1)) (limit_selection I.asFunctor e)

attribute [local irreducible] strictRoosComplex strictRoosCoordinates

private theorem rho_quasiIso
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    (hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)]
    (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ)
    (e : ℕ) (he : 1 ≤ e) : QuasiIso (rho X e he) := by
  let D := ringedSiteModules.{max uC vC r} R
  let := HasDerivedCategory.standard D
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ D)
  obtain ⟨RF, η, hRF, hη, hres, _⟩ :=
    ringedStrictTowerHomotopyLimitOfUniverses.{max uC vC r + 1, uC, vC, r} J R hcomm
  obtain ⟨I, j, hI, hj⟩ := hres X
  have := hI
  have := hj
  have : CochainComplex.IsKInjective ((complexRestriction D e).obj I) :=
    restriction_preservesKInjectives D e he I
  have : QuasiIso ((complexRestriction D e).map j) := inferInstance
  obtain ⟨μ, ι, _, hμ, hι, _, hμq, hιq, _⟩ :=
    strictRoosDerivedLimitComparison.{max uC vC r + 1, uC, vC, r} J R hcomm X I j
  obtain ⟨μe, ιe, _, hμe, hιe, _, hμeq, hιeq, _⟩ :=
    strictRoosDerivedLimitComparison.{max uC vC r + 1, uC, vC, r} J R hcomm
      ((complexRestriction D e).obj X) ((complexRestriction D e).obj I)
      ((complexRestriction D e).map j)
  have : QuasiIso μ := hμq
  have : QuasiIso μe := hμeq
  have : QuasiIso ι := hιq
  have : QuasiIso ιe := hιeq
  let l := limit.pre I.asFunctor (index e)
  have : (index e).Initial := Functor.initial_of_adjunction (indexAdjunction e he)
  have : IsIso l := by dsimp [l]; infer_instance
  have hlim : ι ≫ rho I e he = l ≫ ιe :=
    rho_limit_coordinates I e he ι ιe hι hιe
  have hIq : QuasiIso (rho I e he) := by
    have h : QuasiIso (ι ≫ rho I e he) := by rw [hlim]; infer_instance
    exact (quasiIso_iff_comp_left ι _).mp h
  have hnat : μ ≫ rho I e he = rho X e he ≫ μe :=
    rho_nat_coordinates j e he μ μe hμ hμe
  have : QuasiIso (rho I e he) := hIq
  have h : QuasiIso (rho X e he ≫ μe) := by rw [← hnat]; infer_instance
  exact (quasiIso_iff_comp_right _ μe).mp h

end CofinalityConstruction

attribute [local irreducible] strictRoosComplex strictRoosCoordinates

section ScalarAugmentation
variable {E : Type u} {H : Type v} [Category.{vA} E] [Category.{vB} H]
    [Abelian E] [Abelian H] [HasCountableProducts E] [HasCountableProducts H]
    (F : E ⥤ H) [F.Additive]

end ScalarAugmentation

end CategoryTheory
