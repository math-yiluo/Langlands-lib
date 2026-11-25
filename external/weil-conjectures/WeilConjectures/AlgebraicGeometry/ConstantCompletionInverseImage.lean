/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback

/-!
# Constant coefficient completion: InverseImage

Tower restriction, derived limit restriction, inverse-image data and ringed pullbacks.

Part of the split of `Sheaf.Paper.ConstantCompletionEquivalence`.
Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local irreducible] completed
variable {J A I}
attribute [local irreducible] derivedExtension
attribute [local irreducible] SheafOfModules.monoidalCategory
variable (J A I)
variable {J A I}
attribute [local irreducible] strictLimit
variable (J A I)
attribute [local irreducible] ordinaryUnit
attribute [local irreducible] quotientPresentation

variable {J A I}

/-- Levelwise restriction on strict module towers. Source: Stacks 0940
(auxiliary; not a blueprint node). -/
def tres {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (ℕᵒᵖ ⥤ Mod B) ⥤ (ℕᵒᵖ ⥤ Mod R) :=
  (Functor.whiskeringRight ℕᵒᵖ (Mod B) (Mod R)).obj (res φ)

/-- Levelwise restriction is additive and exact, since evaluation computes these laws.
Source: Stacks 0940 (auxiliary; not a blueprint node).
Proof: evaluate at every tower index. Restriction is additive and exact on module sheaves
by siteRestrictScalars_exact, and finite limits and colimits of functors are pointwise. -/
theorem tres_exact {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (tres φ).Additive ∧ PreservesFiniteLimits (tres φ) ∧
      PreservesFiniteColimits (tres φ) := by
  have := (siteRestrictScalars_exact φ).1
  have := (siteRestrictScalars_exact φ).2
  change ((Functor.whiskeringRight ℕᵒᵖ (Mod B) (Mod R)).obj (res φ)).Additive ∧ _
  dsimp only [tres, res]
  refine ⟨inferInstance, ⟨fun K _ _ ↦ ?_⟩, ⟨fun K _ _ ↦ ?_⟩⟩ <;> infer_instance

/-- The additive structure of the specified levelwise restriction.
Source: Stacks 0940 (auxiliary; not a blueprint node). -/
instance tres_additive {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    (tres φ).Additive := (tres_exact φ).1

/-- Finite limits for levelwise restriction.
Source: Stacks 0940 (auxiliary; not a blueprint node). -/
instance tres_finiteLimits {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesFiniteLimits (tres φ) := (tres_exact φ).2.1

/-- Finite colimits for levelwise restriction.
Source: Stacks 0940 (auxiliary; not a blueprint node). -/
instance tres_finiteColimits {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesFiniteColimits (tres φ) := (tres_exact φ).2.2

/-- Exact levelwise restriction induces restriction on the derived strict tower categories.
Source: Stacks 0940 (auxiliary; not a blueprint node). -/
def tdres {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) : TD B ⥤ TD R :=
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod R)
  letI := HasDerivedCategory.standard (ℕᵒᵖ ⥤ Mod B)
  letI := (siteRestrictScalars_exact φ).1
  letI := (siteRestrictScalars_exact φ).2
  (tres φ).mapDerivedCategory

/-- Restricting before forming the strict quotient tower is additive.
Source: Stacks 06YY (auxiliary; not a blueprint node).
Proof: at every tower index the functor is scalar restriction followed by scalar
extension and restriction. All three maps preserve sums of module homomorphisms.
Equality after every evaluation is equality in the strict functor category. -/
theorem restrictionReduction_additive (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] (I : Ideal A) :
    (res (coefficientMap J A I) ⋙ reductionTower J A I false).Additive := by
  have : (res (coefficientMap J A I)).Additive := inferInstance
  constructor
  intro M N f g
  change (reductionTower J A I false).map
    ((res (coefficientMap J A I)).map (f + g)) = _
  rw [Functor.map_add]
  exact Functor.map_add (reductionTower J A I false)

attribute [instance] restrictionReduction_additive

/-- Reducing and then restricting a completed-coefficient tower is additive.
Source: Stacks 06YY (auxiliary; not a blueprint node).
Proof: evaluate at every tower index. Scalar extension and both restrictions preserve
addition of module maps, so their composite does as well. -/
theorem reductionRestriction_additive (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] (I : Ideal A) :
    (reductionTower J A I true ⋙ tres (coefficientMap J A I)).Additive := by
  infer_instance

attribute [instance] reductionRestriction_additive

/-- The completed strict reduction followed by restriction preserves zero maps.
Source: Stacks 06YY (auxiliary; not a blueprint node).
Proof: apply the additive identity of reductionRestriction_additive to the zero map. -/
theorem reductionRestriction_preservesZero (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] (I : Ideal A) :
    (reductionTower J A I true ⋙ tres (coefficientMap J A I)).PreservesZeroMorphisms := by
  infer_instance

attribute [instance] reductionRestriction_preservesZero

-- Use the generic composite-functor instances while elaborating the remaining proofs.
-- Restore the exported instances at the end of the module.
attribute [-instance] restrictionReduction_additive reductionRestriction_additive
  reductionRestriction_preservesZero

section
attribute [local irreducible] dres change

end

section ExactScalarExtension
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The proved extension-tensor comparison, selected once for each module. -/
private def extensionTensorComponent {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (M : Mod R) :
    (SheafOfModules.monoidalCategory R).tensorObj
      ((res φ).obj (SheafOfModules.unit (siteModuleRings B))) M ≅
        (res φ).obj ((change φ).obj M) :=
  (SheafOfModules.exists_extensionTensorComparison φ M).choose

/-- Its section formula is the original balanced tensor map. -/
private theorem extensionTensorComponent_pure {R B : Sheaf J CommRingCat.{u}}
    (φ : R ⟶ B) (M : Mod R) (U : Cᵒᵖ) (s : B.obj.obj U) (m : M.val.obj U) :
    (extensionTensorComponent φ M).hom.val.app U
        (SheafOfModules.RingedTensor.pure R
          ((res φ).obj (SheafOfModules.unit (siteModuleRings B))) M U s m) =
      tensorSection φ M U s m :=
  (SheafOfModules.exists_extensionTensorComparison φ M).choose_spec U s m

attribute [irreducible] extensionTensorComponent

/-- The pure-tensor comparison is natural in the module argument.
Source: Stacks 03EK; the component is exists_extensionTensorComparison. -/
private def extensionTensorIso {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    letI := SheafOfModules.monoidalCategory R
    MonoidalCategory.tensorLeft ((res φ).obj (SheafOfModules.unit (siteModuleRings B))) ≅
      change φ ⋙ res φ := by
  letI := SheafOfModules.monoidalCategory R
  let N := (res φ).obj (SheafOfModules.unit (siteModuleRings B))
  refine NatIso.ofComponents (extensionTensorComponent φ) ?_
  intro M M' f
  apply SheafOfModules.RingedTensor.pure_hom_ext R N M
  intro U s m
  change (extensionTensorComponent φ M').hom.val.app U
      ((MonoidalCategory.whiskerLeft N f).val.app U
        (SheafOfModules.RingedTensor.pure R N M U s m)) =
    ((change φ).map f).val.app U
      ((extensionTensorComponent φ M).hom.val.app U
        (SheafOfModules.RingedTensor.pure R N M U s m))
  rw [← MonoidalCategory.id_tensorHom, SheafOfModules.RingedTensor.pure_map]
  change (extensionTensorComponent φ M').hom.val.app U
      (SheafOfModules.RingedTensor.pure R N M' U s (f.val.app U m)) = _
  rw [extensionTensorComponent_pure, extensionTensorComponent_pure]
  exact (tensorSection_map φ f U s m).symm

/-- Flatness of the target ring makes scalar extension exact.
Source: Stacks 03EK. Identify its restriction with tensoring by the flat target,
reflect finite limits through restriction, and use the extension adjunction for colimits. -/
private theorem change_exact {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (hflat : SheafOfModules.IsFlat
      ((res φ).obj (SheafOfModules.unit (siteModuleRings B)))) :
    PreservesFiniteLimits (change φ) ∧ PreservesFiniteColimits (change φ) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let N := (res φ).obj (SheafOfModules.unit (siteModuleRings B))
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight N) := hflat.1
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft N) :=
    preservesFiniteLimits_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight N).symm
  have : PreservesFiniteLimits (change φ ⋙ res φ) :=
    preservesFiniteLimits_of_natIso (extensionTensorIso φ)
  have : (res φ).ReflectsIsomorphisms := siteRestrictScalars_reflectsIsomorphisms φ
  have : PreservesFiniteLimits (res φ) := (siteRestrictScalars_exact φ).1
  have : ReflectsFiniteLimits (res φ) :=
    { reflects := fun K _ _ ↦ reflectsLimitsOfShape_of_reflectsIsomorphisms }
  have hleft : PreservesFiniteLimits (change φ) :=
    preservesFiniteLimits_of_reflects_of_preserves (change φ) (res φ)
  have : PreservesColimitsOfSize.{0, 0} (change φ) :=
    (SheafOfModules.RingedTensor.tensorAdjunction φ).leftAdjoint_preservesColimits
  have hright : PreservesFiniteColimits (change φ) := inferInstance
  exact ⟨hleft, hright⟩

end ExactScalarExtension

/-- Forget a module sheaf to its underlying sheaf of sets.
Source: Stacks 03D2 (auxiliary; not a blueprint node). -/
abbrev underlying (O : Sheaf J CommRingCat.{u}) : Mod O ⥤ Sheaf J (Type u) :=
  SheafOfModules.toSheaf (siteModuleRings O) ⋙ sheafCompose J (forget AddCommGrpCat)

/-- A sheaf map with a fixed section formula is unique. -/
private theorem sheaf_map_existsUnique_of_formula {X Y : Sheaf J (Type u)}
    (q : X ⟶ Y) (f : ∀ U : Cᵒᵖ, X.obj.obj U → Y.obj.obj U)
    (hq : ∀ U x, q.hom.app U x = f U x) :
    ∃! q' : X ⟶ Y, ∀ U x, q'.hom.app U x = f U x := by
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro m
  exact (hq' U m).trans (hq U m).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar-extension insertion is the unique underlying-sheaf map m ↦ 1 tensor m.
Source: Stacks 06YY (auxiliary; not a blueprint node).
Proof: the section formula commutes with restrictions by the pure-tensor formula for
changeOfRingsMap and naturality of the sheafification unit. Components determine the map. -/
theorem insertion_existsUnique {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) (M : Mod R) :
    ∃! q : (underlying R).obj M ⟶ (underlying S).obj ((change φ).obj M),
      ∀ (U : Cᵒᵖ) (m : M.val.obj U), q.hom.app U m = tensorSection φ M U 1 m := by
  let η := (scalarExtensionUnit_exists J φ).choose
  exact sheaf_map_existsUnique_of_formula
    ((underlying R).map (η.app M))
    (fun U m ↦ tensorSection φ M U 1 m)
    ((scalarExtensionUnit_exists J φ).choose_spec M)

/-- The actual scalar-extension insertion, including sheafification.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
def insertion {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) (M : Mod R) :
    (underlying R).obj M ⟶ (underlying S).obj ((change φ).obj M) :=
  (insertion_existsUnique φ M).exists.choose

variable {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}

set_option genSizeOf false in
set_option genInjectivity false in
/-- Algebraic lifts of a topos inverse image, coherently in all coefficient rings.
The existing AlgebraicInverseImage specifies every ring operation and module action on
all generalized sections. Naturality specifies its action on ring maps. The constant
comparison is natural in every commutative ring, fixing the canonical constant-object
identification, including its coefficient maps.
Source: Stacks 00YV, 03D2, 099L
(auxiliary; not a blueprint node). -/
structure InverseImageData (L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)) where
  rings : Sheaf J CommRingCat.{u} ⥤ Sheaf J' CommRingCat.{u}
  algebra : ∀ O : Sheaf J CommRingCat.{u},
    SheafOfModules.AlgebraicInverseImage L O (rings.obj O)
  ring_naturality : ∀ {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S),
    L.map ((sheafCompose J (forget CommRingCat)).map φ) ≫ (algebra S).ringUnderlying.hom =
      (algebra R).ringUnderlying.hom ≫
        (sheafCompose J' (forget CommRingCat)).map (rings.map φ)
  constants : constantSheaf J CommRingCat.{u} ⋙ rings ≅ constantSheaf J' CommRingCat.{u}

variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse-image maps to finite coefficients form the canonical projection cone.
Source: Stacks 099L (auxiliary; not a blueprint node).
Proof: apply F.rings to projection naturality and use naturality of F.constants for
A/I^(n+2) → A/I^(n+1). These are exactly the displayed cone equations. -/
theorem pulledProjection_naturality (A : Type u) [CommRing A] (I : Ideal A)
    {m n : ℕᵒᵖ} (f : m ⟶ n) :
    ((Functor.const ℕᵒᵖ).obj (F.rings.obj (completed J A I))).map f ≫
        (F.rings.map (projection J A I n.unop) ≫
          (F.constants.app (CommRingCat.of (A ⧸ I ^ (n.unop + 1)))).hom) =
      (F.rings.map (projection J A I m.unop) ≫
        (F.constants.app (CommRingCat.of (A ⧸ I ^ (m.unop + 1)))).hom) ≫
          (finiteSystem J' A I).map f := by
  have hstep (k : ℕ) :
      ((Functor.const ℕᵒᵖ).obj (F.rings.obj (completed J A I))).map
          (homOfLE (Nat.le_succ k)).op ≫
        (F.rings.map (projection J A I k) ≫
          (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom) =
      (F.rings.map (projection J A I (k + 1)) ≫
          (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1 + 1)))).hom) ≫
        (finiteSystem J' A I).map (homOfLE (Nat.le_succ k)).op := by
    simp only [Functor.const_obj_map, finiteSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    change F.rings.map (projection J A I k) ≫
        (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom =
      (F.rings.map (projection J A I (k + 1)) ≫
        (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1 + 1)))).hom) ≫
          transition J' A I k
    have hnat := F.constants.hom.naturality
      (CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ (k + 1))))
    change F.rings.map (transition J A I k) ≫
        (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom =
      (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1 + 1)))).hom ≫
        transition J' A I k at hnat
    have hproj : projection J A I (k + 1) ≫ transition J A I k =
        projection J A I k := by
      unfold projection completed
      simpa only [finiteSystem, Functor.ofOpSequence_map_homOfLE_succ] using
        limit.w (finiteSystem J A I) (homOfLE (Nat.le_succ k)).op
    calc
      _ = F.rings.map (projection J A I (k + 1) ≫ transition J A I k) ≫
          (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom := by rw [hproj]
      _ = _ := by rw [F.rings.map_comp, Category.assoc, hnat, Category.assoc]
  exact (NatTrans.ofOpSequence
    (F := (Functor.const ℕᵒᵖ).obj (F.rings.obj (completed J A I)))
    (G := finiteSystem J' A I)
    (fun k ↦ F.rings.map (projection J A I k) ≫
      (F.constants.app (CommRingCat.of (A ⧸ I ^ (k + 1)))).hom) hstep).naturality f

attribute [local semireducible] completed

/-- The canonical map from the inverse image of the completed coefficient sheaf to the
completion on the second site, formed from its finite projections.
Source: Stacks 099L (auxiliary; not a blueprint node). -/
def completedMap (A : Type u) [CommRing A] (I : Ideal A) :
    F.rings.obj (completed J A I) ⟶ completed J' A I :=
  limit.lift (finiteSystem J' A I)
    { pt := F.rings.obj (completed J A I)
      π :=
        { app := fun n ↦ F.rings.map (projection J A I n.unop) ≫
            (F.constants.app (CommRingCat.of (A ⧸ I ^ (n.unop + 1)))).hom
          naturality := fun {m n} f ↦ pulledProjection_naturality F A I (m := m) (n := n) f } }

attribute [local irreducible] completed

/-- Module inverse image followed by the existing sheafified scalar extension.
Source: Stacks 03D2, 06YY (auxiliary; not a blueprint node). -/
def pull {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) : Mod R ⥤ Mod S :=
  (F.algebra R).modules ⋙ change c

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Addition transport and underlying naturality make the algebraic module lift additive.
Abstracting the lift avoids repeatedly reducing the full inverse-image data record. -/
private theorem algebraModules_additive {R : Sheaf J CommRingCat.{u}}
    {RI : Sheaf J' CommRingCat.{u}}
    (AI : SheafOfModules.AlgebraicInverseImage L R RI) : AI.modules.Additive := by
  constructor
  intro M N f g
  ext U x
  let e := AI.moduleUnderlying
  let y := (e.hom.app M).hom.app U x
  have hy : (e.inv.app M).hom.app U y = x :=
    congrFun (congrArg (fun t ↦ t.hom.app U) (e.hom_inv_id_app M)) x
  have hn (k : M ⟶ N) :
      (e.inv.app N).hom.app U ((L.map ((underlying R).map k)).hom.app U y) =
        (AI.modules.map k).val.app U x := by
    have hh := congrFun
      (congrArg (fun t ↦ t.hom.app U) (e.inv.naturality k)) y
    change _ = (AI.modules.map k).val.app U
      ((e.inv.app M).hom.app U y) at hh
    exact hh.trans (congrArg ((AI.modules.map k).val.app U) hy)
  have h := AI.moduleAdd N ((underlying R).obj M)
    ((underlying R).map f) ((underlying R).map g) ((underlying R).map (f + g))
    (fun _ _ ↦ rfl) U y
  exact (hn (f + g)).symm.trans
    (h.trans (congrArg₂ (fun (a b : (AI.modules.obj N).val.obj U) ↦ a + b)
      (hn f) (hn g)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- This prescribed module pullback is additive.
Source: Stacks 03D2 (auxiliary; not a blueprint node).
Proof: the algebraic inverse-image lift preserves addition by its generalized-section
moduleAdd identity. The scalar-extension functor is additive, hence so is their composite. -/
theorem pull_additive {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) : (pull F c).Additive := by
  have := algebraModules_additive (F.algebra R)
  change ((F.algebra R).modules ⋙ change c).Additive
  infer_instance

attribute [instance] pull_additive

/-- Insertion after inverse image: u^(-1)M → u^(-1)M tensor S, with coefficient action
fixed by c. Source: Stacks 06YY
(auxiliary; not a blueprint node). -/
def pullInsertion {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) (M : Mod R) :
    L.obj ((underlying R).obj M) ⟶ (underlying S).obj ((pull F c).obj M) :=
  (F.algebra R).moduleUnderlying.inv.app M ≫ insertion c ((F.algebra R).modules.obj M)

set_option genSizeOf false in
set_option genInjectivity false in
/-- A universally specified derived pullback with computation on flat-term K-flat models.
Source: Stacks 06YY, 0G7E (auxiliary; not a blueprint node). -/
structure DerivedPull {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) where
  functor : D R ⥤ D S
  comparison : Q R ⋙ functor ⟶ (pull F c).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q S
  universal : functor.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (Mod R) (ComplexShape.up ℤ))
  computation : ∀ P : Cx R, P.IsKFlatTensor →
    (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) → IsIso (comparison.app P)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The recorded K-flat derived-pullback theorem supplies this universal derived pair.
Source: Stacks 06YY, 0G7E (auxiliary; not a blueprint node).
Proof: apply ringedTopoiDerivedPullback to the supplied geometric adjunction and algebraic
lift; pull has exactly its specified scalar-extension objects and maps. Flat-term K-flat
resolutions supply its resolving class. Transport the universal homotopy counit through
the quotient factorization to obtain the complex-level universal pair and computation. -/
theorem derivedPull_exists (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) : Nonempty (DerivedPull F c) := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  have ho (M : Mod R) : (pull F c).obj M =
      SheafOfModules.changeOfRings c ((F.algebra R).modules.obj M) := rfl
  have hm {M N : Mod R} (f : M ⟶ N) : (pull F c).map f =
      eqToHom (ho M) ≫ SheafOfModules.changeOfRingsHom c
        ((F.algebra R).modules.obj M) ((F.algebra R).modules.map f) ≫
          eqToHom (ho N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨T, ε, hu, _, _, hc, _⟩ :=
    SheafOfModules.ringedTopoiDerivedPullback L V adj (F.algebra R) c (pull F c) ho hm
  let : T.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (Mod R) (.up ℤ)) := hu
  have : T.IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension T ε
      (HomotopyCategory.quasiIso (Mod R) (.up ℤ))
  obtain ⟨β, hβ, hcomp⟩ := cochain_derived_counit (pull F c) T ε
  exact ⟨{ functor := T
           comparison := β
           universal := ⟨hβ⟩
           computation := fun P hp hf ↦ hcomp P (hc P hp hf) }⟩

variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [hL : PreservesFiniteLimits L]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The live K-flat and monoidal-flat interface for a prescribed ringed pullback. -/
private theorem basechange_flat_kFlat
    {R : Sheaf J CommRingCat.{u}} {RI S : Sheaf J' CommRingCat.{u}}
    (L : Sheaf J (Type u) ⥤ Sheaf J' (Type u))
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (AI : SheafOfModules.AlgebraicInverseImage L R RI)
    (c : RI ⟶ S) (T : Mod R ⥤ Mod S) [T.Additive]
    (ho : ∀ M : Mod R, T.obj M = SheafOfModules.changeOfRings c (AI.modules.obj M))
    (hm : ∀ {M N : Mod R} (f : M ⟶ N), T.map f = eqToHom (ho M) ≫
      SheafOfModules.changeOfRingsHom c (AI.modules.obj M) (AI.modules.map f) ≫
        eqToHom (ho N).symm)
    (P : Cx R) (hP : P.IsKFlatTensor)
    (hf : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) :
    CochainComplex.IsKFlatTensor
      ((T.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ q : ℤ, SheafOfModules.IsFlat (T.obj (P.X q)) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  have hf' (q : ℤ) := (exactFunctor (Mod R) (Mod R)).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (P.X q)).symm (hf q)
  obtain ⟨hk, hflat⟩ := SheafOfModules.isKFlat_ringedToposPullback L V adj
    AI c T ho hm P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP) hf'
  refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk, ?_⟩
  intro q
  exact (exactFunctor (Mod S) (Mod S)).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso S (T.obj (P.X q))) (hflat q)

include V adj hL in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pull_flat_kFlat {R : Sheaf J CommRingCat.{u}}
    {S : Sheaf J' CommRingCat.{u}} (c : F.rings.obj R ⟶ S) (P : Cx R)
    (hP : P.IsKFlatTensor) (hf : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) :
    CochainComplex.IsKFlatTensor
      (((pull F c).mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ q : ℤ, SheafOfModules.IsFlat ((pull F c).obj (P.X q)) := by
  have ho (M : Mod R) : (pull F c).obj M =
      SheafOfModules.changeOfRings c ((F.algebra R).modules.obj M) := rfl
  have hm {M N : Mod R} (f : M ⟶ N) : (pull F c).map f =
      eqToHom (ho M) ≫ SheafOfModules.changeOfRingsHom c
        ((F.algebra R).modules.obj M) ((F.algebra R).modules.map f) ≫
          eqToHom (ho N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  exact basechange_flat_kFlat L V adj (F.algebra R) c (pull F c) ho hm P hP hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem change_flat_kFlat {R S : Sheaf J CommRingCat.{u}}
    (c : R ⟶ S) (P : Cx R) (hP : P.IsKFlatTensor)
    (hf : ∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) :
    CochainComplex.IsKFlatTensor
      (((change c).mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ q : ℤ, SheafOfModules.IsFlat ((change c).obj (P.X q)) := by
  have ho (M : Mod R) : (change c).obj M = SheafOfModules.changeOfRings c M := rfl
  have hm {M N : Mod R} (f : M ⟶ N) : (change c).map f =
      eqToHom (ho M) ≫ SheafOfModules.changeOfRingsHom c M f ≫
        eqToHom (ho N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨hk, hflat⟩ :=
    SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
      c P (change c) ho hm
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP) hf
  exact ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk, hflat⟩

/-- Choose the derived pullback with its universal comparison, not an arbitrary lift.
Source: Stacks 06YY (auxiliary; not a blueprint node). -/
def derivedPull {R : Sheaf J CommRingCat.{u}} {S : Sheaf J' CommRingCat.{u}}
    (c : F.rings.obj R ⟶ S) : DerivedPull F c :=
  Classical.choice (derivedPull_exists F V adj c)

attribute [local irreducible] derivedPull pull change

/-- The canonical constant-coefficient structural isomorphism.
Source: Stacks 099L (auxiliary; not a blueprint node). -/
def constantMap (A : Type u) [CommRing A] : F.rings.obj (constant J A) ⟶ constant J' A :=
  (F.constants.app (CommRingCat.of A)).hom

end CategoryTheory.ConstantCompletion
