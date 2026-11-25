/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantModulePushforwardFunctoriality
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatSingleTensorCompatibilityDataSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorNaturality
public import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorAssociativity
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorSymmetry
public import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorFactorization
public import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorPullback
public import WeilConjectures.AlgebraicGeometry.EtaleSingleHomotopyTensorPullback
public import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackCounit
public import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorHomotopyFactorization
public import WeilConjectures.CategoryTheory.FlatPairingAssociativityAssembly
public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.CategoryTheory.FlatPairingPullbackAssembly
import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.Finite.BaseChange
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.OpenClosed.Vanishing
import WeilConjectures.SixFunctors.OpenClosed.Points
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

/-!
# Closed constant coefficient tensors on the small étale site

## Main definitions

* `closedConstantTensorMap`: multiplication after restriction to the intersection.
* `closedConstantSupportChange`: canonical maps comparing chosen fiber products.
* `closedConstantDerivedTensorMap`: multiplication through the flat degree-zero computation.
* `closedConstantDerivedPullbackMap`: inverse image on the degree-zero support model.

## Main statements

* `closedConstantModule_flat`: geometric-stalk flatness for every closed support.
* `closedConstantTensor`: invertibility and all ordinary and derived coherence clauses.

## References

* Stacks Tag 03QP(1)
* Stacks Tag 01JA
* Tag 03Q1(3)
* Stacks Tag 03Q1(3)
* Stacks Tags 03Q1 and 03PU
* Stacks Tags 06YQ and 03EL
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uB

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry
namespace Etale

open _root_.AlgebraicGeometry.Scheme

attribute [local instance] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance] sheafMonoidalCategory sheafBraidedCategory sheafMonoidalClosed

/-- The constant module sheaf of a ring on a small étale site. -/
noncomputable abbrev constantModuleSheaf (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  𝟙_ (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))

/-- The ordinary direct image of the constant module along a scheme map. -/
noncomputable def closedConstantModule (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  (lowerStar (ModuleCat.{u + 1} A) i).obj (constantModuleSheaf A C)

/-- The support morphism of the scheme-theoretic intersection of two closed subschemes. -/
noncomputable def intersectionSupport {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) :
    pullback i j ⟶ X := pullback.fst i j ≫ i

/-- Scheme-theoretic intersections of closed immersions are closed immersions. -/
instance intersectionSupport_isClosedImmersion {C D X : Scheme.{u}}
    (i : C ⟶ X) (j : D ⟶ X) [IsClosedImmersion i] [IsClosedImmersion j] :
    IsClosedImmersion (intersectionSupport i j) := by
  change IsClosedImmersion (pullback.fst i j ≫ i)
  infer_instance

/-- Canonical restriction of constant sections to a closed intersection.
It is the mate of the constant-sheaf comparison under the inverse-image/direct-image
adjunction, with the pullback pasting comparison included. -/
noncomputable def closedConstantRestriction (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    closedConstantModule A i ⟶ closedConstantModule A (intersectionSupport i j) :=
  constantModulePushforwardMap A (ModuleCat.of A A) i (intersectionSupport i j)
    (pullback.fst i j) (by simp [intersectionSupport, pullback.condition,
      -pullback.fst_comp_eq_toBase, -pullback.snd_comp_eq_toBase])

/-- The corresponding restriction from the second support to the same intersection. -/
noncomputable def closedConstantRestriction₂ (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    closedConstantModule A j ⟶ closedConstantModule A (intersectionSupport i j) :=
  constantModulePushforwardMap A (ModuleCat.of A A) j (intersectionSupport i j)
    (pullback.snd i j) (by simp [intersectionSupport, pullback.condition,
      -pullback.fst_comp_eq_toBase, -pullback.snd_comp_eq_toBase])

/-- Pointwise multiplication on the constant module, transported through the sheaf tensor
unitors. -/
noncomputable def constantModuleMultiplication (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    constantModuleSheaf A T ⊗ constantModuleSheaf A T ⟶ constantModuleSheaf A T :=
  (tensorIso (Iso.refl _) (Iso.refl _)).hom ≫ (λ_ _).hom

/-- The canonical ordinary tensor map, obtained from the two restriction maps and the lax
monoidal structure on direct image. This is the specified multiplication on local constants,
not an arbitrary morphism. -/
noncomputable def closedConstantTensorMap (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    closedConstantModule A i ⊗ closedConstantModule A j ⟶
      closedConstantModule A (intersectionSupport i j) :=
  tensorHom (closedConstantRestriction A i j) (closedConstantRestriction₂ A i j) ≫
    (Functor.LaxMonoidal.μ
      (lowerStar (ModuleCat.{u + 1} A) (intersectionSupport i j)) _ _) ≫
    (lowerStar (ModuleCat.{u + 1} A) (intersectionSupport i j)).map
      (constantModuleMultiplication A (pullback i j))

/-- The pullback-section map before taking its adjoint. It is defined by precomposition on
constant sections and the canonical lower-star composition comparison. -/
noncomputable def closedConstantPullbackMap (A : Type (u + 1)) [CommRing A]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] :
    closedConstantModule A i ⟶
      (lowerStar (ModuleCat.{u + 1} A) v).obj
        (closedConstantModule A (pullback.fst v i)) := by
  let q := pullback.snd v i
  let f₂ : pullback v i ⟶ X := pullback.fst v i ≫ v
  have hq : q ≫ i = f₂ := pullback.condition.symm
  exact constantModulePushforwardMap A (ModuleCat.of A A) i f₂ q hq ≫
    (lowerStarComp (ModuleCat.{u + 1} A) (pullback.fst v i) v f₂ rfl).inv.app _

/-- The canonical section map from the constant module on the base to a closed direct image.
It is the recorded transition map for `𝟙 X` and `i`, hence carries the constant section to
its restriction. -/
noncomputable def closedConstantSectionMap (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    constantModuleSheaf A X ⟶ closedConstantModule A i :=
  (lowerStarId (ModuleCat.{u + 1} A) X).inv.app _ ≫
    constantModulePushforwardMap A (ModuleCat.of A A) (𝟙 X) i i (by simp)

/-- The canonical adjoint pullback map, defined as the mate of
`closedConstantPullbackMap`. -/
noncomputable def closedConstantPullbackAdjoint (A : Type (u + 1)) [CommRing A]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] :
    (upperStar (ModuleCat.{u + 1} A) v).obj (closedConstantModule A i) ⟶
      closedConstantModule A (pullback.fst v i) :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _ |>.symm
    (closedConstantPullbackMap A i v)

/-- Compatibility of the specified pullback adjoint with the canonical constant section.
The displayed constant-sheaf comparison is part of the equation, so this does not merely assert
that some section map exists. -/
def closedConstantPullbackRestriction (A : Type (u + 1)) [CommRing A]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] : Prop :=
  (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) v).hom.app (ModuleCat.of A A) ≫
      closedConstantSectionMap A (pullback.fst v i) =
    (upperStar (ModuleCat.{u + 1} A) v).map (closedConstantSectionMap A i) ≫
      closedConstantPullbackAdjoint A i v

/-- Canonical change of support, contravariant in a morphism over the base. -/
noncomputable def closedConstantSupportChange (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    (g : D ⟶ C) (h : g ≫ i = j) : closedConstantModule A i ⟶ closedConstantModule A j :=
  constantModulePushforwardMap A (ModuleCat.of A A) i j g h

/-- The support identification for the identity pullback, induced by its universal lift. -/
noncomputable def closedConstantIdentitySupportMap (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) :
    closedConstantModule A (pullback.fst (𝟙 X) i) ⟶ closedConstantModule A i :=
  closedConstantSupportChange A _ _ (pullback.lift i (𝟙 C) (by simp)) (by simp)

/-- The canonical support comparison for successive base changes. -/
noncomputable def closedConstantCompositionSupportMap (A : Type (u + 1)) [CommRing A]
    {C X X' X'' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) (w : X'' ⟶ X') :
    closedConstantModule A (pullback.fst (w ≫ v) i) ⟶
      closedConstantModule A (pullback.fst w (pullback.fst v i)) :=
  closedConstantSupportChange A _ _
    (pullback.lift (pullback.fst w (pullback.fst v i))
      (pullback.snd w (pullback.fst v i) ≫ pullback.snd v i)
      (by
        rw [← Category.assoc, pullback.condition, Category.assoc,
          pullback.condition, Category.assoc]))
    (by simp)

/-- The support interchange map induced by the canonical pullback symmetry. -/
noncomputable def closedConstantSymmetrySupportMap (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) :
    closedConstantModule A (intersectionSupport j i) ⟶
      closedConstantModule A (intersectionSupport i j) :=
  closedConstantSupportChange A _ _ (pullbackSymmetry i j).hom
    (by simp [intersectionSupport, pullback.condition,
      -pullback.fst_comp_eq_toBase, -pullback.snd_comp_eq_toBase])

/-- The reassociation of triple supports, given by the universal pullback lifts. -/
noncomputable def closedConstantAssociativitySupportMap (A : Type (u + 1)) [CommRing A]
    {C D E X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (k : E ⟶ X) :
    closedConstantModule A (intersectionSupport (intersectionSupport i j) k) ⟶
      closedConstantModule A (intersectionSupport i (intersectionSupport j k)) := by
  let a := pullback.fst i (intersectionSupport j k)
  let b := pullback.snd i (intersectionSupport j k)
  let g : pullback i (intersectionSupport j k) ⟶ pullback i j :=
    pullback.lift a (b ≫ pullback.fst j k)
    (by
      dsimp only [a, b]
      simpa only [intersectionSupport, Category.assoc] using
        (pullback.condition (f := i) (g := intersectionSupport j k)))
  let q : pullback i (intersectionSupport j k) ⟶
      pullback (intersectionSupport i j) k :=
    pullback.lift g (b ≫ pullback.snd j k)
    (by
      calc
        g ≫ intersectionSupport i j = a ≫ i := by simp [g, intersectionSupport,
          -pullback.fst_comp_eq_toBase, -pullback.snd_comp_eq_toBase]
        _ = b ≫ intersectionSupport j k := pullback.condition
        _ = (b ≫ pullback.snd j k) ≫ k := by
          simpa only [intersectionSupport, Category.assoc] using
            congrArg (fun f : pullback j k ⟶ X ↦ b ≫ f)
              (pullback.condition (f := j) (g := k)))
  exact closedConstantSupportChange A _ _ q
    (by simp [q, g, a, intersectionSupport,
      -pullback.fst_comp_eq_toBase, -pullback.snd_comp_eq_toBase])

/-- The base-change identification of an intersection, induced by the universal lifts. -/
noncomputable def closedConstantBaseChangeSupportMap (A : Type (u + 1)) [CommRing A]
    {C D X X' : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (v : X' ⟶ X) :
    closedConstantModule A (pullback.fst v (intersectionSupport i j)) ⟶
      closedConstantModule A (intersectionSupport (pullback.fst v i) (pullback.fst v j)) := by
  let a := pullback.fst (pullback.fst v i) (pullback.fst v j)
  let b := pullback.snd (pullback.fst v i) (pullback.fst v j)
  let g : pullback (pullback.fst v i) (pullback.fst v j) ⟶ pullback i j :=
    pullback.lift (a ≫ pullback.snd v i) (b ≫ pullback.snd v j)
    (by
      dsimp only [a, b]
      rw [Category.assoc, ← pullback.condition, ← Category.assoc,
        pullback.condition, Category.assoc, pullback.condition, Category.assoc])
  let q : pullback (pullback.fst v i) (pullback.fst v j) ⟶
      pullback v (intersectionSupport i j) :=
    pullback.lift (a ≫ pullback.fst v i) g
    (by
      dsimp only [g, intersectionSupport]
      rw [Category.assoc, pullback.lift_fst_assoc, Category.assoc, pullback.condition])
  exact closedConstantSupportChange A _ _ q
    (by simp [q, a, intersectionSupport])

/-- Identity and composition laws with canonical changes of support explicitly composed. -/
def closedConstantPullbackCoherence (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] : Prop :=
  closedConstantPullbackAdjoint A i (𝟙 X) ≫ closedConstantIdentitySupportMap A i =
    (upperStarId (ModuleCat.{u + 1} A) X).hom.app (closedConstantModule A i) ∧
  ∀ {X' X'' : Scheme.{u}} (v : X' ⟶ X) (w : X'' ⟶ X'),
    closedConstantPullbackAdjoint A i (w ≫ v) ≫
        closedConstantCompositionSupportMap A i v w =
      (upperStarComp (ModuleCat.{u + 1} A) w v).hom.app (closedConstantModule A i) ≫
        (upperStar (ModuleCat.{u + 1} A) w).map (closedConstantPullbackAdjoint A i v) ≫
        closedConstantPullbackAdjoint A (pullback.fst v i) w

/-- The normalized tensor pullback square with its canonical support comparison. -/
def closedConstantTensorPullbackSquare (A : Type (u + 1)) [CommRing A]
    {C D X X' : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (v : X' ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] : Prop :=
  (upperStar (ModuleCat.{u + 1} A) v).map (closedConstantTensorMap A i j) ≫
      closedConstantPullbackAdjoint A (intersectionSupport i j) v ≫
      closedConstantBaseChangeSupportMap A i j v =
    Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) v) _ _ ≫
      tensorHom (closedConstantPullbackAdjoint A i v) (closedConstantPullbackAdjoint A j v) ≫
      closedConstantTensorMap A (pullback.fst v i) (pullback.fst v j)

/-- Ordinary associativity and symmetry with explicit canonical support changes. -/
def closedConstantTensorCoherence (A : Type (u + 1)) [CommRing A]
    {C D E X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (k : E ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion k] : Prop :=
  tensorHom (closedConstantTensorMap A i j) (𝟙 _) ≫
      closedConstantTensorMap A (intersectionSupport i j) k ≫
      closedConstantAssociativitySupportMap A i j k =
    (α_ _ _ _).hom ≫ tensorHom (𝟙 _) (closedConstantTensorMap A j k) ≫
      closedConstantTensorMap A i (intersectionSupport j k) ∧
  (β_ _ _).hom ≫ closedConstantTensorMap A j i ≫
      closedConstantSymmetrySupportMap A i j = closedConstantTensorMap A i j

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem transition_unit (A : Type (u + 1)) [CommRing A]
    {V D X : Scheme.{u}} (p : V ⟶ D) (g : D ⟶ X) (h : V ⟶ X)
    (hp : p ≫ g = h) :
    Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} A) g) ≫
      constantModulePushforwardMap A (ModuleCat.of A A) g h p hp =
    Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} A) h) := by
  unfold constantModulePushforwardMap
  erw [upperStarConstantSheafIso_hom_app_tensorUnit (ModuleCat.{u + 1} A) p]
  erw [Adjunction.unit_app_unit_comp_map_η]
  exact (ε_lowerStar_comp p g h hp.symm).symm

private theorem section_unit (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    closedConstantSectionMap A i =
      Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} A) i) := by
  unfold closedConstantSectionMap
  erw [← ε_lowerStar_id]
  exact transition_unit A i (𝟙 X) i (by simp)

private theorem section_epi (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    Epi (closedConstantSectionMap A i) := by
  erw [section_unit A i]
  erw [← (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit_app_unit_comp_map_η]
  have : Epi ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit.app
      (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))) :=
    (shortExact_openClosedShortComplex (ModuleCat.{u + 1} A)
      i.openComplement.ι i
      (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      i.range_eq_compl_range_openComplement_ι).epi_g
  exact epi_comp _ _

private theorem support_change_unit (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    (g : D ⟶ C) (h : g ≫ i = j) :
    Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} A) i) ≫
      closedConstantSupportChange A i j g h =
    Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} A) j) :=
  transition_unit A g i j h

@[reassoc]
private theorem tensor_unit (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    (closedConstantSectionMap A i ⊗ₘ closedConstantSectionMap A j) ≫
      closedConstantTensorMap A i j =
    (λ_ (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))).hom ≫
      closedConstantSectionMap A (intersectionSupport i j) := by
  erw [section_unit, section_unit, section_unit]
  dsimp only [closedConstantTensorMap, closedConstantRestriction, closedConstantRestriction₂]
  erw [tensorHom_comp_tensorHom_assoc]
  erw [transition_unit A (pullback.fst i j) i (intersectionSupport i j) rfl,
    transition_unit A (pullback.snd i j) j (intersectionSupport i j)
      pullback.condition.symm]
  have hm : constantModuleMultiplication A (pullback i j) =
      (λ_ (𝟙_ (Sheaf (pullback i j).smallEtaleTopology (ModuleCat.{u + 1} A)))).hom := by
    change (tensorIso (Iso.refl (𝟙_ _)) (Iso.refl _)).hom ≫ (λ_ (𝟙_ _)).hom = _
    simp only [tensorIso_hom, Iso.refl_hom,
      tensorHom_id, id_whiskerRight, Category.id_comp]
  erw [hm]
  change (Functor.LaxMonoidal.ε _ ⊗ₘ Functor.LaxMonoidal.ε _) ≫
    Functor.LaxMonoidal.μ _ (𝟙_ _) (𝟙_ _) ≫ _ = _
  erw [Functor.LaxMonoidal.ε_tensorHom_comp_μ_assoc]
  simp only [← Functor.map_comp, Iso.inv_hom_id]
  exact leftUnitor_naturality _

@[reassoc]
private theorem pullback_unit (A : Type (u + 1)) [CommRing A]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] :
    (upperStar (ModuleCat.{u + 1} A) v).map (closedConstantSectionMap A i) ≫
      closedConstantPullbackAdjoint A i v =
    Functor.OplaxMonoidal.η (upperStar (ModuleCat.{u + 1} A) v) ≫
      closedConstantSectionMap A (pullback.fst v i) := by
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _).injective
  erw [Adjunction.homEquiv_naturality_left, closedConstantPullbackAdjoint,
    Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right,
    upperStarLowerStarAdjunction_homEquiv_η, section_unit A i, section_unit A (pullback.fst v i)]
  dsimp only [closedConstantPullbackMap]
  erw [← Category.assoc, transition_unit A (pullback.snd v i) i
    (pullback.fst v i ≫ v) pullback.condition.symm]
  erw [ε_lowerStar_comp (Λ := A) (pullback.fst v i) v (pullback.fst v i ≫ v) rfl]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app, Category.comp_id]

private theorem pullback_restriction (A : Type (u + 1)) [CommRing A]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] :
    closedConstantPullbackRestriction A i v := by
  unfold closedConstantPullbackRestriction
  erw [pullback_unit A i v,
    upperStarConstantSheafIso_hom_app_tensorUnit (ModuleCat.{u + 1} A) v]

private theorem mate_symm_monoidal
    {V W V' W' : Type*} [Category V] [Category W] [Category V'] [Category W']
    [MonoidalCategory V] [MonoidalCategory W]
    [MonoidalCategory V'] [MonoidalCategory W']
    {L : V ⥤ W} {R : W ⥤ V} {L' : V' ⥤ W'} {R' : W' ⥤ V'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (F : V ⥤ V') (G : W ⥤ W')
    [L.Monoidal] [R.LaxMonoidal] [L'.Monoidal] [R'.LaxMonoidal]
    [F.LaxMonoidal] [G.LaxMonoidal] [adj.IsMonoidal] [adj'.IsMonoidal]
    (β : TwoSquare R G F R') [β.IsMonoidal] :
    NatTrans.IsMonoidal ((mateEquiv adj adj').symm β) := by
  change NatTrans.IsMonoidal
    ((Functor.leftUnitor _).inv ≫
      Functor.whiskerRight adj.unit (F ⋙ L') ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Functor.associator _ _ _).hom _ ≫
      Functor.whiskerRight (Functor.whiskerLeft L β) L' ≫
      Functor.whiskerRight (Functor.associator _ _ _).inv _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (L ⋙ G) adj'.counit ≫
      (Functor.rightUnitor _).hom)
  infer_instance

private theorem basechange_monoidal
    (A : Type (u + 1)) [CommRing A]
    {C' C X' X : Scheme.{u}} {q : C' ⟶ C} {r : C' ⟶ X'}
    {i : C ⟶ X} {v : X' ⟶ X} (sq : CommSq q r i v) :
    NatTrans.IsMonoidal (baseChangeMap (ModuleCat.{u + 1} A) sq) := by
  change NatTrans.IsMonoidal (baseChangeSquare (ModuleCat.{u + 1} A) sq)
  rw [baseChangeSquare_eq_mateEquiv_symm]
  have : NatTrans.IsMonoidal (squareLowerStarIso (ModuleCat.{u + 1} A) sq).hom := by
    dsimp only [squareLowerStarIso, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  exact mate_symm_monoidal _ _ _ _ _

private theorem pullback_iso (A : Type (u + 1)) [CommRing A]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] :
    IsIso (closedConstantPullbackAdjoint A i v) := by
  let B := ModuleCat.{u + 1} A
  let q := pullback.snd v i
  let r := pullback.fst v i
  let sq : IsPullback q r i v := (IsPullback.of_hasPullback v i).flip
  let b := (baseChangeMap B sq.toCommSq).app (𝟙_ _) ≫
    (lowerStar B r).map (Functor.OplaxMonoidal.η (upperStar B q))
  have hBC : NatTrans.IsMonoidal (baseChangeMap B sq.toCommSq) :=
    basechange_monoidal A sq.toCommSq
  have hb : (upperStar B v).map (closedConstantSectionMap A i) ≫ b =
      Functor.OplaxMonoidal.η (upperStar B v) ≫ closedConstantSectionMap A r := by
    erw [section_unit A i, section_unit A r]
    apply (cancel_epi (Functor.LaxMonoidal.ε (upperStar B v))).1
    dsimp only [b]
    have hu := NatTrans.IsMonoidal.unit (τ := baseChangeMap B sq.toCommSq)
    dsimp only [Functor.LaxMonoidal.comp_ε] at hu
    simp only [Category.assoc] at hu ⊢
    rw [reassoc_of% hu]
    simp only [← Functor.map_comp, Functor.Monoidal.ε_η,
      Functor.Monoidal.ε_η_assoc]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have : Epi (closedConstantSectionMap A i) := section_epi A i
  have he : closedConstantPullbackAdjoint A i v = b := by
    apply (cancel_epi ((upperStar B v).map (closedConstantSectionMap A i))).1
    exact (pullback_unit A i v).trans hb.symm
  rw [he]
  have := isIso_baseChangeMap_of_isFinite B sq
  dsimp only [b]
  apply IsIso.comp_isIso

attribute [local irreducible] closedConstantTensorMap closedConstantPullbackAdjoint

@[reassoc]
private theorem section_support_change (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (g : D ⟶ C) (h : g ≫ i = j) :
    closedConstantSectionMap A i ≫ closedConstantSupportChange A i j g h =
      closedConstantSectionMap A j := by
  erw [section_unit A i, section_unit A j]
  exact support_change_unit A i j g h

private theorem epi_pair {V : Type*} [Category V] [MonoidalCategory V]
    [MonoidalClosed V] [BraidedCategory V] [Abelian V]
    {M M' N N' : V} (f : M ⟶ M') (g : N ⟶ N') [Epi f] [Epi g] :
    Epi (f ⊗ₘ g) := by
  have : Epi ((tensorRight N).map f) := inferInstance
  have : Epi ((tensorLeft M').map g) := inferInstance
  rw [MonoidalCategory.tensorHom_def]
  change Epi (((tensorRight N).map f) ≫ ((tensorLeft M').map g))
  infer_instance

private theorem tensor_comp_left {V : Type*} [Category V] [MonoidalCategory V]
    {L M N P Q : V} (f : L ⟶ M) (g : M ⟶ N) (h : P ⟶ Q) :
    ((f ≫ g) ⊗ₘ h) = f ▷ P ≫ (g ⊗ₘ h) := by
  rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]

private theorem tensor_comp_right {V : Type*} [Category V] [MonoidalCategory V]
    {L M N P Q : V} (f : L ⟶ M) (g : N ⟶ P) (h : P ⟶ Q) :
    (f ⊗ₘ (g ≫ h)) = L ◁ g ≫ (f ⊗ₘ h) := by
  rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]

private theorem ordinary_coherence (A : Type (u + 1)) [CommRing A]
    {C D E X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (k : E ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion k] :
    closedConstantTensorCoherence A i j k := by
  have := section_epi A i
  have := section_epi A j
  have := section_epi A k
  have ha : closedConstantSectionMap A (intersectionSupport (intersectionSupport i j) k) ≫
      closedConstantAssociativitySupportMap A i j k =
      closedConstantSectionMap A (intersectionSupport i (intersectionSupport j k)) := by
    dsimp only [closedConstantAssociativitySupportMap]
    apply section_support_change
  have hs : closedConstantSectionMap A (intersectionSupport j i) ≫
      closedConstantSymmetrySupportMap A i j =
      closedConstantSectionMap A (intersectionSupport i j) := by
    apply section_support_change
  have := epi_pair (closedConstantSectionMap A i) (closedConstantSectionMap A j)
  have := epi_pair (closedConstantSectionMap A i ⊗ₘ closedConstantSectionMap A j)
    (closedConstantSectionMap A k)
  constructor
  · apply (cancel_epi ((closedConstantSectionMap A i ⊗ₘ closedConstantSectionMap A j) ⊗ₘ
      closedConstantSectionMap A k)).1
    erw [tensorHom_comp_tensorHom_assoc]
    erw [tensor_unit A i j]
    simp only [Category.comp_id]
    rw [tensor_comp_left, Category.assoc]
    erw [tensor_unit_assoc A (intersectionSupport i j) k]
    rw [ha]
    erw [associator_naturality_assoc]
    erw [tensorHom_comp_tensorHom_assoc, tensor_unit A j k]
    rw [tensor_comp_right, Category.assoc]
    erw [tensor_unit A i (intersectionSupport j k)]
    monoidal
  · apply (cancel_epi (closedConstantSectionMap A i ⊗ₘ
      closedConstantSectionMap A j)).1
    erw [BraidedCategory.braiding_naturality_assoc, tensor_unit_assoc A j i]
    rw [hs]
    erw [tensor_unit A i j]
    change (β_ (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
      (𝟙_ _)).hom ≫ (λ_ (𝟙_ _)).hom ≫ _ = (λ_ (𝟙_ _)).hom ≫ _
    simp only [braiding_tensorUnit_right, Category.assoc, unitors_equal,
      unitors_inv_equal, Iso.inv_hom_id_assoc]

private theorem ordinary_pullback_square (A : Type (u + 1)) [CommRing A]
    {C D X X' : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (v : X' ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    closedConstantTensorPullbackSquare A i j v := by
  have := section_epi A i
  have := section_epi A j
  let F := upperStar (ModuleCat.{u + 1} A) v
  have := epi_pair (closedConstantSectionMap A i) (closedConstantSectionMap A j)
  apply (cancel_epi (F.map (closedConstantSectionMap A i ⊗ₘ
    closedConstantSectionMap A j))).1
  erw [← Functor.map_comp_assoc, tensor_unit A i j, Functor.map_comp]
  erw [Category.assoc, pullback_unit_assoc A (intersectionSupport i j) v]
  have hs : closedConstantSectionMap A (pullback.fst v (intersectionSupport i j)) ≫
      closedConstantBaseChangeSupportMap A i j v =
      closedConstantSectionMap A (intersectionSupport (pullback.fst v i) (pullback.fst v j)) := by
    dsimp only [closedConstantBaseChangeSupportMap]
    apply section_support_change
  rw [hs]
  erw [← Functor.OplaxMonoidal.δ_natural_assoc F
    (closedConstantSectionMap A i) (closedConstantSectionMap A j)]
  erw [tensorHom_comp_tensorHom_assoc, pullback_unit A i v, pullback_unit A j v]
  rw [← tensorHom_comp_tensorHom_assoc]
  erw [tensor_unit A (pullback.fst v i) (pullback.fst v j)]
  erw [Functor.OplaxMonoidal.δ_comp_η_tensorHom_assoc F (Functor.OplaxMonoidal.η F)]
  erw [leftUnitor_naturality_assoc]
  simp only [Iso.inv_hom_id_assoc]
  rfl

private theorem naturality_unit_comp
    {V W Z : Type*} [Category V] [Category W] [Category Z]
    (F : V ⥤ W) (G : W ⥤ Z) (H : V ⥤ Z) (α : H ⟶ F ⋙ G)
    {U L : V} {U' L' : W} {U'' L'' : Z}
    (s : U ⟶ L) (s' : U' ⟶ L') (t : U'' ⟶ L'')
    (b : F.obj L ⟶ L') (c : G.obj L' ⟶ L'')
    (η : F.obj U ⟶ U') (ζ : G.obj U' ⟶ U'')
    (h : F.map s ≫ b = η ≫ s') (h' : G.map s' ≫ c = ζ ≫ t) :
    H.map s ≫ α.app L ≫ G.map b ≫ c =
      α.app U ≫ G.map η ≫ ζ ≫ t := by
  rw [α.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc, h']

private theorem oplax_unit_comp
    {V W Z : Type*} [Category V] [Category W] [Category Z]
    [MonoidalCategory V] [MonoidalCategory W] [MonoidalCategory Z]
    (F : V ⥤ W) (G : W ⥤ Z) (H : V ⥤ Z)
    [F.Monoidal] [G.Monoidal] [H.Monoidal]
    (α : H ⟶ F ⋙ G) [NatTrans.IsMonoidal α] :
    α.app (𝟙_ V) ≫ G.map (Functor.OplaxMonoidal.η F) ≫
      Functor.OplaxMonoidal.η G = Functor.OplaxMonoidal.η H := by
  apply (cancel_epi (Functor.LaxMonoidal.ε H)).1
  rw [← Category.assoc, ← Category.assoc, NatTrans.IsMonoidal.unit]
  simp only [Functor.LaxMonoidal.comp_ε, Category.assoc]
  rw [← Functor.map_comp_assoc, Functor.Monoidal.ε_η]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Functor.Monoidal.ε_η]

private theorem pullback_coherence (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    closedConstantPullbackCoherence A i := by
  let B := ModuleCat.{u + 1} A
  have := section_epi A i
  constructor
  · apply (cancel_epi ((upperStar B (𝟙 X)).map (closedConstantSectionMap A i))).1
    erw [pullback_unit_assoc A i (𝟙 X)]
    have hs : closedConstantSectionMap A (pullback.fst (𝟙 X) i) ≫
        closedConstantIdentitySupportMap A i = closedConstantSectionMap A i := by
      apply section_support_change
    rw [hs]
    erw [(upperStarId B X).hom.naturality (closedConstantSectionMap A i)]
    have hu : Functor.OplaxMonoidal.η (upperStar B (𝟙 X)) =
        (upperStarId B X).hom.app (𝟙_ (Sheaf X.smallEtaleTopology B)) := by
      apply ((upperStarLowerStarAdjunction B (𝟙 X)).homEquiv _ _).injective
      erw [upperStarLowerStarAdjunction_homEquiv_η B (𝟙 X)]
      change Functor.LaxMonoidal.ε (lowerStar B (𝟙 X)) =
        (upperStarLowerStarAdjunction B (𝟙 X)).unit.app _ ≫
          (lowerStar B (𝟙 X)).map ((upperStarId B X).hom.app _)
      rw [upperStarId_hom_app_unit_app, ε_lowerStar_id]
      rfl
    exact congrArg (fun f ↦ f ≫ closedConstantSectionMap A i) hu
  · intro X' X'' v w
    apply (cancel_epi ((upperStar B (w ≫ v)).map (closedConstantSectionMap A i))).1
    erw [pullback_unit_assoc A i (w ≫ v)]
    have hs : closedConstantSectionMap A (pullback.fst (w ≫ v) i) ≫
        closedConstantCompositionSupportMap A i v w =
        closedConstantSectionMap A (pullback.fst w (pullback.fst v i)) := by
      apply section_support_change
    rw [hs]
    have hn := naturality_unit_comp (upperStar B v) (upperStar B w)
      (upperStar B (w ≫ v)) (upperStarComp B w v).hom
      (closedConstantSectionMap A i) (closedConstantSectionMap A (pullback.fst v i))
      (closedConstantSectionMap A (pullback.fst w (pullback.fst v i)))
      (closedConstantPullbackAdjoint A i v)
      (closedConstantPullbackAdjoint A (pullback.fst v i) w)
      (Functor.OplaxMonoidal.η (upperStar B v))
      (Functor.OplaxMonoidal.η (upperStar B w))
      (pullback_unit A i v) (pullback_unit A (pullback.fst v i) w)
    have hu := oplax_unit_comp (upperStar B v) (upperStar B w)
      (upperStar B (w ≫ v)) (upperStarComp B w v).hom
    have hu' := congrArg (fun f ↦ f ≫
      closedConstantSectionMap A (pullback.fst w (pullback.fst v i))) hu.symm
    simp only [Category.assoc] at hu'
    exact hu'.trans hn.symm

private theorem closed_section_pullback_iso (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    IsIso ((upperStar (ModuleCat.{u + 1} A) i).map (closedConstantSectionMap A i)) := by
  rw [section_unit A i]
  erw [← (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).unit_app_unit_comp_map_η,
    Functor.map_comp]
  apply IsIso.comp_isIso

private theorem closed_stalk_section_iso (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ C) :
    IsIso (((Scheme.pointSmallEtale (t ≫ i)).ulift.{u + 1}).sheafFiber.map
      (closedConstantSectionMap A i)) :=
  isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map (ModuleCat.{u + 1} A) i
    (closedConstantSectionMap A i) (closed_section_pullback_iso A i) t

private theorem closed_stalk_zero (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (hs : s.base (IsLocalRing.closedPoint Ω) ∉ Set.range i.base) :
    IsZero (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber.obj
      (closedConstantModule A i)) := by
  let U := i.openComplement
  have hr : Set.range s.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact Scheme.range_base_subset_of_closedPoint_mem s hs
  let t := IsOpenImmersion.lift U.ι s hr
  have ht : t ≫ U.ι = s := IsOpenImmersion.lift_fac _ _ _
  have hz := isZero_upperStar_lowerStar_of_disjoint_range
    (ModuleCat.{u + 1} A) U.ι i
    (disjoint_range_of_range_eq_compl U.ι i
      i.range_eq_compl_range_openComplement_ι) (constantModuleSheaf A C)
  have hz' := ((Scheme.pointSmallEtale t).ulift.{u + 1}).sheafFiber.map_isZero hz
  have e := (upperStarCompUliftSheafFiberIso (ModuleCat.{u + 1} A) U.ι t).app
    ((lowerStar (ModuleCat.{u + 1} A) i).obj (constantModuleSheaf A C))
  rw [ht] at e
  exact hz'.of_iso e.symm

private theorem tensor_iso (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    IsIso (closedConstantTensorMap A i j) := by
  apply Scheme.isIso_of_isIso_sheafFiber_map
  intro x
  let s := X.algClosurePoint x
  let T := (Scheme.pointSmallEtale s).ulift.{u + 1}.sheafFiber
    (A := ModuleCat.{u + 1} A)
  change IsIso (T.map (closedConstantTensorMap A i j))
  by_cases hi : s.base (IsLocalRing.closedPoint _) ∈ Set.range i.base
  · by_cases hj : s.base (IsLocalRing.closedPoint _) ∈ Set.range j.base
    · obtain ⟨ti, hti, _⟩ := IsClosedImmersion.existsUnique_fac_of_field i s hi
      obtain ⟨tj, htj, _⟩ := IsClosedImmersion.existsUnique_fac_of_field j s hj
      let t := pullback.lift ti tj (hti.trans htj.symm)
      have ht : t ≫ intersectionSupport i j = s := by
        simp only [t, intersectionSupport, pullback.lift_fst_assoc, hti]
      have hei : IsIso (T.map (closedConstantSectionMap A i)) := by
        dsimp only [T]
        rw [← hti]
        exact closed_stalk_section_iso A i ti
      have hej : IsIso (T.map (closedConstantSectionMap A j)) := by
        dsimp only [T]
        rw [← htj]
        exact closed_stalk_section_iso A j tj
      have heij : IsIso (T.map (closedConstantSectionMap A (intersectionSupport i j))) := by
        dsimp only [T]
        rw [← ht]
        exact closed_stalk_section_iso A (intersectionSupport i j) t
      have he : IsIso (T.map (closedConstantSectionMap A i ⊗ₘ
          closedConstantSectionMap A j)) := by
        rw [Functor.Monoidal.map_tensor]
        infer_instance
      have hm := congrArg T.map (tensor_unit A i j)
      simp only [Functor.map_comp] at hm
      have hc : IsIso (T.map (closedConstantSectionMap A i ⊗ₘ
          closedConstantSectionMap A j) ≫ T.map (closedConstantTensorMap A i j)) := by
        rw [hm]
        apply IsIso.comp_isIso
      exact IsIso.of_isIso_comp_left
        (T.map (closedConstantSectionMap A i ⊗ₘ closedConstantSectionMap A j))
        (T.map (closedConstantTensorMap A i j))
    · have hzj := closed_stalk_zero A j s hj
      have hz : IsZero (T.obj (closedConstantModule A i ⊗ closedConstantModule A j)) := by
        exact ((tensorLeft (T.obj (closedConstantModule A i))).map_isZero hzj).of_iso
          (Functor.Monoidal.μIso T _ _).symm
      have hij : s.base (IsLocalRing.closedPoint _) ∉ Set.range (intersectionSupport i j).base := by
        intro h
        apply hj
        rw [show intersectionSupport i j = pullback.snd i j ≫ j from pullback.condition]
          at h
        exact (Set.range_comp_subset_range _ _) h
      exact (hz.isIso (closed_stalk_zero A (intersectionSupport i j) s hij) _)
  · have hzi := closed_stalk_zero A i s hi
    have hz : IsZero (T.obj (closedConstantModule A i ⊗ closedConstantModule A j)) := by
      exact ((tensorRight (T.obj (closedConstantModule A j))).map_isZero hzi).of_iso
        (Functor.Monoidal.μIso T _ _).symm
    have hij : s.base (IsLocalRing.closedPoint _) ∉ Set.range (intersectionSupport i j).base := by
      intro h
      apply hi
      exact (Set.range_comp_subset_range _ _) h
    exact (hz.isIso (closed_stalk_zero A (intersectionSupport i j) s hij) _)

attribute [local irreducible] closedConstantModule

/-- Closed constant direct images are flat, including empty supports and the zero ring. -/
theorem closedConstantModule_flat (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i] :
    ObjectProperty.flat (closedConstantModule A i) := by
  apply (flat_iff_forall_flat_sheafFiber_obj _).2
  intro Ω _ _ s
  let T := (Scheme.pointSmallEtale s).ulift.{u + 1}.sheafFiber
    (A := ModuleCat.{u + 1} A)
  change ObjectProperty.flat (T.obj (closedConstantModule A i))
  by_cases hs : s.base (IsLocalRing.closedPoint Ω) ∈ Set.range i.base
  · obtain ⟨t, ht, _⟩ := IsClosedImmersion.existsUnique_fac_of_field i s hs
    subst s
    have : IsIso (T.map (closedConstantSectionMap A i)) :=
      closed_stalk_section_iso A i t
    have hunit : ObjectProperty.flat (T.obj (constantModuleSheaf A X)) :=
      ObjectProperty.prop_of_iso ObjectProperty.flat (Functor.Monoidal.εIso T)
        ((ModuleCat.flat_iff_flat _).2 (inferInstance : Module.Flat A A))
    exact ObjectProperty.prop_of_iso ObjectProperty.flat
      (asIso (T.map (closedConstantSectionMap A i))) hunit
  · exact ObjectProperty.flat_of_isZero (closed_stalk_zero A i s hs)

set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false

/-- Apply an ordinary pairing after the canonical flat degree-zero tensor computation.
The coefficient category is left abstract while composing the two canonical arrows. -/
noncomputable def closedConstantFlatModelMap
    {B : Type uB} [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X : Scheme.{u}} (L F G : Sheaf X.smallEtaleTopology B)
    (h : ObjectProperty.flat L) (f : L ⊗ F ⟶ G) :
    ((derivedTensor B X).obj ((DerivedCategory.singleFunctor _ 0).obj L)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F) ⟶
        (DerivedCategory.singleFunctor _ 0).obj G :=
  singleFunctorFlatPairing L F G h f

attribute [local irreducible] closedConstantFlatModelMap

/-- The canonical derived multiplication on the specified flat degree-zero model. -/
noncomputable def closedConstantDerivedTensorMap (A : Type (u + 1)) [CommRing A]
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((DerivedCategory.singleFunctor _ 0).obj (closedConstantModule A i))).obj
        ((DerivedCategory.singleFunctor _ 0).obj (closedConstantModule A j)) ⟶
      (DerivedCategory.singleFunctor _ 0).obj
        (closedConstantModule A (intersectionSupport i j)) :=
  closedConstantFlatModelMap (B := ModuleCat.{u + 1} A) (X := X)
    (closedConstantModule A i) (closedConstantModule A j)
    (closedConstantModule A (intersectionSupport i j))
    (closedConstantModule_flat A i) (closedConstantTensorMap A i j)

attribute [local irreducible] closedConstantDerivedTensorMap

/-- The derived pullback map of the same supported constant sheaf, using the canonical
commutation of exact inverse image with the single functor and the specified b map. -/
noncomputable def closedConstantDerivedPullbackMap (A : Type (u + 1)) [CommRing A]
    {C X X' : Scheme.{u}} (i : C ⟶ X) (v : X' ⟶ X) [IsClosedImmersion i] :
    ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor).obj
      ((DerivedCategory.singleFunctor _ 0).obj (closedConstantModule A i)) ⟶
        (DerivedCategory.singleFunctor _ 0).obj
          (closedConstantModule A (pullback.fst v i)) :=
  singleFunctorPullbackMap v (closedConstantPullbackAdjoint A i v)

attribute [local irreducible] closedConstantDerivedPullbackMap

/-- Map two arrows with the actual derived tensor bifunctor, without synthesizing a
second monoidal instance on the derived category. -/
noncomputable def closedConstantDerivedPairMap
    {B : Type uB} [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) {K K' L L' : DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (f : K ⟶ K') (g : L ⟶ L') :
    ((derivedTensor B X).obj K).obj L ⟶ ((derivedTensor B X).obj K').obj L' :=
  derivedTensorPairMap X f g

/-- Derived associativity and symmetry for the specified canonical multiplication. -/
structure ClosedConstantDerivedTensorCoherence (A : Type (u + 1)) [CommRing A]
    {C D E X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (k : E ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] [IsClosedImmersion k] : Prop where
  associativity : CommSq
    (((derivedTensor (ModuleCat.{u + 1} A) X).map
      (closedConstantDerivedTensorMap A i j)).app _)
    (derivedTensorAssociator (ModuleCat.{u + 1} A) X _ _ _).hom
    (closedConstantDerivedTensorMap A (intersectionSupport i j) k ≫
      (DerivedCategory.singleFunctor _ 0).map (closedConstantAssociativitySupportMap A i j k))
    (((derivedTensor (ModuleCat.{u + 1} A) X).obj _).map
      (closedConstantDerivedTensorMap A j k) ≫
        closedConstantDerivedTensorMap A i (intersectionSupport j k))
  symmetry : (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app _).app _) ≫
    closedConstantDerivedTensorMap A j i ≫
      (DerivedCategory.singleFunctor _ 0).map (closedConstantSymmetrySupportMap A i j) =
        closedConstantDerivedTensorMap A i j

/-- Derived pullback compatibility for the specified multiplication and b maps. -/
structure ClosedConstantDerivedTensorPullbackSquare (A : Type (u + 1)) [CommRing A]
    {C D X X' : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (v : X' ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] : Prop where
  commutes : CommSq
    (((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor).map
      (closedConstantDerivedTensorMap A i j))
    (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) v).app _).app _ ≫
      closedConstantDerivedPairMap X' (closedConstantDerivedPullbackMap A i v)
        (closedConstantDerivedPullbackMap A j v))
    (closedConstantDerivedPullbackMap A (intersectionSupport i j) v ≫
      (DerivedCategory.singleFunctor _ 0).map (closedConstantBaseChangeSupportMap A i j v))
    (closedConstantDerivedTensorMap A (pullback.fst v i) (pullback.fst v j))

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section DerivedModels

variable {B : Type uB} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  {X : Scheme.{u}}

private theorem flat_model_eq (L M N : Sheaf X.smallEtaleTopology B)
    (hL : ObjectProperty.flat L) (f : L ⊗ M ⟶ N) :
    closedConstantFlatModelMap L M N hL f = singleFunctorFlatPairing L M N hL f := by
  unfold closedConstantFlatModelMap
  rfl

private theorem flat_model_iso (L M N : Sheaf X.smallEtaleTopology B)
    (hL : ObjectProperty.flat L) (f : L ⊗ M ⟶ N) [IsIso f] :
    IsIso (closedConstantFlatModelMap L M N hL f) := by
  unfold closedConstantFlatModelMap singleFunctorFlatPairing
  apply IsIso.comp_isIso

end DerivedModels

/-- Closed constant tensors, canonical pullback adjoints, flatness, and all ordinary and
derived coherence clauses, from the canonical flat degree-zero pairing compatibility.

The final two proposition structures state the derived associativity, symmetry and
pullback equalities, using `CommSq.w` for the associativity and pullback squares. -/
theorem closedConstantTensor (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) {C D E : Scheme.{u}}
    (i : C ⟶ X) [IsClosedImmersion i]
    (j : D ⟶ X) [IsClosedImmersion j]
    (k : E ⟶ X) [IsClosedImmersion k]
    {X' : Scheme.{u}} (v : X' ⟶ X) :
    IsIso (closedConstantPullbackAdjoint A i v) ∧
    IsIso (closedConstantPullbackAdjoint A j v) ∧
    IsIso (closedConstantPullbackAdjoint A (intersectionSupport i j) v) ∧
    closedConstantPullbackRestriction A i v ∧
    closedConstantPullbackRestriction A j v ∧
    closedConstantPullbackRestriction A (intersectionSupport i j) v ∧
    ObjectProperty.flat (closedConstantModule A i) ∧
    ObjectProperty.flat (closedConstantModule A j) ∧
    ObjectProperty.flat (closedConstantModule A (intersectionSupport i j)) ∧
    IsIso (closedConstantTensorMap A i j) ∧
    closedConstantTensorCoherence A i j k ∧
    closedConstantPullbackCoherence A i ∧
    closedConstantPullbackCoherence A j ∧
    closedConstantPullbackCoherence A (intersectionSupport i j) ∧
    closedConstantTensorPullbackSquare A i j v ∧
    IsIso (closedConstantDerivedTensorMap A i j) ∧
    ClosedConstantDerivedTensorCoherence A i j k ∧
    ClosedConstantDerivedTensorPullbackSquare A i j v := by
  have hi := closedConstantModule_flat A i
  have hj := closedConstantModule_flat A j
  have hij := closedConstantModule_flat A (intersectionSupport i j)
  have hi' := closedConstantModule_flat A (pullback.fst v i)
  have ht : IsIso (closedConstantTensorMap A i j) := tensor_iso A i j
  have hd : IsIso (closedConstantDerivedTensorMap A i j) := by
    unfold closedConstantDerivedTensorMap
    exact flat_model_iso _ _ _ hi _
  have hmono := etaleSingleFunctor_monoidalCompatibility (ModuleCat.{u + 1} A) v
  have hc := ordinary_coherence A i j k
  have hdc : ClosedConstantDerivedTensorCoherence A i j k := by
    constructor
    · constructor
      simpa only [closedConstantDerivedTensorMap, flat_model_eq] using
        hmono.associativity hi hj hij
          (closedConstantTensorMap A i j)
          (closedConstantTensorMap A (intersectionSupport i j) k)
          (closedConstantTensorMap A j k)
          (closedConstantTensorMap A i (intersectionSupport j k))
          (closedConstantAssociativitySupportMap A i j k)
          (by simpa only [tensorHom_id, id_tensorHom] using hc.1)
    · simpa only [closedConstantDerivedTensorMap, flat_model_eq] using
        hmono.symmetry hi hj
          (closedConstantTensorMap A i j) (closedConstantTensorMap A j i)
          (closedConstantSymmetrySupportMap A i j) hc.2
  have hdp : ClosedConstantDerivedTensorPullbackSquare A i j v := by
    constructor
    constructor
    simpa only [closedConstantDerivedTensorMap, flat_model_eq, closedConstantDerivedPullbackMap,
      closedConstantDerivedPairMap, derivedTensorPairMap, singleFunctorPullbackMap,
      Functor.map_comp, Category.assoc] using
      hmono.pullback hi hi'
        (closedConstantTensorMap A i j)
        (closedConstantTensorMap A (pullback.fst v i) (pullback.fst v j))
        (closedConstantPullbackAdjoint A i v) (closedConstantPullbackAdjoint A j v)
        (closedConstantPullbackAdjoint A (intersectionSupport i j) v ≫
          closedConstantBaseChangeSupportMap A i j v)
        (by simpa only [closedConstantTensorPullbackSquare, Category.assoc] using
          ordinary_pullback_square A i j v)
  exact ⟨pullback_iso A i v, pullback_iso A j v,
    pullback_iso A (intersectionSupport i j) v,
    pullback_restriction A i v, pullback_restriction A j v,
    pullback_restriction A (intersectionSupport i j) v, hi, hj, hij, ht, hc,
    pullback_coherence A i, pullback_coherence A j,
    pullback_coherence A (intersectionSupport i j), ordinary_pullback_square A i j v,
    hd, hdc, hdp⟩

end Etale
end AlgebraicGeometry
