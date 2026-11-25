/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Kummer
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
/-!
# Relative supported Cartier Kummer boundary

Source: Stacks Project, Tags 03PL and 0A45; blueprint
sec-smooth-purity/sk-prop-sf-cbc/lem-amb-cartier-kummer-map.md
(auxiliary; not a blueprint node).

## Main definitions

* `supportedDivisorSection`: the section dual to the ideal inclusion.
* `SupportedKummerBoundary`: the normalized relative torsor-extension boundary.
* `supportedConstantExchange`: the canonical closed exchange on constants.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The adjunction unit on the constant sheaf, with its canonical constant comparison.
Source: Stacks 0A45 (auxiliary; not a blueprint node). -/
def supportedConstantUnit (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    ordinaryFiniteConstant A T ⟶
      (lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D) :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app
      (ModuleCat.of A A)).hom

/-- The integral constant sheaf used to evaluate a supported class on one.
Source: Stacks 03FD (auxiliary; not a blueprint node). -/
abbrev supportedIntegralConstant (T : Scheme.{u}) :=
  (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- Integral unit for a closed support, with the same inverse-image adjunction.
Source: Stacks 0A45 (auxiliary; not a blueprint node). -/
def supportedIntegralUnit {D T : Scheme.{u}} (i : D ⟶ T) :
    supportedIntegralConstant T ⟶
      (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D) :=
  (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).homEquiv _ _
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom

/-- The section one of the integral constant sheaf.
Source: Stacks 03FD (auxiliary; not a blueprint node). -/
def supportedIntegralOne (T : Scheme.{u}) :
    (supportedIntegralConstant T).obj.obj (op (Scheme.Etale.mk (𝟙 T))) :=
  (toSheafify T.smallEtaleTopology
    ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
      (op (Scheme.Etale.mk (𝟙 T))) (ULift.up 1)

/-- Map from the supported integral coefficient sheaf to the underlying A-coefficients.
Source: Stacks 03FD (auxiliary; not a blueprint node). -/
def supportedIntegralGenerator (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D) ⟶
      (moduleAbelianForget A T).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D)) :=
  (lowerStar AddCommGrpCat.{u + 1} i).map (ordinaryFiniteIntegralGenerator A D)

/-- The canonical section of O(D), transposed from the inclusion of its ideal.
Source: blueprint lemma-cycle-class-cartier-divisor, paragraph 1
(auxiliary; not a blueprint node). -/
def supportedDivisorSection {D T : Scheme.{u}} (i : D ⟶ T) :
    Scheme.Modules.unit T ⟶ Scheme.Modules.dual i.ker.toModules :=
  (SheafOfModules.unitHomEquiv _).symm
    ((SheafOfModules.homObjSectionsEquiv i.ker.toModules (Scheme.Modules.unit T)).symm
      i.ker.toModulesι)

/-- Restriction of the canonical divisor section, transported to the recorded frame
 torsor's ordinary-pullback interface by uniqueness of left adjoints.
Source: blueprint lemma-cycle-class-cartier-divisor, paragraph 1
(auxiliary; not a blueprint node). -/
def supportedDivisorSectionPullback {D T : Scheme.{u}} (i : D ⟶ T) (W : T.Opens) :
    (Scheme.Modules.pullback W.ι).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback W.ι).obj (Scheme.Modules.dual i.ker.toModules) :=
  let e := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction W.ι)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction W.ι)
  (e.app (Scheme.Modules.unit T)).inv ≫
    (Scheme.Modules.tensorPullback W.ι).map (supportedDivisorSection i) ≫
      (e.app (Scheme.Modules.dual i.ker.toModules)).hom

/-- The actual finite-coefficient Chern class, before the module/abelian comparison.
Source: Stacks 03PL (auxiliary; not a blueprint node). -/
@[irreducible]
def supportedKummerChern (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) {D T : Scheme.{u}} (i : D ⟶ T)
    (hI : i.ker.IsInvertible) (hT : IsUnit (N : Γ(T, ⊤))) :
    Sheaf.H ((moduleAbelianForget A T).obj
      (Scheme.finiteEtaleTateLine T N A hA)) 2 :=
  letI := hI.isInvertible_dual_toModules
  Sheaf.H.map (ordinaryFiniteRootMap A N hA T) 2
    (T.kummerδ₁ N hT (Scheme.Pic.toCohomologicalPicardGroup T
      (Scheme.Pic.ofIsInvertible (Scheme.Modules.dual i.ker.toModules))))

/-- The relative Kummer specification, in the extension model of relative cohomology.
The lifting torsor of E at the supported section one is the frame torsor of O(D),
and its specified section over the complementary open is sent to zero in E.
Thus it remembers the trivialization, not merely the ordinary Picard class.
Source: Stacks 03AJ, 03PL, 0A45 and blueprint lemma-cycle-class-cartier-divisor, paragraphs 1--4
(auxiliary; not a blueprint node). -/
@[irreducible]
def SupportedKummerBoundary (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (N : Γ(T, ⊤)))
    (c : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2) : Prop :=
  letI := hI.isInvertible_dual_toModules
  letI := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual i.ker.toModules)
  ∀ (W : T.Opens) (_hW : (W : Set T) = (Set.range i.base)ᶜ),
    ∃ (τ : (Scheme.Modules.etaleIsoTorsor (Scheme.Modules.dual i.ker.toModules)).sheaf.obj.obj
          (op (Scheme.Etale.mk W.ι)))
      (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
      (a : T.gmSheaf ⟶ E)
      (b : E ⟶ (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D))
      (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
      (f : (Scheme.Modules.etaleIsoTorsor (Scheme.Modules.dual i.ker.toModules)).sheaf ⟶
        (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj E),
      Scheme.Modules.etaleIsoTorsorVal (Scheme.Modules.dual i.ker.toModules) τ =
        supportedDivisorSectionPullback i W ∧
      (∀ (U : T.Etaleᵒᵖ) (g : T.gmSheaf.obj.obj U)
        (p : (Scheme.Modules.etaleIsoTorsor
          (Scheme.Modules.dual i.ker.toModules)).sheaf.obj.obj U),
        @id (E.obj.obj U) (f.hom.app U ((Scheme.Modules.etaleIsoTorsor
          (Scheme.Modules.dual i.ker.toModules)).vadd U g p)) =
          a.hom.app U g + (@id (E.obj.obj U) (f.hom.app U p))) ∧
      (∀ (U : T.Etaleᵒᵖ) (p : (Scheme.Modules.etaleIsoTorsor
          (Scheme.Modules.dual i.ker.toModules)).sheaf.obj.obj U),
        b.hom.app U (f.hom.app U p) =
          ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D)).obj.map
            ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T).from U.unop).op
            ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
              (supportedIntegralOne T))) ∧
      @id (E.obj.obj (op (Scheme.Etale.mk W.ι)))
        (f.hom.app (op (Scheme.Etale.mk W.ι)) τ) = 0 ∧
      (Ext.mk₀ (supportedIntegralGenerator A i)).comp
          (c.mapExactFunctor (moduleAbelianForget A T)) (zero_add 2) =
        (hE.extClass.comp (T.kummerSequence_shortExact N hT).extClass (rfl : 1 + 1 = 2)).comp
          (Ext.mk₀ (ordinaryFiniteRootMap A N hA T)) (add_zero 2)

end AlgebraicGeometry.Etale
