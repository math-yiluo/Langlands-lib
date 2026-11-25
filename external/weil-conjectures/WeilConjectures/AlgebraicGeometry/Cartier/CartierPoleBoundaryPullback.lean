/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeExtensionCohomologyNormalization
import WeilConjectures.AlgebraicGeometry.Cartier.CartierPairPullbackSection
import all WeilConjectures.AlgebraicGeometry.Relative.RelativeFramedExtensionPullback
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierPairTensorAddition
import all WeilConjectures.AlgebraicGeometry.CartierComplementFrame
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import all WeilConjectures.AlgebraicGeometry.Modules.SectionAvoidance
import all WeilConjectures.AlgebraicGeometry.InternalHomRestrictScheme

/-!
# Pullback of the integral Cartier pole extension

Source: blueprint lemma-cycle-class-cartier-divisor, relative trivialization paragraph;
Stacks 03AJ and 0A45 (blueprint: lem-asd-cartier-pole-boundary-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

attribute [local irreducible] Scheme.Modules.framePullbackMap

private theorem exists_poleComplementFrame {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    ∃ τ : (cartierPairFrameTorsor i hI).sheaf.obj.obj
        (op (Scheme.Etale.mk i.openComplement.ι)),
      cartierPairFrameVal i hI (U := op (Scheme.Etale.mk i.openComplement.ι)) τ =
        supportedDivisorSectionPullback i i.openComplement := by
  have hβ := (Classical.choose_spec (cartierPoleBoundary_existsUnique i hI)).1
  obtain ⟨τ, E, a, b, hab, hE, f, hτ, _⟩ := hβ i.openComplement rfl
  exact ⟨τ, hτ⟩

private theorem pole_pullback_of_framed_map {D D' T T' : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (i' : D' ⟶ T') [IsClosedImmersion i'] (hI' : i'.ker.IsInvertible)
    (v : T' ⟶ T) (w : D' ⟶ D) (sq : IsPullback w i' i v)
    (hW : i'.openComplement = v ⁻¹ᵁ i.openComplement)
    (τ : (cartierPairFrameTorsor i hI).sheaf.obj.obj
      (op (Scheme.Etale.mk i.openComplement.ι)))
    (hτ : cartierPairFrameVal i hI (U := op (Scheme.Etale.mk i.openComplement.ι)) τ =
      supportedDivisorSectionPullback i i.openComplement)
    (b : (cartierPairFrameTorsor i hI).sheaf.obj ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ v).op ⋙ (cartierPairFrameTorsor i' hI').sheaf.obj)
    (hb : ∀ (V : T.Etaleᵒᵖ) (g : T.gmSheaf.obj.obj V)
      (t : (cartierPairFrameTorsor i hI).sheaf.obj.obj V),
      b.app V ((cartierPairFrameTorsor i hI).vadd V g t) =
        (cartierPairFrameTorsor i' hI').vadd
          (op ((MorphismProperty.Over.pullback @Etale ⊤ v).obj V.unop))
          ((Scheme.gmSheafToLowerStarGmSheaf v).hom.app V g) (b.app V t))
    (hτ' : cartierPairFrameVal i' hI'
      (U := op (Scheme.Etale.mk i'.openComplement.ι))
      (relativeExtensionPulledFrame i i' v hW
        ⟨cartierPairFrameTorsor i hI, τ⟩ (cartierPairFrameTorsor i' hI') b).2 =
      supportedDivisorSectionPullback i' i'.openComplement) :
    (Ext.mk₀ (relativeExtensionExchange i i' v w sq.toCommSq)).comp
        (cartierPoleBoundary i' hI') (zero_add 1) =
      ((cartierPoleBoundary i hI).mapExactFunctor
        (upperStar AddCommGrpCat.{u + 1} v)).comp
        (Ext.mk₀ (Scheme.upperStarGmSheafToGmSheaf v)) (add_zero 1) := by
  let P : Sheaf.Torsor.WithSection T.gmSheaf (Scheme.Etale.mk i.openComplement.ι) :=
    ⟨cartierPairFrameTorsor i hI, τ⟩
  let Q := cartierPairFrameTorsor i' hI'
  let R := relativeExtensionPulledFrame i i' v hW P Q b
  have hPole : cartierPoleBoundary i hI = relativeExtension i P :=
    pole_boundary_eq_relative i hI τ hτ _
      (Classical.choose_spec (cartierPoleBoundary_existsUnique i hI)).1
  have hPole' : cartierPoleBoundary i' hI' = relativeExtension i' R :=
    pole_boundary_eq_relative i' hI' R.2 hτ' _
      (Classical.choose_spec (cartierPoleBoundary_existsUnique i' hI')).1
  have hn := relative_extension_pullback_square i i' v w sq hW
    (Scheme.gmSheafToLowerStarGmSheaf v) P Q b hb
  exact (congrArg (fun x ↦
    (Ext.mk₀ (relativeExtensionExchange i i' v w sq.toCommSq)).comp x (zero_add 1))
      hPole').trans (hn.trans (congrArg (fun x ↦
        (x.mapExactFunctor (upperStar AddCommGrpCat.{u + 1} v)).comp
          (Ext.mk₀ (Scheme.upperStarGmSheafToGmSheaf v)) (add_zero 1)) hPole.symm))

/-- The integral pole-extension class of a Cartier divisor commutes with pullback
of its Cartier pair. This is a degree-one identity with integral coefficients and
units, before either the Kummer connecting map or coefficient extension.

Source: blueprint lemma-cycle-class-cartier-divisor, paragraph beginning "All the cone
maps"; Stacks 03AJ and 0A45
(blueprint: lem-asd-cartier-pole-boundary-pullback).

Proof: identify the inverse-image ideal with the primed ideal by the cartesian
square. The Cartier dual comparison preserves their canonical sections, hence
induces an equivariant natural map of frame torsors preserving the complementary
frames. Identify each normalized pole class with the relative extension of this
framed torsor. Choose a representing primed relative extension. The mate of
closed exchange preserves supported one by the constant-unit compatibility. The
frame map induces a morphism from the source relative extension to its direct
image; its complementary frame is sent to zero. Adjunction gives a morphism
from the exact inverse image of the source extension to the primed extension,
with kernel map the units comparison and quotient map closed exchange.
Naturality of short-exact extension classes is the displayed equation. Only the
exchange morphism is needed, with no invertibility or flatness assumption on the
base map. The construction also applies to empty schemes and empty support. -/
theorem cartierPoleBoundary_pullback {D D' T T' : Scheme.{u}}
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (i' : D' ⟶ T') [IsClosedImmersion i'] (hI' : i'.ker.IsInvertible)
    (v : T' ⟶ T) (w : D' ⟶ D) (sq : IsPullback w i' i v) :
    (Ext.mk₀ (relativeExtensionExchange i i' v w sq.toCommSq)).comp
        (cartierPoleBoundary i' hI') (zero_add 1) =
      ((cartierPoleBoundary i hI).mapExactFunctor
        (upperStar AddCommGrpCat.{u + 1} v)).comp
        (Ext.mk₀ (Scheme.upperStarGmSheafToGmSheaf v)) (add_zero 1) := by
  have := hI.isInvertible_dual_toModules
  have := hI'.isInvertible_dual_toModules
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual i.ker.toModules)
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual i'.ker.toModules)
  have : SheafOfModules.IsInvertible.{u, u, u}
      ((Scheme.Modules.pullback v).obj (Scheme.Modules.dual i.ker.toModules)) :=
    SheafOfModules.IsInvertible.pullback inferInstance
  have hW : i'.openComplement = v ⁻¹ᵁ i.openComplement := by
    apply TopologicalSpace.Opens.ext
    change (Set.range i'.base)ᶜ = v ⁻¹' (Set.range i.base)ᶜ
    rw [Scheme.range_snd_of_isPullback sq]
    rfl
  obtain ⟨e, he⟩ := cartierPair_pullback_section i hI i' hI' v w sq
  obtain ⟨τ, hτ⟩ := exists_poleComplementFrame i hI
  let P : Sheaf.Torsor.WithSection T.gmSheaf (Scheme.Etale.mk i.openComplement.ι) :=
    ⟨cartierPairFrameTorsor i hI, τ⟩
  let Q := cartierPairFrameTorsor i' hI'
  let b := Scheme.Modules.framePullbackMap v (Scheme.Modules.dual i.ker.toModules)
    (Scheme.Modules.dual i'.ker.toModules) e
  let R := relativeExtensionPulledFrame i i' v hW P Q b
  have hτ' : cartierPairFrameVal i' hI'
      (U := op (Scheme.Etale.mk i'.openComplement.ι)) R.2 =
      supportedDivisorSectionPullback i' i'.openComplement := by
    let U := Scheme.Etale.mk i.openComplement.ι
    let U' := Scheme.Etale.mk i'.openComplement.ι
    let k : U' ⟶ (MorphismProperty.Over.pullback @Etale ⊤ v).obj U :=
      eqToHom (congrArg (fun W : T'.Opens ↦ Scheme.Etale.mk W.ι) hW) ≫
        openSectionPullback v i.openComplement
    have hp : Scheme.Modules.etaleIsoTorsorVal (Scheme.Modules.dual i.ker.toModules)
        (U := op U) τ =
        (Scheme.Modules.pullback i.openComplement.ι).map (supportedDivisorSection i) := by
      exact hτ.trans (pullbackSection_eq i i.openComplement)
    have hn := Scheme.Modules.framePullbackMap_section v
      (Scheme.Modules.dual i.ker.toModules) (Scheme.Modules.dual i'.ker.toModules) e
      (supportedDivisorSection i) (supportedDivisorSection i') he (op U) τ hp
    have hval : cartierPairFrameVal i' hI' (U := op U') =
        Scheme.Modules.etaleIsoTorsorVal (Scheme.Modules.dual i'.ker.toModules)
          (U := op U') := rfl
    rw [hval]
    dsimp only [R, relativeExtensionPulledFrame]
    erw [Scheme.Modules.etaleIsoTorsorVal_map, hn,
      Scheme.Modules.pullbackMap_presheaf_map, pullbackSection_eq]
    rfl
  exact pole_pullback_of_framed_map i hI i' hI' v w sq hW τ hτ b
    (Scheme.Modules.framePullbackMap_vadd v (Scheme.Modules.dual i.ker.toModules)
      (Scheme.Modules.dual i'.ker.toModules) e) hτ'

end AlgebraicGeometry.Etale
