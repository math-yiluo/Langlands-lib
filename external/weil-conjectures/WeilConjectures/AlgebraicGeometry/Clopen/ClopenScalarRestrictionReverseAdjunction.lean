/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenUnitEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.Algebra.Homology.ClopenComparisonTensorSquare.ClopenReverseModuleAdjunction

/-! # Reverse adjunction for clopen restriction with identified coefficients

The interface retains literal module restriction and hides the instance-heavy
ordinary/system normalization package used by the proof.
(blueprint: lem-cbc-clopen-scalar-restriction-reverse-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- On a clopen immersion, scalar-identified restriction is also left adjoint to
any of its left adjoints. Source: Stacks 04TS, disjoint two-open module gluing.
(blueprint: lem-cbc-clopen-scalar-restriction-reverse-adjunction).
Proof: literal restriction is projection under disjoint clopen gluing, and extension
by zero is insertion of a zero component, hence is both its left and right adjoint.
The coefficient identification induces an equivalence by restriction of scalars.
Compose the two adjunctions with this equivalence. Uniqueness of left adjoints
identifies the composite extension with L; transport the reverse adjunction across
that isomorphism. This works also for an empty clopen piece. -/
theorem clopenScalarRestrictionReverseAdjunction {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [IsClosedImmersion j]
    [(proEtaleOpenComposition j).IsContinuous (ProEt.topology U) (ProEt.topology T)]
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (c : S ≅ ((proEtaleOpenComposition j).sheafPushforwardContinuous
      CommRingCat.{t + 1} (ProEt.topology U) (ProEt.topology T)).obj R)
    (L : proEtaleRingModules U S ⥤ proEtaleRingModules T R)
    (adj : L ⊣ SheafOfModules.pushforward (F := proEtaleOpenComposition j)
      ((sheafCompose (ProEt.topology U)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map c.hom)) :
    Nonempty (SheafOfModules.pushforward (F := proEtaleOpenComposition j)
      ((sheafCompose (ProEt.topology U)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map c.hom) ⊣ L) := by
  obtain ⟨e, ar, _⟩ :=
    SheafOfModules.ClopenComparisonTensorSquare.clopen_reverse_module_adjunction
      .ordinary j R
  let rc := (sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).mapIso c
  let E := proEtaleScalarEquivalence U rc
  let F : proEtaleRingModules T R ⥤ proEtaleRingModules U S :=
    SheafOfModules.pushforward (F := proEtaleOpenComposition j)
      (J := ProEt.topology U) (K := ProEt.topology T)
      (R := (sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R) rc.hom
  let h : SheafOfModules.OpenTensorNormalization.restrict .ordinary j R ⋙
      E.functor ≅ F := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
      exact PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by intros; rfl)
    · intro M N a
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro W
      rfl
  let a := (E.symm.toAdjunction.comp e.adjunction).ofNatIsoRight h
  let i := a.leftAdjointUniq adj
  exact ⟨((ar.comp E.toAdjunction).ofNatIsoLeft h).ofNatIsoRight i⟩

end AlgebraicGeometry.Scheme
