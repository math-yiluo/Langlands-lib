/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Basic

import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffine
import all WeilConjectures.AlgebraicGeometry.FormalSystemsPullback
import WeilConjectures.AlgebraicGeometry.FormalCompletionFullyFaithfulProper
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Algebraizing a formal pullback isomorphism with quotient compatibility

Source: Stacks Project, Tag 088B, final complete-base paragraph; Tags 087W and 0883.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A formal pullback isomorphism over a complete affine base lifts to an algebraic
isomorphism, compatibly with the actual quotient projections.
Source: Stacks Project, Tag 088B, final complete-base paragraph; Tags 087W and 0883.
(blueprint: lem-weil-pbc-formal-comparison-algebraization-quotient-lift)

Proof: Tag 087W associates to G its finite module over the completion of A.
Since A is I-adically complete, restrict this module along the isomorphism
A -> its completion and take its tilde, a coherent module A0. The unit and inverse
comparison of the affine equivalence give e from G to the quotient system of A0. Pullback preserves
coherence on the Noetherian proper scheme and commutes with the quotient system;
the comparison is specified by the images of the quotient projections. Compose
it with the pullback of e.inv and beta. Tag 0883 lifts this isomorphism
and its inverse uniquely to maps between p* A0 and F. Injectivity on Hom makes
the lifted composites identities. The resulting isomorphism b has exactly the
displayed projection equation, since the quotient comparison sends the projection
to the pullback of the projection. The zero ring causes no exception: all these
categories and maps are zero. -/
theorem formalComparison_algebraization_quotient_lift
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    {Z : Scheme.{u}} (p : Z ⟶ Spec (CommRingCat.of A)) [IsProper p]
    (G : CoherentFormalModule (Spec (CommRingCat.of A)) J) (F : CoherentModules Z)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback p ≅
      formalCompletionSystem (J.comap p) F.obj) :
    ∃ (A₀ : CoherentModules (Spec (CommRingCat.of A)))
      (e : G.obj ≅ formalCompletionSystem J A₀.obj)
      (b : (Scheme.Modules.tensorPullback p).obj A₀.obj ≅ F.obj),
      ∀ n : ℕ,
        (Scheme.Modules.tensorPullback p).map (formalModuleQuotientπ J (n + 1) A₀.obj) ≫
          (Scheme.Modules.tensorPullback p).map (e.inv.app (op n)) ≫ β.hom.app (op n) =
        b.hom ≫ formalModuleQuotientπ (J.comap p) (n + 1) F.obj := by
  classical
  let S := Spec (CommRingCat.of A)
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType p
  obtain ⟨E, _, _, _, _, _, ⟨ε⟩⟩ := coherentFormalModules_affine A I J hJ
  let N := (E.functor.obj G).obj
  let M := (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj N
  let H := (tilde.functor (CommRingCat.of A)).obj M
  have : Module.Finite A (AdicCompletion I A) :=
    Module.Finite.equiv (AdicCompletion.ofLinearEquiv I A)
  let : Module (AdicCompletion I A) M := N.isModule
  have : IsScalarTower A (AdicCompletion I A) M :=
    IsScalarTower.of_algebraMap_smul (fun a x ↦
      (ModuleCat.restrictScalars.smul_def (algebraMap A (AdicCompletion I A)) a x).symm)
  have : Module.Finite (AdicCompletion I A) M := (E.functor.obj G).property
  have : Module.Finite A M := Module.Finite.trans (AdicCompletion I A) M
  have : H.IsQuasicoherent := inferInstanceAs ((tilde (R := CommRingCat.of A) M).IsQuasicoherent)
  have hfinite : Module.Finite A
      ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj H) :=
    Module.Finite.equiv ((tilde.isoTop (R := CommRingCat.of A) M).toLinearEquiv)
  let : Module A Γ(H, ⊤) := inferInstanceAs
    (Module A ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj H))
  let : Algebra A Γ(S, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toAlgebra
  have : IsScalarTower A Γ(S, ⊤) Γ(H, ⊤) :=
    IsScalarTower.of_algebraMap_smul (fun a x ↦ (Scheme.Modules.smul_top_eq H a x).symm)
  have : Module.Finite A Γ(H, ⊤) := hfinite
  have : Module.Finite Γ(S, ⊤) Γ(H, ⊤) := Module.Finite.of_restrictScalars_finite A _ _
  have : H.IsFiniteType :=
    ((Scheme.Modules.quasicoherent_finite_type_affine S).2 H inferInstance).2.1
      PUnit.{u + 1} (fun _ ↦ ⊤) (by simp) (fun _ ↦ isAffineOpen_top _)
      (fun _ ↦ inferInstance) |>.1
  let A₀ : CoherentModules S := ⟨H,
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType S H).mpr
      ⟨inferInstance, inferInstance⟩⟩
  let e : G.obj ≅ formalCompletionSystem J A₀.obj :=
    (ObjectProperty.ι (IsCoherentFormalModule J)).mapIso (E.unitIso.app G) ≪≫
      ε.app (E.functor.obj G)
  let H₀ : CoherentModules Z := ⟨(Scheme.Modules.tensorPullback p).obj A₀.obj,
    coherent_pullback p A₀.obj A₀.property⟩
  let q : formalCompletionSystem (J.comap p) H₀.obj ≅
      formalCompletionSystem (J.comap p) F.obj :=
    (completionPullbackIso p J).app A₀ ≪≫
      Functor.isoWhiskerRight e.symm (Scheme.Modules.tensorPullback p) ≪≫ β
  let C := completion Z (J.comap p)
  have hC (U V : CoherentModules Z) : Function.Bijective
      (fun v : U ⟶ V ↦ C.map v) := by
    dsimp only [C]
    rw [hJ]
    exact formalCompletion_map_bijective_of_proper I p U V
  have : C.Full := ⟨fun {H K} ↦ (hC H K).surjective⟩
  have : C.Faithful := ⟨fun {H K} ↦ (hC H K).injective⟩
  let q₀ : C.obj H₀ ≅ C.obj F := ObjectProperty.isoMk (IsCoherentFormalModule (J.comap p)) q
  let b₀ := C.preimageIso q₀
  let b : (Scheme.Modules.tensorPullback p).obj A₀.obj ≅ F.obj :=
    (ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace)).mapIso b₀
  refine ⟨A₀, e, b, ?_⟩
  intro n
  have hb : (formalCompletionMap (J.comap p) b.hom).app (op n) = q.hom.app (op n) := by
    have hh := C.map_preimage q₀.hom
    exact congrArg (fun f ↦ f.hom.app (op n)) hh
  have hπ : formalModuleQuotientπ (J.comap p) (n + 1) H₀.obj ≫
      q.hom.app (op n) = b.hom ≫ formalModuleQuotientπ (J.comap p) (n + 1) F.obj := by
    rw [← hb]
    exact cokernel.π_desc _ _ _
  dsimp only [q, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom] at hπ
  change formalModuleQuotientπ (J.comap p) (n + 1)
      ((Scheme.Modules.tensorPullback p).obj A₀.obj) ≫
        (powerQuotientIso p J A₀.obj
          ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mp
            A₀.property).1 (n + 1)).hom ≫
        (Scheme.Modules.tensorPullback p).map (e.inv.app (op n)) ≫
        β.hom.app (op n) = _ at hπ
  rw [← Category.assoc, ← Category.assoc, powerQuotientIso_π] at hπ
  simpa only [Category.assoc] using hπ

end
end AlgebraicGeometry
