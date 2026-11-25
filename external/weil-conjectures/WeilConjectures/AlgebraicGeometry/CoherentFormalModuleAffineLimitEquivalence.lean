/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAffineSpecTransport
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffine
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Affine section comparisons for coherent formal modules

Source: Stacks Project, Lemmas 087W and 087X.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The finite completed-module equivalence with natural local section cones.
Source: Stacks Project, Lemma 087W and the affine reduction in Lemma 087X.
(blueprint: lem-weil-pbc-formal-affine-limit-equivalence)

Proof: Use the canonical isomorphism V ≅ Spec A, where A = Γ(X,V).
The inverse isomorphism sends I|V to the ideal sheaf associated with J=I(V):
on top sections its ring map is V.topIso.hom followed by ΓSpecIso.inv.
Pull coherent formal modules back termwise along the isomorphism. Pullback
composition and identity comparisons give the unit and counit, lifted through the
fully faithful system inclusions. Compose this transport equivalence with the
finite completed-module equivalence of Lemma 087W. Its limiting cones transport
back to the top sections on V, with scalars restricted along V.topIso.inv.
The section comparisons are linear because pullback along an isomorphism and
ΓSpecIso intertwine the scalar actions. Transport of limiting cones preserves
universality. Naturality of the original projections and of these comparisons
gives the displayed equation for each map and each level. This works also for
an empty open or for zero or unit ideals: no properness of J is used.
-/
theorem coherentFormalModule_affine_limit_equivalence
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData) (V : X.affineOpens)
    [IsNoetherian V.1.toScheme] :
    ∃ E : CoherentFormalModule V.1.toScheme (I.comap V.1.ι) ≌
      ObjectProperty.FullSubcategory
        (fun N : ModuleCat.{u} (AdicCompletion (I.ideal V) Γ(X, V.1)) ↦
          Module.Finite (AdicCompletion (I.ideal V) Γ(X, V.1)) N),
    ∃ p : ∀ F : CoherentFormalModule V.1.toScheme (I.comap V.1.ι),
      (Functor.const ℕᵒᵖ).obj
        ((ModuleCat.restrictScalars
          (algebraMap Γ(X, V.1) (AdicCompletion (I.ideal V) Γ(X, V.1)))).obj
            (E.functor.obj F).obj) ⟶
      F.obj ⋙ (SheafOfModules.evaluation V.1.toScheme.ringCatSheaf (op ⊤) ⋙
        ModuleCat.restrictScalars V.1.topIso.inv.hom),
    (∀ F, Nonempty (IsLimit (Cone.mk _ (p F)))) ∧
    (∀ (F G : CoherentFormalModule V.1.toScheme (I.comap V.1.ι))
      (f : F ⟶ G) (n : ℕ),
      (ModuleCat.restrictScalars
        (algebraMap Γ(X, V.1) (AdicCompletion (I.ideal V) Γ(X, V.1)))).map
          (E.functor.map f).hom ≫ (p G).app (op n) =
      (p F).app (op n) ≫
        (SheafOfModules.evaluation V.1.toScheme.ringCatSheaf (op ⊤) ⋙
        ModuleCat.restrictScalars V.1.topIso.inv.hom).map (f.hom.app (op n))) := by
  classical
  let : IsNoetherianRing Γ(X, V.1) :=
    IsLocallyNoetherian.component_noetherian V
  obtain ⟨T, ⟨d⟩⟩ := coherentFormalModule_affine_spec_transport X I V
  obtain ⟨E, p, hl, hn, _⟩ := coherentFormalModules_affine Γ(X, V.1) (I.ideal V)
    (Scheme.IdealSheafData.ofIdealTop
      ((I.ideal V).map (Scheme.ΓSpecIso (CommRingCat.of Γ(X, V.1))).inv.hom)) rfl
  refine ⟨T.trans E, (fun F ↦ p (T.functor.obj F) ≫ (d.app F).inv), ?_, ?_⟩
  · intro F
    exact ⟨(IsLimit.postcomposeInvEquiv (d.app F)
      (Cone.mk _ (p (T.functor.obj F)))).symm (hl (T.functor.obj F)).some⟩
  · intro F G f n
    change (ModuleCat.restrictScalars
      (algebraMap Γ(X, V.1) (AdicCompletion (I.ideal V) Γ(X, V.1)))).map
        (E.functor.map (T.functor.map f)).hom ≫
          ((p (T.functor.obj G)).app (op n) ≫ (d.inv.app G).app (op n)) =
      ((p (T.functor.obj F)).app (op n) ≫ (d.inv.app F).app (op n)) ≫ _
    have h := congrArg (fun a ↦ a.app (op n)) (d.inv.naturality f)
    change moduleSpecΓFunctor.map ((T.functor.map f).hom.app (op n)) ≫
        (d.inv.app G).app (op n) = (d.inv.app F).app (op n) ≫
          (SheafOfModules.evaluation V.1.toScheme.ringCatSheaf (op ⊤) ⋙
            ModuleCat.restrictScalars V.1.topIso.inv.hom).map (f.hom.app (op n)) at h
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (d.inv.app G).app (op n))
        (hn (T.functor.obj F) (T.functor.obj G) (T.functor.map f) n)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg ((p (T.functor.obj F)).app (op n) ≫ ·) h).trans
            (Category.assoc _ _ _).symm)))

end AlgebraicGeometry
