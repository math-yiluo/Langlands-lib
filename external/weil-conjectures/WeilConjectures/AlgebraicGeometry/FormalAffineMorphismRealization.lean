/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Limits

import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAffineLimitModel
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Realization of affine formal morphisms over the completed base

Source: Stacks Project, Tag 087W (affine equivalence), Tag 01XZ (finite modules).
(blueprint: lem-weil-pbc-formal-affine-morphism-realization)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Every formal morphism has a coherent realization over the completed affine base.
Source: Stacks Project, Tags 087W and 01XZ.
(blueprint: lem-weil-pbc-formal-affine-morphism-realization)

Proof: Restrict both formal systems to the affine open U, identifying U with Spec B
by its canonical affine isomorphism. Restriction commutes with ideal quotients, so
these remain coherent formal systems for J(U). Apply the affine formal-module
equivalence (087W) to obtain finite R-modules N and M and an R-linear map v. Its
natural affine-limit model identifies the two original evaluated limits, as B-modules, with
N and M restricted along B to R. The ring R is Noetherian. Associate to N,M their
tilde modules on Spec R. Finite presentations of N,M give finite presentations of
these sheaves via presentationTilde, hence quasi-coherence and finite type. They are
coherent by 01XZ and their sections recover N,M.
Compose the limit isomorphisms with these section isomorphisms. Naturality of both
the limit-cone comparison and tilde's unit identifies the limit map of α with
sections of tilde(v), giving the square. Empty affine opens and J(U)=B give the zero
ring R and zero modules, so the same construction covers these cases.
-/
theorem formal_affine_morphism_realization
    {Y : Scheme.{u}} [IsNoetherian Y] (J : Y.IdealSheafData)
    (G H : CoherentFormalModule Y J) (α : G ⟶ H) :
    ∀ U : Y.affineOpens,
      let B := Γ(Y, U.1)
      let R := AdicCompletion (J.ideal U) B
      ∃ (A D : CoherentModules (Spec (CommRingCat.of R))) (c : A.obj ⟶ D.obj),
        ∃ eA : limit (G.obj ⋙ SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) ≅
            (ModuleCat.restrictScalars (algebraMap B R)).obj
              ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj A.obj),
        ∃ eD : limit (H.obj ⋙
              SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) ≅
            (ModuleCat.restrictScalars (algebraMap B R)).obj
              ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj D.obj),
          lim.map (Functor.whiskerRight α.hom
            (SheafOfModules.evaluation Y.ringCatSheaf (op U.1))) ≫ eD.hom =
          eA.hom ≫ (ModuleCat.restrictScalars (algebraMap B R)).map
            ((moduleSpecΓFunctor (R := CommRingCat.of R)).map c) := by
  intro U
  classical
  let B := Γ(Y, U.1)
  let R := AdicCompletion (J.ideal U) B
  have : IsNoetherian U.1.toScheme := {}
  have : IsNoetherianRing B := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing R := AdicCompletion.isNoetherianRing (J.ideal U)
  obtain ⟨E, ⟨e⟩⟩ := coherentFormalModule_affine_limit_model Y J U
  let T := coherentFormalModulesRestriction J U.1 ⋙ E.functor
  let N := (T.obj G).obj
  let M := (T.obj H).obj
  let v : N ⟶ M := (T.map α).hom
  have hcoh (P : ModuleCat.{u} R) (hP : Module.Finite R P) :
      RingedSpace.IsCoherent (Spec (CommRingCat.of R)).toRingedSpace
        ((tilde.functor (CommRingCat.of R)).obj P) := by
    have : Module.Finite R P := hP
    have hp := Module.finitePresentation_of_finite R P
    obtain ⟨s, hs, t, ht⟩ := hp.out
    let pres := presentationTilde (R := CommRingCat.of R) P (s : Set P) hs (t : Set _) ht
    have : pres.IsFinite :=
      { isFiniteType_generators := ⟨inferInstanceAs (Finite (s : Set P))⟩
        isFiniteType_relations := ⟨inferInstanceAs (Finite (t : Set (s →₀ R)))⟩ }
    have : ((tilde.functor (CommRingCat.of R)).obj P).IsFinitePresentation :=
      pres.isFinitePresentation
    exact (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mpr
      ⟨inferInstance, inferInstance⟩
  let A : CoherentModules (Spec (CommRingCat.of R)) :=
    ⟨(tilde.functor (CommRingCat.of R)).obj N, hcoh N (T.obj G).property⟩
  let D : CoherentModules (Spec (CommRingCat.of R)) :=
    ⟨(tilde.functor (CommRingCat.of R)).obj M, hcoh M (T.obj H).property⟩
  let S := ModuleCat.restrictScalars (algebraMap B R)
  let uN := (tilde.toTildeΓNatIso (R := CommRingCat.of R)).app N
  let uM := (tilde.toTildeΓNatIso (R := CommRingCat.of R)).app M
  refine ⟨A, D, (tilde.functor (CommRingCat.of R)).map v,
    e.app G ≪≫ S.mapIso uN, e.app H ≪≫ S.mapIso uM, ?_⟩
  have he := e.hom.naturality α
  have hu := (tilde.toTildeΓNatIso (R := CommRingCat.of R)).hom.naturality v
  change lim.map (Functor.whiskerRight α.hom
      (SheafOfModules.evaluation Y.ringCatSheaf (op U.1))) ≫
    ((e.app H).hom ≫ S.map uM.hom) =
    ((e.app G).hom ≫ S.map uN.hom) ≫
      S.map ((moduleSpecΓFunctor (R := CommRingCat.of R)).map
        ((tilde.functor (CommRingCat.of R)).map v))
  change lim.map (Functor.whiskerRight α.hom
      (SheafOfModules.evaluation Y.ringCatSheaf (op U.1))) ≫ (e.app H).hom =
    (e.app G).hom ≫ S.map v at he
  change v ≫ uM.hom = uN.hom ≫
    (moduleSpecΓFunctor (R := CommRingCat.of R)).map
      ((tilde.functor (CommRingCat.of R)).map v) at hu
  rw [← Category.assoc, he, Category.assoc, ← S.map_comp, hu, S.map_comp,
    Category.assoc]

end AlgebraicGeometry
