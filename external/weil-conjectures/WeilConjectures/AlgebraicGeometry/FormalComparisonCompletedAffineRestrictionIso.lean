/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Limits

import WeilConjectures.AlgebraicGeometry.FormalComparisonCompletedAffineAdjunctionModel
import WeilConjectures.AlgebraicGeometry.TensorPullbackUnitRestrictionIso
import WeilConjectures.AlgebraicGeometry.CompletedAffineCoherentIsoLift
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # The completed affine comparison is invertible off the exceptional ideal

Source: Stacks Project, Tag 088B, proof, completed-base adjunction argument.
(blueprint: lem-weil-pbc-formal-comparison-completed-affine-restriction-iso)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A coherent realization of the canonical comparison is invertible off the
extended exceptional ideal. Unlike the model theorem, this supplies no objects,
map, or limit isomorphisms: all are inputs and the commuting square is a hypothesis.
Source: Stacks Project, Tag 088B, proof from the flat completed-base change through
invertibility of the algebraized adjunction off V(K).
(blueprint: lem-weil-pbc-formal-comparison-completed-affine-restriction-iso)

Proof: First reduce to the standard tensor adjunction: uniqueness of adjunctions
for the same functors relates the supplied unit to the standard unit by a natural
automorphism of tensor pullback. Absorb that automorphism in β, which stays an
isomorphism and gives the same hα equation for the standard unit.
Restrict the data to U=Spec B, and base change along B to its J(U)-adic
completion R. This map is flat and its positive ideal-power quotients agree with
those of B. Flat base change identifies pushforwards, quotient maps and adjunction
units. The quotient equation determines κ since its quotient projections are epi;
formal functions makes its inverse-limit map invertible, so the adjunction equation
determines the limit of α. Over R, algebraize the pulled-back formal source using
087W. Tensor pullback commutes with completion, and the fully faithful completion
functor on the proper source lifts β and its inverse to mutually inverse coherent
maps b and b inverse. The canonical comparison is therefore the completion of the
adjunction unit followed by pushforward of b. It is invertible off the extended
K-support because f is an isomorphism there. The displayed square identifies c
with that coherent map up to coherent isomorphisms: finite R-modules are complete
for J(U)R, and B-linear maps between them are R-linear by continuity (they preserve
J(U)^n and the B-image is dense modulo these powers). Indeed, J(U)^nR times a
module equals J(U)^n times its underlying B-module, by the finite generators of
J(U)^n. Thus eA,eD transport the
canonical realization to the supplied A,D. Quasi-coherent modules on Spec R are
fully faithfully recovered from sections, so this conjugacy holds as sheaf maps.
Restriction preserves conjugacy, proving IsIso of the restriction of c. If R=0
all modules vanish, so the conclusion still holds.
-/
theorem formalComparison_completed_affine_restriction_isIso
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (J K : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (hV : IsIso (pullback.snd f (Scheme.Opens.ι K.support.compl)))
    (adj : Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f)
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback f ≅
      formalCompletionSystem (J.comap f) F.obj)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
      formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f)
    (α : G ⟶ (completion Y J).obj ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩)
    (hκ : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
        κ.app (op n) =
      (Scheme.Modules.pushforward f).map
        (formalModuleQuotientπ (J.comap f) (n + 1) F.obj))
    (hα : ∀ n : ℕ, α.hom.app (op n) ≫ κ.app (op n) =
      adj.unit.app (G.obj.obj (op n)) ≫
        (Scheme.Modules.pushforward f).map (β.hom.app (op n))) :
    ∀ U : Y.affineOpens,
      let B := Γ(Y, U.1)
      let R := AdicCompletion (J.ideal U) B
      let L := (K.ideal U).map (algebraMap B R)
      let Q := Scheme.IdealSheafData.ofIdealTop
        (L.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      ∀ (A D : CoherentModules (Spec (CommRingCat.of R))) (c : A.obj ⟶ D.obj),
        ∀ eA : limit (G.obj ⋙ SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) ≅
            (ModuleCat.restrictScalars (algebraMap B R)).obj
              ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj A.obj),
        ∀ eD : limit (((completion Y J).obj
            ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩).obj ⋙
              SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) ≅
            (ModuleCat.restrictScalars (algebraMap B R)).obj
              ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj D.obj),
          (lim.map (Functor.whiskerRight α.hom
            (SheafOfModules.evaluation Y.ringCatSheaf (op U.1))) ≫ eD.hom =
          eA.hom ≫ (ModuleCat.restrictScalars (algebraMap B R)).map
            ((moduleSpecΓFunctor (R := CommRingCat.of R)).map c)) →
          IsIso ((Scheme.Modules.restrictFunctor
            (Scheme.Opens.ι Q.support.compl)).map c) := by
  intro U B R L Q A D c eA eD hs
  classical
  have : IsNoetherianRing B := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing R := AdicCompletion.isNoetherianRing (J.ideal U)
  obtain ⟨Z, p, adjR, A₀, F₀, b, hD, _, hp, eA₀, eD₀, hs₀⟩ :=
    formalComparison_completed_affine_adjunction_model
      J K f hV adj G F β h κ α hκ hα U
  let D₀ : CoherentModules (Spec (CommRingCat.of R)) :=
    ⟨(Scheme.Modules.pushforward p).obj F₀.obj, hD⟩
  let c₀ : A₀.obj ⟶ D₀.obj :=
    adjR.unit.app A₀.obj ≫ (Scheme.Modules.pushforward p).map b.hom
  let S := ModuleCat.restrictScalars (algebraMap B R)
  let T := moduleSpecΓFunctor (R := CommRingCat.of R)
  let V := Scheme.Modules.restrictFunctor (Scheme.Opens.ι Q.support.compl)
  have hu := Scheme.Modules.tensorPullback_unit_restriction_isIso
    p Q.support.compl hp adjR A₀.obj
  have hc₀ : IsIso (V.map c₀) := by
    dsimp only [c₀]
    rw [V.map_comp]
    infer_instance
  obtain ⟨a, ha⟩ := completedAffine_coherent_iso_lift B (J.ideal U) A A₀
    (eA.symm ≪≫ eA₀)
  obtain ⟨d, hd⟩ := completedAffine_coherent_iso_lift B (J.ideal U) D D₀
    (eD.symm ≪≫ eD₀)
  change S.map (T.map a.hom) = eA.inv ≫ eA₀.hom at ha
  change S.map (T.map d.hom) = eD.inv ≫ eD₀.hom at hd
  change _ ≫ eD.hom = eA.hom ≫ S.map (T.map c) at hs
  change _ ≫ eD₀.hom = eA₀.hom ≫ S.map (T.map c₀) at hs₀
  have hsections : T.map (c ≫ d.hom) = T.map (a.hom ≫ c₀) := by
    apply S.map_injective
    simp only [Functor.map_comp, ha, hd]
    apply (cancel_epi eA.hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← hs]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact hs₀
  have : A.obj.IsQuasicoherent :=
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mp A.property |>.1
  have : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) A.obj) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := CommRingCat.of R) A.obj
  have hconj : c ≫ d.hom = a.hom ≫ c₀ := by
    apply (cancel_epi (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) A.obj)).1
    have h₁ := (tilde.adjunction (R := CommRingCat.of R)).counit.naturality
      (c ≫ d.hom)
    have h₂ := (tilde.adjunction (R := CommRingCat.of R)).counit.naturality
      (a.hom ≫ c₀)
    change (tilde.functor (CommRingCat.of R)).map (T.map (c ≫ d.hom)) ≫
        (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) D₀.obj) =
      (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) A.obj) ≫ (c ≫ d.hom) at h₁
    rw [hsections] at h₁
    exact h₁.symm.trans h₂
  have hrestricted : V.map c ≫ V.map d.hom = V.map a.hom ≫ V.map c₀ := by
    simpa only [Functor.map_comp] using congrArg V.map hconj
  have : IsIso (V.map c ≫ V.map d.hom) := by
    rw [hrestricted]
    infer_instance
  exact IsIso.of_isIso_comp_right (V.map c) (V.map d.hom)

end AlgebraicGeometry
