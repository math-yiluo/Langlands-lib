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
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Category.ModuleCat.Limits

import WeilConjectures.AlgebraicGeometry.FormalComparisonCompletedAffineData
import WeilConjectures.AlgebraicGeometry.FormalSystemCompletedAffineSections
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Flat transport of the comparison to the completed affine base

Source: Stacks Project, Tag 088B, restriction, flat base-change and uniqueness paragraphs.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem limit_square_restrict
    {B R : Type u} [CommRing B] [CommRing R] (r : B →+* R)
    (A C : ℕᵒᵖ ⥤ ModuleCat.{u} B) (A₀ C₀ : ℕᵒᵖ ⥤ ModuleCat.{u} R)
    (a : A ⟶ C) (b : A₀ ⟶ C₀)
    (iA : A ≅ A₀ ⋙ ModuleCat.restrictScalars r)
    (iC : C ≅ C₀ ⋙ ModuleCat.restrictScalars r)
    (hi : a ≫ iC.hom = iA.hom ≫ Functor.whiskerRight b (ModuleCat.restrictScalars r)) :
    ∃ eA : limit A ≅ (ModuleCat.restrictScalars r).obj (limit A₀),
    ∃ eC : limit C ≅ (ModuleCat.restrictScalars r).obj (limit C₀),
      lim.map a ≫ eC.hom = eA.hom ≫ (ModuleCat.restrictScalars r).map (lim.map b) := by
  let L := ModuleCat.restrictScalars.{u} r
  let eA := lim.mapIso iA ≪≫ (preservesLimitIso L A₀).symm
  let eC := lim.mapIso iC ≪≫ (preservesLimitIso L C₀).symm
  refine ⟨eA, eC, ?_⟩
  apply (cancel_mono (preservesLimitIso L C₀).hom).1
  simp only [eA, eC, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := (preservesLimitNatIso L).hom.naturality b
  change L.map (lim.map b) ≫ (preservesLimitIso L C₀).hom =
    (preservesLimitIso L A₀).hom ≫ lim.map (Functor.whiskerRight b L) at hn
  rw [hn]
  simp only [Iso.inv_hom_id_assoc]
  rw [← lim.map_comp, ← lim.map_comp, hi]

-- The comparison composes four diagram functors and dependent pullback equalities.
set_option backward.isDefEq.respectTransparency false in
/-- Restriction and flat completion base change transport the formal comparison and
its section inverse limit. This step neither algebraizes the source nor lifts beta.

Source: Stacks Project, Tag 088B, paragraphs introducing the completed base Y' and X';
Tags 02KH, 087W, 02OC and 05GG.
(blueprint: lem-weil-pbc-formal-comparison-completed-affine-transport)

Proof: Let g be Spec of the completion map followed by the inverse affine chart and
its open inclusion. Set Z = X times_Y Spec R, q its projection to X, and p its
projection to Spec R. Pull G termwise along g and pull F along q. Formal-system
pullback gives coherence and the quotient transition laws and identifies completion
with pulled-back completion. Its composition comparison transports beta to beta0.
Completion is flat, so degree-zero flat base change identifies p_* F0 with g* f_* F
and identifies the pushforward of every quotient with its pulled-back pushforward.
Transport kappa and alpha through these identifications. The quotient projection
identity gives hKappa0 by naturality of base change. The adjunction square gives
hAlpha0. If the supplied adjunction differs from the chosen adjunction after base
change, compose beta0 with the natural pullback automorphism relating their units;
this preserves invertibility and makes this square exact.
On U, coherent formal terms are annihilated by J(U)^(n+1). Completion has the same
positive-power quotients as B, so their section modules identify with the restrictions
of the R-section modules of the transported terms, naturally in transitions and maps.
These level identifications give eG and eD on limits. Naturality for alpha at each
level, followed by the universal property of the two limits, gives the last square.
The object equalities record the actual pullbacks, rather than arbitrary formal or
coherent objects. The argument also works when the completion is zero or J is zero.
-/
theorem formalComparison_completed_affine_transport
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
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
        (Scheme.Modules.pushforward f).map (β.hom.app (op n)))
    (U : Y.affineOpens)
    [IsNoetherianRing (AdicCompletion (J.ideal U) Γ(Y, U.1))] :
    let B := Γ(Y, U.1)
    let R := AdicCompletion (J.ideal U) B
    let S := Spec (CommRingCat.of R)
    let I := (J.ideal U).map (algebraMap B R)
    let J₀ := Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    let g : S ⟶ Y := Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫
      U.2.isoSpec.inv ≫ U.1.ι
    let Z := pullback f g
    let p : Z ⟶ S := pullback.snd f g
    ∃ (adjR : Scheme.Modules.tensorPullback p ⊣ Scheme.Modules.pushforward p)
      (G₀ : CoherentFormalModule S J₀) (F₀ : CoherentModules Z)
      (β₀ : G₀.obj ⋙ Scheme.Modules.tensorPullback p ≅
        formalCompletionSystem (J₀.comap p) F₀.obj)
      (hD : RingedSpace.IsCoherent S.toRingedSpace
        ((Scheme.Modules.pushforward p).obj F₀.obj))
      (κ₀ : formalCompletionSystem J₀ ((Scheme.Modules.pushforward p).obj F₀.obj) ⟶
        formalCompletionSystem (J₀.comap p) F₀.obj ⋙ Scheme.Modules.pushforward p)
      (α₀ : G₀ ⟶ (completion S J₀).obj
        ⟨(Scheme.Modules.pushforward p).obj F₀.obj, hD⟩),
      G₀.obj = G.obj ⋙ Scheme.Modules.tensorPullback g ∧
      F₀.obj = (Scheme.Modules.tensorPullback (pullback.fst f g)).obj F.obj ∧
      (∀ n : ℕ, formalModuleQuotientπ J₀ (n + 1)
          ((Scheme.Modules.pushforward p).obj F₀.obj) ≫ κ₀.app (op n) =
        (Scheme.Modules.pushforward p).map
          (formalModuleQuotientπ (J₀.comap p) (n + 1) F₀.obj)) ∧
      (∀ n : ℕ, α₀.hom.app (op n) ≫ κ₀.app (op n) =
        adjR.unit.app (G₀.obj.obj (op n)) ≫
          (Scheme.Modules.pushforward p).map (β₀.hom.app (op n))) ∧
      ∃ eG : limit (G.obj ⋙ SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) ≅
        (ModuleCat.restrictScalars (algebraMap B R)).obj
          (limit (G₀.obj ⋙ moduleSpecΓFunctor (R := CommRingCat.of R))),
      ∃ eD : limit (((completion Y J).obj
          ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩).obj ⋙
            SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) ≅
        (ModuleCat.restrictScalars (algebraMap B R)).obj
          (limit (((completion S J₀).obj
            ⟨(Scheme.Modules.pushforward p).obj F₀.obj, hD⟩).obj ⋙
              moduleSpecΓFunctor (R := CommRingCat.of R))),
        lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation Y.ringCatSheaf (op U.1))) ≫ eD.hom =
        eG.hom ≫ (ModuleCat.restrictScalars (algebraMap B R)).map
          (lim.map (Functor.whiskerRight α₀.hom
            (moduleSpecΓFunctor (R := CommRingCat.of R)))) := by
  classical
  dsimp only
  let B := Γ(Y, U.1)
  let R := AdicCompletion (J.ideal U) B
  let S := Spec (CommRingCat.of R)
  let I := (J.ideal U).map (algebraMap B R)
  let J₀ := Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  let g : S ⟶ Y := Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫
    U.2.isoSpec.inv ≫ U.1.ι
  let p := pullback.snd f g
  let T := Scheme.Modules.tensorPullback g
  let E := moduleSpecΓFunctor (R := CommRingCat.of R)
  let L := ModuleCat.restrictScalars.{u} (algebraMap B R)
  let D := (completion Y J).obj ⟨(Scheme.Modules.pushforward f).obj F.obj, h⟩
  have hd := formalComparison_completed_affine_data J f adj G F β h κ α hκ hα U
  dsimp only at hd
  obtain ⟨adjR, G₀, F₀, β₀, hD, κ₀, α₀, hG, hF, hκ₀, hα₀, δ, hδ⟩ := hd
  let D₀ := (completion S J₀).obj ⟨(Scheme.Modules.pushforward p).obj F₀.obj, hD⟩
  have hs := formalSystem_completed_affine_sections J U
  dsimp only at hs
  obtain ⟨e, he⟩ := hs
  let tG := Functor.isoWhiskerRight (eqToIso hG) E
  let tD := Functor.isoWhiskerRight δ E
  let iG := e G ≪≫ (Functor.isoWhiskerRight tG L).symm
  let iD := e D ≪≫ (Functor.isoWhiskerRight tD L).symm
  have ht : Functor.whiskerRight (Functor.whiskerRight α₀.hom E) L ≫
        (Functor.isoWhiskerRight tD L).hom =
      (Functor.isoWhiskerRight tG L).hom ≫ Functor.whiskerRight
        (Functor.whiskerRight (Functor.whiskerRight α.hom T) E) L := by
    simpa only [Functor.whiskerRight_comp, tD, tG, Functor.isoWhiskerRight_hom,
      eqToIso.hom] using
      congrArg (fun a ↦ Functor.whiskerRight (Functor.whiskerRight a E) L) hδ
  have hi : Functor.whiskerRight α.hom
        (SheafOfModules.evaluation Y.ringCatSheaf (op U.1)) ≫ iD.hom =
      iG.hom ≫ Functor.whiskerRight (Functor.whiskerRight α₀.hom E) L := by
    apply (cancel_mono (Functor.isoWhiskerRight tD L).hom).1
    simp only [iD, iG, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    rw [ht]
    simp only [Iso.inv_hom_id_assoc]
    exact he G D α
  have hl := limit_square_restrict (algebraMap B R)
    _ _ (G₀.obj ⋙ E) (D₀.obj ⋙ E)
    (Functor.whiskerRight α.hom (SheafOfModules.evaluation Y.ringCatSheaf (op U.1)))
    (Functor.whiskerRight α₀.hom E) iG iD hi
  dsimp only at hl
  obtain ⟨eG, eD, heGD⟩ := hl
  exact ⟨adjR, G₀, F₀, β₀, hD, κ₀, α₀, hG, hF, hκ₀, hα₀, eG, eD, heGD⟩

end AlgebraicGeometry
