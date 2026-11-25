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

public import Mathlib.AlgebraicGeometry.Morphisms.Flat

import WeilConjectures.AlgebraicGeometry.FormalCompletionPullbackNormalized
import WeilConjectures.AlgebraicGeometry.OrdinaryFlatExchangePrescribedAdjunction
import WeilConjectures.AlgebraicGeometry.FormalSystemExchangeMateCompatibility
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Ordinary flat quotient comparisons and adjunction mates

Source: Stacks Project, Tags 088B, 0887, 02KH and 02N7.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem exchange_projection
    {C D E A : Type*} [Category C] [Category D] [Category E] [Category A]
    (P : C ⥤ D) (T : D ⥤ E) (U : C ⥤ A) (Q : A ⥤ E)
    (B : P ⋙ T ⟶ U ⋙ Q) {M N : C} {M₀ N₀ : A}
    (hM : M₀ = U.obj M) (π : M ⟶ N) (π₀ : M₀ ⟶ N₀)
    (e : U.obj N ≅ N₀) [IsIso (B.app M)]
    (he : U.map π ≫ e.hom = eqToHom hM.symm ≫ π₀) :
    (Q.map (eqToHom hM) ≫ inv (B.app M)) ≫ T.map (P.map π) ≫
      (B.app N ≫ Q.map e.hom) = Q.map π₀ := by
  have hn := B.naturality π
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← Category.assoc (T.map (P.map π)) (B.app N), hn]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rw [← Q.map_comp, he, Q.map_comp]
  rw [← Category.assoc, ← Q.map_comp]
  simp

/-- Flat base change transports an algebraization isomorphism and its adjunction mate,
and its termwise comparison respects the quotient projections before completion of
pushforward. No completed pushforward or comparison map kappa is involved.
Source: Stacks Project, Tags 088B (completed-base-change paragraph), 0887 and 02KH;
Tag 02N7 for the adjunction mate of the base-change map.
(blueprint: lem-weil-pbc-formal-flat-quotient-mate-data)

Proof: Write q and p for the projections. Choose the tensor-pullback adjunction on p.
The composition comparisons identify g* followed by p* with f* followed by q*;
compare the supplied adjunction on f with the chosen tensor adjunction and absorb
its invertible left-adjoint comparison in this composition isomorphism. Pull beta
through this comparison and the completion-pullback isomorphism for F to obtain
beta zero. The degree-zero flat base-change mate b_M:g*f_*M -> p_*q*M is natural
in M and invertible on quasi-coherent M by 02KH. For F, use its inverse and the
supplied equality F zero = q*F to define b:D -> g*H. Termwise b on the quotients
of F, followed by the inverse completion-pullback comparison, defines t. Naturality
of b at each quotient projection, and the projection normalization of completion
pullback, prove the first displayed equation. The mate identity for b, naturality
at beta, and the adjusted composition comparison prove the second equation.
Naturality of the comparisons makes beta zero and t maps of whole inverse systems.
All constructions use cokernels and adjunctions and also apply to empty schemes,
zero modules, zero ideals and unit ideals; no faithful completion is used. -/
theorem formal_flat_quotient_mate_data
    {X Y S : Scheme.{u}} [IsNoetherian Y] [IsNoetherian S]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f] (g : S ⟶ Y) [Flat g]
    (I : S.IdealSheafData) (hI : J.comap g = I)
    (adj : Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f)
    (G : CoherentFormalModule Y J) (F : CoherentModules X)
    (β : G.obj ⋙ Scheme.Modules.tensorPullback f ≅
      formalCompletionSystem (J.comap f) F.obj)
    (G₀ : CoherentFormalModule S I) (F₀ : CoherentModules (pullback f g))
    (hG : G₀.obj = G.obj ⋙ Scheme.Modules.tensorPullback g)
    (hF : F₀.obj = (Scheme.Modules.tensorPullback (pullback.fst f g)).obj F.obj) :
    let p := pullback.snd f g
    ∃ (adjR : Scheme.Modules.tensorPullback p ⊣ Scheme.Modules.pushforward p)
      (β₀ : G₀.obj ⋙ Scheme.Modules.tensorPullback p ≅
        formalCompletionSystem (I.comap p) F₀.obj)
      (b : (Scheme.Modules.pushforward p).obj F₀.obj ≅
        (Scheme.Modules.tensorPullback g).obj ((Scheme.Modules.pushforward f).obj F.obj))
      (t : (formalCompletionSystem (J.comap f) F.obj ⋙
          Scheme.Modules.pushforward f) ⋙ Scheme.Modules.tensorPullback g ⟶
        formalCompletionSystem (I.comap p) F₀.obj ⋙ Scheme.Modules.pushforward p),
      (∀ n : ℕ, b.hom ≫ (Scheme.Modules.tensorPullback g).map
          ((Scheme.Modules.pushforward f).map
            (formalModuleQuotientπ (J.comap f) (n + 1) F.obj)) ≫ t.app (op n) =
        (Scheme.Modules.pushforward p).map
          (formalModuleQuotientπ (I.comap p) (n + 1) F₀.obj)) ∧
      (∀ n : ℕ, (eqToHom hG).app (op n) ≫
          (Scheme.Modules.tensorPullback g).map
            (adj.unit.app (G.obj.obj (op n)) ≫
              (Scheme.Modules.pushforward f).map (β.hom.app (op n))) ≫ t.app (op n) =
        adjR.unit.app (G₀.obj.obj (op n)) ≫
          (Scheme.Modules.pushforward p).map (β₀.hom.app (op n))) := by
  classical
  subst I
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  let adjR := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))
  let c : Scheme.Modules.tensorPullback g ⋙ Scheme.Modules.tensorPullback (pullback.snd f g) ≅
      Scheme.Modules.tensorPullback f ⋙ Scheme.Modules.tensorPullback (pullback.fst f g) :=
    (conjugateIsoEquiv
      (adj.comp (Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.fst f g))))
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp adjR)).symm
        (Scheme.Modules.pushforwardComp (pullback.fst f g) f ≪≫
          Scheme.Modules.pushforwardCongr pullback.condition ≪≫
          (Scheme.Modules.pushforwardComp (pullback.snd f g) g).symm)
  let B : Scheme.Modules.pushforward f ⋙ Scheme.Modules.tensorPullback g ⟶
      Scheme.Modules.tensorPullback (pullback.fst f g) ⋙
        Scheme.Modules.pushforward (pullback.snd f g) :=
    { app := fun M ↦ Scheme.Modules.moduleBaseChangeMap f (pullback.snd f g) g
        (pullback.fst f g) pullback.condition M
      naturality := fun _ _ a ↦
        Scheme.Modules.moduleBaseChangeMap_naturality f (pullback.snd f g) g
          (pullback.fst f g) pullback.condition a }
  have hB (M : X.Modules) (hM : M.IsQuasicoherent) : IsIso (B.app M) :=
    (ordinary_flat_exchange_prescribed_adjunction f g adj).1 M hM
  have hmate (N : Y.Modules) :
      (Scheme.Modules.tensorPullback g).map (adj.unit.app N) ≫
        B.app ((Scheme.Modules.tensorPullback f).obj N) =
      adjR.unit.app ((Scheme.Modules.tensorPullback g).obj N) ≫
        (Scheme.Modules.pushforward (pullback.snd f g)).map (c.hom.app N) :=
    (ordinary_flat_exchange_prescribed_adjunction f g adj).2 N
  have hJ : (J.comap f).comap (pullback.fst f g) = (J.comap g).comap (pullback.snd f g) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
    exact congrArg J.comap pullback.condition
  obtain ⟨e, he⟩ := exists_formalCompletionPullback_normalized
    (pullback.fst f g) (J.comap f) F ((J.comap g).comap (pullback.snd f g)) hJ F₀.obj hF
  obtain ⟨β₀, t, ht, hunit⟩ := formal_system_exchange_mate_compatibility
    (Scheme.Modules.tensorPullback f) (Scheme.Modules.pushforward f)
    (Scheme.Modules.tensorPullback g) (Scheme.Modules.tensorPullback (pullback.fst f g))
    (Scheme.Modules.tensorPullback (pullback.snd f g))
    (Scheme.Modules.pushforward (pullback.snd f g)) adj adjR c B hmate
    G.obj G₀.obj hG (formalCompletionSystem (J.comap f) F.obj)
    (formalCompletionSystem ((J.comap g).comap (pullback.snd f g)) F₀.obj) β e
  have hFqc : F.obj.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mp F.property).1
  let : IsIso (B.app F.obj) := hB F.obj hFqc
  let b : (Scheme.Modules.pushforward (pullback.snd f g)).obj F₀.obj ≅
      (Scheme.Modules.tensorPullback g).obj ((Scheme.Modules.pushforward f).obj F.obj) :=
    (Scheme.Modules.pushforward (pullback.snd f g)).mapIso (eqToIso hF) ≪≫
      (asIso (B.app F.obj)).symm
  refine ⟨adjR, β₀, b, t, ?_, hunit⟩
  rw [ht]
  intro n
  exact exchange_projection (Scheme.Modules.pushforward f)
      (Scheme.Modules.tensorPullback g) (Scheme.Modules.tensorPullback (pullback.fst f g))
      (Scheme.Modules.pushforward (pullback.snd f g)) B
      (M := F.obj) (N := formalModuleQuotient (J.comap f) (n + 1) F.obj)
      (M₀ := F₀.obj)
      (N₀ := formalModuleQuotient ((J.comap g).comap (pullback.snd f g)) (n + 1) F₀.obj) hF
      (formalModuleQuotientπ (J.comap f) (n + 1) F.obj)
      (formalModuleQuotientπ ((J.comap g).comap (pullback.snd f g)) (n + 1) F₀.obj)
      (e.app (op n)) (he n)

end AlgebraicGeometry
