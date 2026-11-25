/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalFunctionsFinitePullback
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import WeilConjectures.AlgebraicGeometry.FormalFunctionsFiniteOpenUnitPasting
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-! # Finite pullback on the inverse-image opens

Source: Stacks Project, Tag 02OD, factorization through the local spectrum;
Tags 01F7 and 01FB, composition and restriction of cohomology maps.
(blueprint: lem-weil-pbc-formal-functions-finite-open-factorization)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.moduleCohomologyFMap

private theorem cohomology_congr {A B : Scheme.{u}} {h k : A ⟶ B}
    (e : h = k) {G : B.Modules} {F : A.Modules}
    (φ : G ⟶ (Scheme.Modules.pushforward h).obj F) (p : ℕ) :
    Scheme.Modules.moduleCohomologyFMap h φ p =
      Scheme.Modules.moduleCohomologyFMap k
        (φ ≫ (Scheme.Modules.pushforwardCongr e).hom.app F) p := by
  subst k
  have hc : (Scheme.Modules.pushforwardCongr (rfl : h = h)).hom.app F = 𝟙 _ := by
    ext U
    simp
  rw [hc]
  exact congrArg (fun a ↦ Scheme.Modules.moduleCohomologyFMap h a p) (Category.comp_id φ).symm

private theorem cohomology_comp_congr {A B C : Scheme.{u}}
    (h : A ⟶ B) (k : B ⟶ C) (j : A ⟶ C) (hj : h ≫ k = j)
    {G : C.Modules} {H : B.Modules} {F : A.Modules}
    (ψ : G ⟶ (Scheme.Modules.pushforward k).obj H)
    (φ : H ⟶ (Scheme.Modules.pushforward h).obj F)
    (χ : G ⟶ (Scheme.Modules.pushforward j).obj F)
    (hc : ψ ≫ (Scheme.Modules.pushforward k).map φ ≫
      (Scheme.Modules.pushforwardComp h k).hom.app F ≫
      (Scheme.Modules.pushforwardCongr hj).hom.app F = χ) (p : ℕ) :
    Scheme.Modules.moduleCohomologyFMap k ψ p ≫
      Scheme.Modules.moduleCohomologyFMap h φ p =
        Scheme.Modules.moduleCohomologyFMap j χ p := by
  have hh := Scheme.Modules.moduleCohomologyFMap_comp h k ψ φ p
  have ht := cohomology_congr hj
    (G := G) (F := F)
    (ψ ≫ (Scheme.Modules.pushforward k).map φ ≫
      (Scheme.Modules.pushforwardComp h k).hom.app F) p
  have hc' : (ψ ≫ (Scheme.Modules.pushforward k).map φ ≫
      (Scheme.Modules.pushforwardComp h k).hom.app F) ≫
      (Scheme.Modules.pushforwardCongr hj).hom.app F = χ := by
    simpa only [Category.assoc] using hc
  exact hh.symm.trans (ht.trans
    (congrArg (fun a ↦ Scheme.Modules.moduleCohomologyFMap j (G := G) (F := F) a p) hc'))


private theorem restriction_data {A B : Scheme.{u}} (h : A ⟶ B)
    {G : B.Modules} {F : A.Modules}
    (φ : G ⟶ (Scheme.Modules.pushforward h).obj F)
    (U : B.Opens) (W : A.Opens) (he : W = h ⁻¹ᵁ U) (hle : W ≤ h ⁻¹ᵁ U) :
    ∃ φU : (Scheme.Modules.restrictFunctor U.ι).obj G ⟶
      (Scheme.Modules.pushforward (h.resLE U W hle)).obj
        ((Scheme.Modules.restrictFunctor W.ι).obj F),
      (Scheme.Modules.restrictAdjunction U.ι).unit.app G ≫
        (Scheme.Modules.pushforward U.ι).map φU ≫
        (Scheme.Modules.pushforwardComp (h.resLE U W hle) U.ι).hom.app
          ((Scheme.Modules.restrictFunctor W.ι).obj F) ≫
        (Scheme.Modules.pushforwardCongr (h.resLE_comp_ι hle)).hom.app
          ((Scheme.Modules.restrictFunctor W.ι).obj F) =
      φ ≫ (Scheme.Modules.pushforward h).map
        ((Scheme.Modules.restrictAdjunction W.ι).unit.app F) ≫
        (Scheme.Modules.pushforwardComp W.ι h).hom.app
          ((Scheme.Modules.restrictFunctor W.ι).obj F) ∧
      ∀ p : ℕ, Scheme.Modules.moduleCohomologyFMap h φ p ≫
        Scheme.Modules.moduleCohomologyRestriction W F p =
      Scheme.Modules.moduleCohomologyRestriction U G p ≫
        Scheme.Modules.moduleCohomologyFMap (h.resLE U W hle) φU p := by
  subst W
  exact Scheme.Modules.moduleCohomologyFMap_restriction h φ U

/-- A single additive map on open cohomology intertwines global finite pullback
with restriction and the two restricted pullbacks. No germ or stalk comparison
occurs in this statement.
Source: Stacks Project, Tag 02OD, the finite maps factor through the local spectrum;
Tags 01F7 and 01FB, functoriality of cohomology.
(blueprint: lem-weil-pbc-formal-functions-finite-open-factorization)

Proof: write g' for the projection from the local base change to X and i' for
formalFunctionsFiniteι. Put U=f inverse V, U'=g' inverse U and W=i_n inverse U.
The projection identity i' followed by g'=i_n gives W=i' inverse U'. Restrict the
h-map formalFunctionsFiniteFMap to U' using moduleCohomologyFMap_restriction.
Transport its target along the equality of opens, using the canonical restricted
module identification, and take its cohomology map as t. The restriction square
in that theorem gives the first equality for every global class z.
For the second equality, transpose the defining formalFunctionsFiniteFMap across
its tensor-pullback adjunction. Its image is the i_n unit with the pushforward
composition and equality identifications. Restrict this equation to W. Substitute
E.unit_square and D.unit_square. Naturality of pushforwardComp and pushforwardCongr
identifies the composite of E.psi with the restricted finite h-map with D.psi:
both transpose under restriction to the same restricted i_n unit. Applying
moduleCohomologyFMap_comp and its congruence for the projection identity yields
the second equality. Arbitrary resolution choices affect neither equality, since
these h-maps are fixed by their unit squares. The construction applies to every
open V, even one not containing y, and to arbitrary F: no flatness, properness,
coherence, Noetherianity, surjectivity, or completion comparison is required.
At p=0 these are ordinary section pullbacks; for zero coefficients or empty opens
all maps are zero. The intermediate map is used only to prove a proposition. -/
theorem formalFunctions_finite_open_factorization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (F : X.Modules) (p n : ℕ) (I : InjectiveResolution F)
    (K : InjectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))
    (J : InjectiveResolution ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F))
    (V : Y.Opens)
    (E : Scheme.Modules.FlatBaseChangeOpenChoices f (Y.fromSpecStalk y) F I K V)
    (D : Scheme.Modules.FlatBaseChangeOpenChoices f (formalFibreBaseMap Y y n) F I J V) :
    ∃ t : (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.moduleCohomology
          ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.toRingedSpace p).obj
          ((Scheme.Modules.restrictFunctor
            ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).obj
            ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))) →+
      (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.moduleCohomology
          ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.toRingedSpace p).obj
          ((Scheme.Modules.restrictFunctor ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).obj
            ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F))),
      (∀ z : formalFunctionsLocalCohomology f y F p,
        t (Scheme.Modules.moduleCohomologyRestriction
          ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V))
          ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F) p z) =
        Scheme.Modules.moduleCohomologyRestriction ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V))
          ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F) p
          (formalFunctionsFinitePullback f y F p n z)) ∧
      (∀ xi : (forget₂ _ AddCommGrpCat.{u}).obj
          ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)),
        t (Scheme.Modules.moduleCohomologyFMap
          ((pullback.snd (Y.fromSpecStalk y) f).resLE (f ⁻¹ᵁ V)
            ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) E.psi p xi) =
        Scheme.Modules.moduleCohomologyFMap ((formalFibreι f y n).resLE (f ⁻¹ᵁ V)
          ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) D.psi p xi) := by
  let g := pullback.snd (Y.fromSpecStalk y) f
  let j := formalFunctionsFiniteι f y n
  let i := formalFibreι f y n
  let U := f ⁻¹ᵁ V
  let U' := g ⁻¹ᵁ U
  let W := i ⁻¹ᵁ U
  let F' := (Scheme.Modules.tensorPullback g).obj F
  let Fₙ := (Scheme.Modules.tensorPullback i).obj F
  have hw : W = j ⁻¹ᵁ U' := by
    change i ⁻¹ᵁ U = j ⁻¹ᵁ (g ⁻¹ᵁ U)
    exact (congrArg (fun a : formalFibre f y n ⟶ X ↦ a ⁻¹ᵁ U)
      (formalFunctionsFiniteι_snd f y n)).symm.trans (j.comp_preimage g U)
  have hle : W ≤ j ⁻¹ᵁ U' := hw.le
  let r := j.resLE U' W hle
  let s := g.resLE U U' le_rfl
  let q := i.resLE U W le_rfl
  have hrs : r ≫ s = q := by
    apply (cancel_mono U.ι).1
    calc
      (r ≫ s) ≫ U.ι = W.ι ≫ (j ≫ g) := by
        rw [Category.assoc, g.resLE_comp_ι, ← Category.assoc,
          j.resLE_comp_ι, Category.assoc]
      _ = W.ι ≫ i := congrArg (fun a : formalFibre f y n ⟶ X ↦ W.ι ≫ a)
        (formalFunctionsFiniteι_snd f y n)
      _ = q ≫ U.ι := (i.resLE_comp_ι le_rfl).symm
  have hres := restriction_data j (G := F') (F := Fₙ)
    (formalFunctionsFiniteFMap f y F n) U' W hw hle
  rcases hres with ⟨τ, hτ, hc⟩
  refine ⟨(Scheme.Modules.moduleCohomologyFMap r τ p).hom, ?_, ?_⟩
  · intro z
    exact (congrArg (fun a ↦ a.hom z) (hc p)).symm
  · have hs : E.psi ≫ (Scheme.Modules.pushforward s).map τ ≫
        (Scheme.Modules.pushforwardComp r s).hom.app
          ((Scheme.Modules.restrictFunctor W.ι).obj Fₙ) ≫
        (Scheme.Modules.pushforwardCongr hrs).hom.app
          ((Scheme.Modules.restrictFunctor W.ι).obj Fₙ) = D.psi :=
      formalFunctions_finite_open_unit_pasting f y F n I K J V E D hle hrs τ hτ
    have hh := cohomology_comp_congr r s q hrs
      (G := (Scheme.Modules.restrictFunctor U.ι).obj F)
      (H := (Scheme.Modules.restrictFunctor U'.ι).obj F')
      (F := (Scheme.Modules.restrictFunctor W.ι).obj Fₙ) E.psi τ D.psi hs p
    intro xi
    exact congrArg (fun a ↦ a.hom xi) hh

end AlgebraicGeometry
