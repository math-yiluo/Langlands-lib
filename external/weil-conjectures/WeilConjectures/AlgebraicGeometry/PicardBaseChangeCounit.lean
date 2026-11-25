/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardCanonicalBaseChange
import WeilConjectures.AlgebraicGeometry.PicardTensorSquareConjugacy
import WeilConjectures.AlgebraicGeometry.PicardBaseChangeFactorization

/-! # Counit formula for the canonical Picard base-change map

Source: Stacks Project, Tags 0095, 0096, 08HY and 0BDP.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

private noncomputable abbrev tensorAdj {A B : Scheme.{u}} (k : A ⟶ B) :=
  Classical.choose (exists_tensorPullbackAdjunction k)

private noncomputable def rightSquare {X S T X' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ T) (g : T ⟶ S) (v : X' ⟶ X)
    (e : v ≫ f = f' ≫ g) :
    TwoSquare (pushforward v) (pushforward f') (pushforward f) (pushforward g) :=
  TwoSquare.mk _ _ _ _
    ((pushforwardComp v f).hom ≫ (pushforwardCongr e).hom ≫ (pushforwardComp f' g).inv)

private noncomputable def baseSquare {X S T X' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ T) (g : T ⟶ S) (v : X' ⟶ X)
    (e : v ≫ f = f' ≫ g) :
    TwoSquare (pushforward f) (tensorPullback v) (tensorPullback g) (pushforward f') :=
  (mateEquiv (tensorAdj v) (tensorAdj g)).symm (rightSquare f f' g v e)

private theorem baseSquare_app {X S T X' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ T) (g : T ⟶ S) (v : X' ⟶ X)
    (e : v ≫ f = f' ≫ g) (F : X.Modules) :
    (baseSquare f f' g v e).app F = moduleBaseChangeMap f f' g v e F := by
  apply ((tensorAdj g).homEquiv _ _).injective
  dsimp only [tensorAdj, Functor.comp_obj]
  rw [moduleBaseChangeMap, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm (tensorAdj v) (tensorAdj g)
    (rightSquare f f' g v e) F).symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem square_counit {X S T X' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ T) (g : T ⟶ S) (v : X' ⟶ X)
    (e : v ≫ f = f' ≫ g) (F : X.Modules) :
    (tensorPullback f').map (moduleBaseChangeMap f f' g v e F) ≫
      (tensorAdj f').counit.app ((tensorPullback v).obj F) =
    (picardTensorCompIso f' g ((pushforward f).obj F) ≪≫
      eqToIso (congrArg (fun k ↦ (tensorPullback k).obj ((pushforward f).obj F)) e.symm) ≪≫
      (picardTensorCompIso v f ((pushforward f).obj F)).symm).hom ≫
      (tensorPullback v).map ((tensorAdj f).counit.app F) := by
  have he : ((mateEquiv (tensorAdj f) (tensorAdj f')).symm
      (baseSquare f f' g v e)).app ((pushforward f).obj F) =
      ((conjugateEquiv ((tensorAdj f).comp (tensorAdj v))
        ((tensorAdj g).comp (tensorAdj f'))).symm
        (rightSquare f f' g v e)).app ((pushforward f).obj F) := by
    rw [baseSquare, iterated_mateEquiv_conjugateEquiv_symm]
  have hc' := mateEquiv_counit_symm (tensorAdj f) (tensorAdj f')
    (baseSquare f f' g v e) F
  rw [baseSquare_app, he] at hc'
  have ht := picardTensorSquareConjugacy f f' g v e ((pushforward f).obj F)
  exact hc'.trans (congrArg
    (fun a ↦ a ≫ (tensorPullback v).map ((tensorAdj f).counit.app F)) ht)

private theorem baseChange_postcompose_counit {X S T X' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ T) (g : T ⟶ S) (v : X' ⟶ X)
    (e : v ≫ f = f' ≫ g) (F : X.Modules) (G : X'.Modules)
    (D : (tensorPullback v).obj F ⟶ G) :
    (tensorPullback f').map
        (moduleBaseChangeMap f f' g v e F ≫ (pushforward f').map D) ≫
      (tensorAdj f').counit.app G =
    ((tensorPullback f').map (moduleBaseChangeMap f f' g v e F) ≫
      (tensorAdj f').counit.app ((tensorPullback v).obj F)) ≫ D := by
  have hn : (tensorPullback f').map ((pushforward f').map D) ≫
      (tensorAdj f').counit.app G =
      (tensorAdj f').counit.app ((tensorPullback v).obj F) ≫ D :=
    (tensorAdj f').counit.naturality D
  rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc]

/-- The square comparison from the bottom composite pullback to the top composite.
Source: Stacks Project, Tags 0095 and 0096, composition of module pullbacks.
(blueprint: lem-sc-picard-base-change-counit) -/
noncomputable def picardBaseChangeSquareIso
    {X S W T : Scheme.{u}} (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W) (A : W.Modules) :
    (tensorPullback (Limits.pullback.snd f (h ≫ j))).obj ((tensorPullback h).obj A) ≅
      (tensorPullback (picardBaseChangeTop f j h)).obj
        ((tensorPullback (Limits.pullback.snd f j)).obj A) :=
  picardTensorCompIso (Limits.pullback.snd f (h ≫ j)) h A ≪≫
    eqToIso (congrArg (fun k ↦ (tensorPullback k).obj A)
      (by dsimp [picardBaseChangeTop]; rw [Limits.pullback.lift_snd])) ≪≫
    (picardTensorCompIso (picardBaseChangeTop f j h) (Limits.pullback.snd f j) A).symm

/-- Identify the iterated top pullback of a coefficient with its pullback to X_T.
Source: Stacks Project, Tags 0095 and 0096, composition of module pullbacks.
(blueprint: lem-sc-picard-base-change-counit) -/
noncomputable def picardBaseChangeCoefficientIso
    {X S W T : Scheme.{u}} (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W) (M : X.Modules) :
    (tensorPullback (picardBaseChangeTop f j h)).obj
        ((tensorPullback (Limits.pullback.fst f j)).obj M) ≅
      (tensorPullback (Limits.pullback.fst f (h ≫ j))).obj M :=
  picardTensorCompIso (picardBaseChangeTop f j h) (Limits.pullback.fst f j) M ≪≫
    eqToIso (congrArg (fun k ↦ (tensorPullback k).obj M)
      (by dsimp [picardBaseChangeTop]; rw [Limits.pullback.lift_fst]))

/-- The adjoint of the canonical base-change map for one coefficient.
Source: Stacks Project, Tag 08HY, mate description; Tags 0095 and 0096,
composition comparisons. (blueprint: lem-sc-picard-base-change-counit)

Proof: Express the map as the mate of the pushforward square, as in its definition.
Take its transpose along p_T. Naturality of the top unit and the bottom counit,
and the two adjunction triangle identities, give the square pullback comparison
followed by the pullback of the p_W counit. To identify the comparison, transport
all four tensor pullbacks to ordinary pullbacks by leftAdjointUniq. Its unit and
counit equations identify the transported mate with the ordinary pullback square;
ordinary pullback composition is conjugate to sectionwise pushforward composition.
Transport back to obtain picardBaseChangeSquareIso. Finally naturality of the
p_T counit moves the coefficient comparison out of the pushed-forward factor,
giving the final coefficient isomorphism. This argument is for an arbitrary
module M and involves no evaluation, tensor pairing, or invertibility of the
base-change map; it applies also to zero modules and empty schemes. -/
theorem picardDirectImageBaseChangeMap_counit
    {X S W T : Scheme.{u}} (f : X ⟶ S) (j : W ⟶ S) (h : T ⟶ W) (M : X.Modules) :
    (tensorPullback (Limits.pullback.snd f (h ≫ j))).map
        (picardDirectImageBaseChangeMap f j h M) ≫
      (Classical.choose (exists_tensorPullbackAdjunction
        (Limits.pullback.snd f (h ≫ j)))).counit.app
          ((tensorPullback (Limits.pullback.fst f (h ≫ j))).obj M) =
    (picardBaseChangeSquareIso f j h
      ((pushforward (Limits.pullback.snd f j)).obj
        ((tensorPullback (Limits.pullback.fst f j)).obj M))).hom ≫
      (tensorPullback (picardBaseChangeTop f j h)).map
        ((Classical.choose (exists_tensorPullbackAdjunction
          (Limits.pullback.snd f j))).counit.app
            ((tensorPullback (Limits.pullback.fst f j)).obj M)) ≫
      (picardBaseChangeCoefficientIso f j h M).hom := by
  let v := picardBaseChangeTop f j h
  have e : v ≫ Limits.pullback.snd f j = Limits.pullback.snd f (h ≫ j) ≫ h := by
    dsimp [v, picardBaseChangeTop]
    rw [Limits.pullback.lift_snd]
  have hs := square_counit (Limits.pullback.snd f j)
    (Limits.pullback.snd f (h ≫ j)) h v e
    ((tensorPullback (Limits.pullback.fst f j)).obj M)
  have hb := baseChange_postcompose_counit (Limits.pullback.snd f j)
    (Limits.pullback.snd f (h ≫ j)) h v e
    ((tensorPullback (Limits.pullback.fst f j)).obj M)
    ((tensorPullback (Limits.pullback.fst f (h ≫ j))).obj M)
    (picardBaseChangeCoefficientIso f j h M).hom
  rw [hs] at hb
  rw [Category.assoc] at hb
  convert hb using 1
  · have hi : picardBaseChangeCoefficientIso f j h M =
        (picardTensorCompIso v (Limits.pullback.fst f j) M ≪≫
          eqToIso (congrArg (fun k ↦ (tensorPullback k).obj M)
            (show v ≫ Limits.pullback.fst f j = Limits.pullback.fst f (h ≫ j) from by
              dsimp [v, picardBaseChangeTop]
              rw [Limits.pullback.lift_fst]))) := by
      unfold picardBaseChangeCoefficientIso
      rfl
    have hf := picardDirectImageBaseChangeMap_factorization f j h M
      (picardBaseChangeCoefficientIso f j h M) hi
    exact congrArg (fun β ↦ (tensorPullback (Limits.pullback.snd f (h ≫ j))).map β ≫
      (tensorAdj (Limits.pullback.snd f (h ≫ j))).counit.app
        ((tensorPullback (Limits.pullback.fst f (h ≫ j))).obj M)) hf
  · let A := (pushforward (Limits.pullback.snd f j)).obj
      ((tensorPullback (Limits.pullback.fst f j)).obj M)
    have hi : picardBaseChangeSquareIso f j h A =
        (picardTensorCompIso (Limits.pullback.snd f (h ≫ j)) h A ≪≫
          eqToIso (congrArg (fun k ↦ (tensorPullback k).obj A) e.symm) ≪≫
          (picardTensorCompIso v (Limits.pullback.snd f j) A).symm) := by
      unfold picardBaseChangeSquareIso
      rfl
    exact congrArg (fun c : (tensorPullback (Limits.pullback.snd f (h ≫ j))).obj
        ((tensorPullback h).obj A) ≅
        (tensorPullback v).obj ((tensorPullback (Limits.pullback.snd f j)).obj A) ↦
      c.hom ≫ (tensorPullback v).map
      ((tensorAdj (Limits.pullback.snd f j)).counit.app
        ((tensorPullback (Limits.pullback.fst f j)).obj M)) ≫
      (picardBaseChangeCoefficientIso f j h M).hom) hi

end AlgebraicGeometry.Scheme.Modules
