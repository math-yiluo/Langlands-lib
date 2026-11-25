/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeOpenSquareIso
import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeSquareRestrictionCommutes
import WeilConjectures.AlgebraicGeometry.TensorPullback

/-!
# Module base change maps and open restriction

Source: Stacks Project, Tags 02KG, 0ATL, 0ATM, 00A0 and 08HY
(blueprint: lem-weil-pbc-module-base-change-map-open-restriction).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false

/-- The module base change map is adjoint to the pushforward of the pullback unit,
using the sectionwise identification of composite pushforwards.
Source: Stacks Project, Tag 08HY
(blueprint: lem-weil-pbc-module-base-change-map-open-restriction). -/
def moduleBaseChangeMap {X S T X₁ : Scheme.{u}}
    (f : X ⟶ S) (f₁ : X₁ ⟶ T) (u₁ : T ⟶ S) (v : X₁ ⟶ X)
    (h : v ≫ f = f₁ ≫ u₁) (F : X.Modules) :
    (tensorPullback u₁).obj ((pushforward f).obj F) ⟶
      (pushforward f₁).obj ((tensorPullback v).obj F) :=
  ((Classical.choose (exists_tensorPullbackAdjunction u₁)).homEquiv _ _).symm
    ((pushforward f).map
      ((Classical.choose (exists_tensorPullbackAdjunction v)).unit.app F) ≫
      (pushforwardComp v f).hom.app ((tensorPullback v).obj F) ≫
      (pushforwardCongr h).hom.app ((tensorPullback v).obj F) ≫
      (pushforwardComp f₁ u₁).inv.app ((tensorPullback v).obj F))

/-- Naturality of the adjoint-defined base change map.
Source: Stacks Project, Tag 08HY
(blueprint: lem-weil-pbc-module-base-change-map-open-restriction).
Proof: the unit is natural in F; pushforward and the sectionwise composition
identifications preserve that equality. Naturality of the adjunction Hom bijection
then gives the displayed equality. This is the naturality clause preceding step (1). -/
theorem moduleBaseChangeMap_naturality {X S T X₁ : Scheme.{u}}
    (f : X ⟶ S) (f₁ : X₁ ⟶ T) (u₁ : T ⟶ S) (v : X₁ ⟶ X)
    (h : v ≫ f = f₁ ≫ u₁) {F G : X.Modules} (φ : F ⟶ G) :
    (tensorPullback u₁).map ((pushforward f).map φ) ≫ moduleBaseChangeMap f f₁ u₁ v h G =
      moduleBaseChangeMap f f₁ u₁ v h F ≫
        (pushforward f₁).map ((tensorPullback v).map φ) := by
  unfold moduleBaseChangeMap
  apply (Classical.choose (exists_tensorPullbackAdjunction u₁)).homEquiv_naturality_right_square
  let e := Classical.choose (exists_tensorPullbackAdjunction v)
  let t : pushforward f ⟶ tensorPullback v ⋙ pushforward v ⋙ pushforward f :=
    Functor.whiskerRight e.unit (pushforward f)
  let q : pushforward v ⋙ pushforward f ⟶ pushforward f₁ ⋙ pushforward u₁ :=
    (pushforwardComp v f).hom ≫ (pushforwardCongr h).hom ≫ (pushforwardComp f₁ u₁).inv
  exact (t ≫ Functor.whiskerLeft (tensorPullback v) q).naturality φ

/-- Base change maps commute with restriction to open squares with full inverse-image
opens, and the restriction maps are isomorphisms.
Source: Stacks Project, Tags 02KG (locality), 00A0 (restriction), 0ATL and 0ATM (pasting)
(blueprint: lem-weil-pbc-module-base-change-map-open-restriction).
Proof:
(1) By lem-weil-pbc-module-restriction-open-immersion-colimits and
lem-weil-pbc-open-immersion-module-pullback-restriction, open-immersion pullback is
sectionwise restriction and its unit restricts sections. The full inverse-image
hypotheses identify the opens computing both sides of rho and rho', so these maps
are isomorphisms (00A0).
(2) Paste the original square with the primed open square. By
lem-weil-pbc-module-base-change-map-pasting (0ATM), its outer map is jV^* beta followed
by b, including the canonical pullback composition comparisons.
(3) Paste the unprimed open square with the restricted square. The same pasting lemma
(0ATL, 0ATM) gives a followed by beta-circle. The commutation relations identify the
outer squares, hence their adjoint-defined maps agree.
(4) The comparisons a and b are composites of pullback composition isomorphisms,
pullbacks of rho, and rho'. They are isomorphisms, and cancellation in (3) gives the
isomorphism criterion. No affine or quasi-coherence hypothesis is needed. -/
theorem moduleBaseChangeMap_open_restriction
    {X S X' S' U V XU X'V : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (jU : U ⟶ S) (jV : V ⟶ S') (jX : XU ⟶ X) (jX' : X'V ⟶ X')
    [IsOpenImmersion jU] [IsOpenImmersion jV]
    [IsOpenImmersion jX] [IsOpenImmersion jX']
    (fU : XU ⟶ U) (fV' : X'V ⟶ V) (gV : V ⟶ U) (gV' : X'V ⟶ XU)
    (hf : jX ≫ f = fU ≫ jU) (hf' : jX' ≫ f' = fV' ≫ jV)
    (hg : jV ≫ g = gV ≫ jU) (hg' : jX' ≫ g' = gV' ≫ jX)
    (hV : gV' ≫ fU = fV' ≫ gV)
    (hX : Set.range jX = f ⁻¹' Set.range jU)
    (hX' : Set.range jX' = f' ⁻¹' Set.range jV) :
    let adj : ∀ {A B : Scheme.{u}} (k : A ⟶ B), tensorPullback k ⊣ pushforward k :=
      fun {A B : Scheme.{u}} (k : A ⟶ B) ↦
      Classical.choose (exists_tensorPullbackAdjunction k)
    let c : ∀ {A B C : Scheme.{u}} (k : A ⟶ B) (l : B ⟶ C),
        tensorPullback (k ≫ l) ≅ tensorPullback l ⋙ tensorPullback k :=
      fun {A B C : Scheme.{u}} (k : A ⟶ B) (l : B ⟶ C) ↦
      (conjugateIsoEquiv ((adj l).comp (adj k)) (adj (k ≫ l))).symm
        (pushforwardComp k l)
    let rho := fun F : X.Modules ↦ moduleBaseChangeMap f fU jU jX hf F
    let rho' := fun G : X'.Modules ↦ moduleBaseChangeMap f' fV' jV jX' hf' G
    (∀ F : X.Modules, IsIso (rho F)) ∧
    (∀ G : X'.Modules, IsIso (rho' G)) ∧
    ∀ F : X.Modules,
      let a := (c jV g).inv.app ((pushforward f).obj F) ≫
        (eqToIso (congrArg (fun k ↦ (tensorPullback k).obj ((pushforward f).obj F)) hg)).hom ≫
        (c gV jU).hom.app ((pushforward f).obj F) ≫ (tensorPullback gV).map (rho F)
      let b := rho' ((tensorPullback g').obj F) ≫
        (pushforward fV').map ((c jX' g').inv.app F) ≫
        (pushforward fV').map
          (eqToIso (congrArg (fun k ↦ (tensorPullback k).obj F) hg')).hom ≫
        (pushforward fV').map ((c gV' jX).hom.app F)
      let beta := moduleBaseChangeMap f f' g g' h F
      let betaV := moduleBaseChangeMap fU fV' gV gV' hV ((tensorPullback jX).obj F)
      IsIso a ∧ IsIso b ∧
        (tensorPullback jV).map beta ≫ b = a ≫ betaV ∧
        (IsIso ((tensorPullback jV).map beta) ↔ IsIso betaV) := by
  intro adj c rho rho'
  have hr : ∀ F : X.Modules, IsIso (rho F) := fun F ↦
    moduleBaseChangeMap_open_square_isIso f fU jU jX hf hX F
  have hr' : ∀ G : X'.Modules, IsIso (rho' G) := fun G ↦
    moduleBaseChangeMap_open_square_isIso f' fV' jV jX' hf' hX' G
  refine ⟨hr, hr', ?_⟩
  intro F a b beta betaV
  have : IsIso (rho F) := hr F
  have : IsIso (rho' ((tensorPullback g').obj F)) := hr' _
  have ha : IsIso a := by dsimp only [a]; infer_instance
  have hb : IsIso b := by dsimp only [b]; infer_instance
  have hc : (tensorPullback jV).map beta ≫ b = a ≫ betaV :=
    moduleBaseChangeMap_square_restriction_commutes f f' g g' h
      jU jV jX jX' fU fV' gV gV' hf hf' hg hg' hV F
  refine ⟨ha, hb, hc, ?_⟩
  rw [← isIso_comp_right_iff ((tensorPullback jV).map beta) b, hc,
    isIso_comp_left_iff a betaV]


end
end AlgebraicGeometry.Scheme.Modules
