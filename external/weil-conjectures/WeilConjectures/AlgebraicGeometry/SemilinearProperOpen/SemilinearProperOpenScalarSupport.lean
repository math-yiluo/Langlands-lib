/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore

import Mathlib.Util.AliasIn
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarDerivedComparison
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarAdjunctions
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenArrows

/-! # Existing scalar constructions for semilinear proper/open mates

This part of the intrinsic coefficient API is separated to keep each file within
the compilation limit. The original constructions and their properties are retained.

## References

* Zheng 4.1
* Stacks 03CZ and 03D7
* Stacks 03EK
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option synthInstance.maxSize 32
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections
section ProofEnvironment
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf Functor.mapDerivedCategoryNatIso
  HasDerivedCategory.standard DerivedCategory.Q
  Functor.mapDerivedCategoryFactors
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
attribute [local irreducible] SemilinearSections.systemRing
  coefficientMap VaryingRing.ringMap alpha gamma

section ScalarRestriction
attribute [local implicit_reducible]
  VaryingRing.coefficientTransition VaryingRing.ordinaryScalarMap
  StrictTower.G StrictTower.R P R

variable (B : Type (u + 1)) [CommRing B]
  (φ : ∀ n : ℕ, B →+* C n)
  (hφ : ∀ n : ℕ, (τ n).hom.comp (φ (n + 1)) = φ n)

/-- The actual level scalar restriction along the supplied B -> C_n. -/
abbrev levelRestriction (X : Scheme.{u}) (n : ℕ) :=
  SemilinearSections.res.{u + 1, u, u + 1}
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom (φ n)))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Constructing the entire scalar-restriction functor requires sectionwise transports.
/-- Termwise scalar restriction to ordinary constant-B towers, uniquely characterized
on objects, transitions, and morphisms. -/
theorem rhoOrdinary_existsUnique (X : Scheme.{u})
    (compatible : ∀ n : ℕ, (τ n).hom.comp (φ (n + 1)) = φ n) :
    ∃! F : Modules C τ X ⥤ StrictTower.Towers B X,
      (∀ n : ℕ, F ⋙ (CategoryTheory.evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) =
        SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology X) (coefficients C X)
          (transition C τ X) n ⋙ levelRestriction C B φ X n) ∧
      (∀ (M : Modules C τ X) (n m : ℕ) (h : n ≤ m) (U : X.ProEt),
        HEq (fun x ↦ ((((F.obj M).map (homOfLE h).op).val.app (op U)) x))
          (fun x : M.val.obj (op (m, U)) ↦
            M.val.map (Prod.mkHom (homOfLE h) (𝟙 U)).op x)) := by
  apply ordinary_restriction_existsUnique (ProEt.topology X)
    (coefficients C X) (transition C τ X) (StrictTower.coefficients B X)
    (fun n ↦ (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (φ n)))
  intro n
  rw [← Functor.map_comp]
  exact congrArg ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map)
    (CommRingCat.hom_ext (compatible n))

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The unique ordinary restriction functor with the prescribed section formulas. -/
def rhoOrdinary (X : Scheme.{u}) :=
  (rhoOrdinary_existsUnique C τ B φ X hφ).choose
attribute [local irreducible] rhoOrdinary

set_option synthInstance.maxSize 64 in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem rho_section_type (X : Scheme.{u}) (M : Modules C τ X)
    (n : ℕ) (U : X.ProEt) :
    ((((rhoOrdinary C τ B φ hφ X).obj M).obj (op n)).val.obj (op U) : Type (u + 1)) =
      (M.val.obj (op (n, U)) : Type (u + 1))  := by
  have e : rhoOrdinary C τ B φ hφ X ⋙
      (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) =
      SemilinearSections.evaluation (ProEt.topology X) (coefficients C X)
        (transition C τ X) n ⋙ levelRestriction C B φ X n := by
    unfold rhoOrdinary
    exact (rhoOrdinary_existsUnique C τ B φ X hφ).choose_spec.1.1 n
  exact congrArg (fun N : StrictTower.Modules B X ↦ (N.val.obj (op U) : Type (u + 1)))
    (Functor.congr_obj e M)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem rho_transition (X : Scheme.{u}) (M : Modules C τ X)
    (n m : ℕ) (h : n ≤ m) (U : X.ProEt) :
    HEq (fun x ↦ ((((rhoOrdinary C τ B φ hφ X).obj M).map
      (homOfLE h).op).val.app (op U)) x)
      (fun x : M.val.obj (op (m, U)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 U)).op x) := by
  unfold rhoOrdinary
  exact (rhoOrdinary_existsUnique C τ B φ X hφ).choose_spec.1.2 M n m h U
section OrdinaryScalarProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem transition_transport
    {A B D E M N : Type u} (hD : D = M) (hE : E = N)
    (a : A → B) (b : B → E) (c : A → D) (d : D → E)
    (l : B → N) (m : A → M) (t : M → N)
    (hb : HEq b l) (hc : HEq c m) (hd : HEq d t)
    (ht : ∀ x, l (a x) = t (m x)) : ∀ x, b (a x) = d (c x) := by
  subst D E
  rw [eq_of_heq hb, eq_of_heq hc, eq_of_heq hd]
  exact ht

private theorem post_eq_sections
    {A B : Type*} [Category A] [Category B] {J : GrothendieckTopology B}
    {S : Sheaf J RingCat} {F G H : A ⥤ SheafOfModules.{u + 1} S}
    (e : F ≅ G) (h : G = H) (M : A) (U : Bᵒᵖ) :
    HEq (fun x ↦ ((e ≪≫ eqToIso h).hom.app M).val.app U x)
      (fun x ↦ (e.hom.app M).val.app U x) := by
  subst H
  rfl

private theorem normalized_inverse {A B : Type u} (f : A → B) (g : B → A)
    (h : ∀ x, f (g x) = x) (hf : ∀ x, HEq (f x) x) (x : B) : HEq (g x) x :=
  (hf (g x)).symm.trans (heq_of_eq (h x))
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem normalized_apply {A B D : Type u} (hA : A = D) (hB : B = D)
    (f : A → B) (hf : HEq f (fun x : D ↦ x)) (x : A) : HEq (f x) x := by
  subst A B
  exact heq_of_eq (congrFun (eq_of_heq hf) x)

private theorem post_eq_section
    {A D : Type*} [Category A] [Category D] {J : GrothendieckTopology D}
    {S : Sheaf J RingCat} {F G H : A ⥤ SheafOfModules.{u + 1} S}
    (e : F ≅ G) (h : G = H) (M : A) (U : Dᵒᵖ) (x : (F.obj M).val.obj U) :
    HEq (((e ≪≫ eqToIso h).hom.app M).val.app U x)
      ((e.hom.app M).val.app U x) := by
  subst H
  rfl

private theorem restriction_rho_iso
    (D : VaryingRing.OrdinaryScalarRestriction C τ B (fun n ↦ CommRingCat.ofHom (φ n)))
    (X : Scheme.{u}) : ∃ e : D.rho X ≅ rhoOrdinary C τ B φ hφ X,
      ∀ (M : Modules C τ X) (n : ℕ) (H : X.ProEtᵒᵖ)
        (x : (((D.rho X).obj M).obj (op n)).val.obj H),
        HEq (((e.hom.app M).app (op n)).val.app H x) x := by
  have he (n : ℕ) : rhoOrdinary C τ B φ hφ X ⋙
      (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) =
      SemilinearSections.evaluation (ProEt.topology X) (coefficients C X)
        (transition C τ X) n ⋙ levelRestriction C B φ X n := by
    unfold rhoOrdinary
    exact (rhoOrdinary_existsUnique C τ B φ X hφ).choose_spec.1.1 n
  let e (n : ℕ) :
      D.rho X ⋙ (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) ≅
      rhoOrdinary C τ B φ hφ X ⋙
        (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) :=
    D.level X n ≪≫ eqToIso (he n).symm
  let t (M : VaryingRing.Modules C τ X) : (D.rho X).obj M ⟶
      (rhoOrdinary C τ B φ hφ X).obj M :=
    NatTrans.ofOpSequence (fun n ↦ (e n).hom.app M) (by
      intro n
      ext U x
      exact transition_transport
        (A := (((D.rho X).obj M).obj (op (n + 1))).val.obj U)
        (B := (((D.rho X).obj M).obj (op n)).val.obj U)
        (rho_section_type C τ B φ hφ X M (n + 1) U.unop)
        (rho_section_type C τ B φ hφ X M n U.unop)
        _ _ _ _ _ _ _
        (post_eq_sections (D.level X n) (he n).symm M U)
        (post_eq_sections (D.level X (n + 1)) (he (n + 1)).symm M U)
        (rho_transition C τ B φ hφ X M n (n + 1) (Nat.le_succ n) U.unop)
        (D.transitions X M n U) x)
  let eM (M : VaryingRing.Modules C τ X) : (D.rho X).obj M ≅
      (rhoOrdinary C τ B φ hφ X).obj M :=
    NatIso.ofComponents (fun n ↦ (e n.unop).app M)
      (fun f ↦ (t M).naturality f)
  refine ⟨NatIso.ofComponents eM (by
    intro M N f
    apply NatTrans.ext
    funext n
    exact (e n.unop).hom.naturality f), ?_⟩
  intro M n H x
  have ht := post_eq_section (D.level X n) (he n).symm M H x
  apply HEq.trans ht
  exact D.level_sections X n M H x

end OrdinaryScalarProof

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Scalar restriction is exact without coefficient flatness. -/
theorem rhoOrdinary_exact (X : Scheme.{u}) :
    (rhoOrdinary C τ B φ hφ X).Additive ∧
      PreservesFiniteLimits (rhoOrdinary C τ B φ hφ X) ∧
        PreservesFiniteColimits (rhoOrdinary C τ B φ hφ X)  := by
  have hψ : ∀ n, CommRingCat.ofHom (φ (n + 1)) ≫ τ n = CommRingCat.ofHom (φ n) :=
    fun n ↦ CommRingCat.hom_ext (hφ n)
  obtain ⟨D⟩ := VaryingRing.ordinaryScalarRestriction C τ B
    (fun n ↦ CommRingCat.ofHom (φ n)) hψ
  obtain ⟨e, _⟩ := restriction_rho_iso C τ B φ hφ D X
  let dAX : (D.rho X).Additive := D.additive X
  let dLX : PreservesFiniteLimits (D.rho X) := D.limits X
  let dCX : PreservesFiniteColimits (D.rho X) := D.colimits X
  exact ⟨Functor.additive_of_iso (F := D.rho X) e,
    preservesFiniteLimits_of_natIso (F := D.rho X) e,
    preservesFiniteColimits_of_natIso (F := D.rho X) e⟩

/-- Additivity of scalar restriction. -/
instance rho_additive (X : Scheme.{u}) : (rhoOrdinary C τ B φ hφ X).Additive :=
  (rhoOrdinary_exact C τ B φ hφ X).1

/-- Left exactness of scalar restriction. -/
instance rho_limits (X : Scheme.{u}) :
    PreservesFiniteLimits (rhoOrdinary C τ B φ hφ X) :=
  (rhoOrdinary_exact C τ B φ hφ X).2.1

/-- Right exactness of scalar restriction. -/
instance rho_colimits (X : Scheme.{u}) :
    PreservesFiniteColimits (rhoOrdinary C τ B φ hφ X) :=
  (rhoOrdinary_exact C τ B φ hφ X).2.2

/-- Exact scalar restriction on ordinary derived systems. -/
abbrev rho (X : Scheme.{u}) := (rhoOrdinary C τ B φ hφ X).mapDerivedCategory

/-- Direct image and scalar restriction commute by the identity on component sections. -/
theorem rhoPushOrdinary_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : rhoOrdinary C τ B φ hφ X ⋙ StrictTower.towerDirectImage B f ≅
      push C τ f ⋙ rhoOrdinary C τ B φ hφ Y,
      ∀ (M : Modules C τ X) (n : ℕ) (U : Y.ProEt),
        HEq (fun x ↦ ((((e.hom.app M).app (op n)).val.app (op U)) x))
          (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x) := by
  have hψ : ∀ n, CommRingCat.ofHom (φ (n + 1)) ≫ τ n = CommRingCat.ofHom (φ n) :=
    fun n ↦ CommRingCat.hom_ext (hφ n)
  obtain ⟨D⟩ := VaryingRing.ordinaryScalarRestriction C τ B
    (fun n ↦ CommRingCat.ofHom (φ n)) hψ
  obtain ⟨G⟩ := VaryingRing.ordinaryScalarAdjunctions C τ B
    (fun n ↦ CommRingCat.ofHom (φ n)) hψ D
  obtain ⟨aX, haX⟩ := restriction_rho_iso C τ B φ hφ D X
  obtain ⟨aY, haY⟩ := restriction_rho_iso C τ B φ hφ D Y
  let d := Functor.isoWhiskerRight aX.symm (StrictTower.towerDirectImage B f) ≪≫
    (G.d f).symm ≪≫ Functor.isoWhiskerLeft (VaryingRing.push C τ f) aY
  have hd : ∀ (M : Modules C τ X) (n : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ (((d.hom.app M).app (op n)).val.app (op U)) x)
        (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x) := by
    intro M n U
    apply normalized_function
      (rho_section_type C τ B φ hφ X M n ((proEtaleBaseChange f).obj U))
      (rho_section_type C τ B φ hφ Y ((VaryingRing.push C τ f).obj M) n U)
    intro x
    let y := (((aX.inv.app M).app (op n)).val.app
      (op ((proEtaleBaseChange f).obj U))) x
    let z := ((((G.d f).inv.app M).app (op n)).val.app (op U)) y
    have hy : HEq y x := normalized_inverse
      (fun q ↦ (((aX.hom.app M).app (op n)).val.app
        (op ((proEtaleBaseChange f).obj U))) q)
      (fun q ↦ (((aX.inv.app M).app (op n)).val.app
        (op ((proEtaleBaseChange f).obj U))) q)
      (fun q ↦ congrArg (fun v ↦ (v.app (op n)).val.app
        (op ((proEtaleBaseChange f).obj U)) q) (aX.inv_hom_id_app M))
      (haX M n (op ((proEtaleBaseChange f).obj U))) x
    have hz : HEq z y := normalized_inverse
      (fun q ↦ ((((G.d f).hom.app M).app (op n)).val.app (op U)) q)
      (fun q ↦ ((((G.d f).inv.app M).app (op n)).val.app (op U)) q)
      (fun q ↦ congrArg (fun v ↦ (v.app (op n)).val.app (op U) q)
        ((G.d f).inv_hom_id_app M)) (G.d_sections f M n (op U)) y
    exact (haY ((VaryingRing.push C τ f).obj M) n (op U) z).trans
      (hz.trans hy)
  obtain ⟨e, he⟩ := tower_normalized_transport
    (congrArg (fun F : Modules C τ X ⥤ Modules C τ Y ↦
      F ⋙ rhoOrdinary C τ B φ hφ Y) (push_eq C τ f).symm) d
    (fun M n U ↦ M.val.obj (op (n.unop, (proEtaleBaseChange f).obj U)))
    (fun M n U ↦ hd M n.unop U)
  refine ⟨e, (fun M n U ↦ he M (op n) U), ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  ext U x
  exact congrFun (eq_of_heq ((he' M n.unop U.unop).trans
    (he M n U.unop).symm)) x

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem restriction_pull_mate_normalization_canonical
    (D : VaryingRing.OrdinaryScalarRestriction C τ B (fun n ↦ CommRingCat.ofHom (φ n)))
    (G : VaryingRing.OrdinaryScalarAdjunctions C τ B (fun n ↦ CommRingCat.ofHom (φ n)) D)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (e : rhoOrdinary C τ B φ hφ X ⋙ StrictTower.towerDirectImage B f ≅
      VaryingRing.push C τ f ⋙ rhoOrdinary C τ B φ hφ Y)
    (he : ∀ (M : Modules C τ X) (n : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ ((e.hom.app M).app (op n)).val.app (op U) x)
        (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)) :
    ∃ (aX : D.rho X ≅ rhoOrdinary C τ B φ hφ X)
      (aY : D.rho Y ≅ rhoOrdinary C τ B φ hφ Y),
      HEq ((mateEquiv (VaryingRing.moduleAdj C τ f)
        (VaryingRing.scalarTowerAdj B f)).symm e.inv)
        (Functor.whiskerRight aY.inv (StrictTower.towerPullback B f) ≫
          (G.b f).inv ≫ Functor.whiskerLeft (VaryingRing.pull C τ f) aX.hom) := by
  obtain ⟨aX, haX⟩ := restriction_rho_iso C τ B φ hφ D X
  obtain ⟨aY, haY⟩ := restriction_rho_iso C τ B φ hφ D Y
  let d := Functor.isoWhiskerLeft (VaryingRing.push C τ f) aY.symm ≪≫
    G.d f ≪≫ Functor.isoWhiskerRight aX (StrictTower.towerDirectImage B f)
  have hd : d.hom = e.inv := by
    apply (cancel_mono e.hom).mp
    erw [e.inv_hom_id]
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    ext U x
    let y := (((aY.inv.app ((VaryingRing.push C τ f).obj M)).app n).val.app U) x
    let z := ((((G.d f).hom.app M).app n).val.app U) y
    let t := (((aX.hom.app M).app n).val.app
      ((proEtaleBaseChange f).op.obj U)) z
    have hy : HEq y x := normalized_inverse
      (fun q ↦ (((aY.hom.app ((VaryingRing.push C τ f).obj M)).app n).val.app U) q)
      (fun q ↦ (((aY.inv.app ((VaryingRing.push C τ f).obj M)).app n).val.app U) q)
      (fun q ↦ congrArg (fun v ↦ (v.app n).val.app U q)
        (aY.inv_hom_id_app ((VaryingRing.push C τ f).obj M)))
      (haY ((VaryingRing.push C τ f).obj M) n.unop U) x
    have hz := G.d_sections f M n.unop U y
    have ht := haX M n.unop ((proEtaleBaseChange f).op.obj U) z
    have hh := normalized_apply
      (rho_section_type C τ B φ hφ X M n.unop ((proEtaleBaseChange f).obj U.unop))
      (rho_section_type C τ B φ hφ Y ((VaryingRing.push C τ f).obj M) n.unop U.unop)
      _ (he M n.unop U.unop) t
    exact eq_of_heq (hh.trans (ht.trans (hz.trans hy)))
  let w := ((TwoSquare.mk _ _ _ _ (G.b f).inv).whiskerTop aY.inv).whiskerBottom aX.hom
  have hw : mateEquiv (VaryingRing.moduleAdj C τ f)
      (VaryingRing.scalarTowerAdj B f) w = TwoSquare.mk _ _ _ _ d.hom := by
    dsimp only [w]
    erw [mateEquiv_whiskerTop_whiskerBottom]
    refine NatTrans.ext (funext fun N ↦ ?_)
    change aY.inv.app ((VaryingRing.push C τ f).obj N) ≫
      (mateEquiv (VaryingRing.moduleAdj C τ f) (VaryingRing.scalarTowerAdj B f)
        (G.b f).inv).app N ≫
        (StrictTower.towerDirectImage B f).map (aX.hom.app N) = d.hom.app N
    rw [G.mate]
    rfl
  refine ⟨aX, aY, ?_⟩
  rw [← hd]
  change HEq ((mateEquiv (VaryingRing.moduleAdj C τ f)
    (VaryingRing.scalarTowerAdj B f)).symm (TwoSquare.mk _ _ _ _ d.hom)) _
  rw [← hw, Equiv.symm_apply_apply]
  exact HEq.rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem restriction_pull_mate_normalization
    (D : VaryingRing.OrdinaryScalarRestriction C τ B (fun n ↦ CommRingCat.ofHom (φ n)))
    (G : VaryingRing.OrdinaryScalarAdjunctions C τ B (fun n ↦ CommRingCat.ofHom (φ n)) D)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Modules C τ X ⥤ Modules C τ Y) [F.IsRightAdjoint]
    (hF : F = VaryingRing.push C τ f)
    (e : rhoOrdinary C τ B φ hφ X ⋙ StrictTower.towerDirectImage B f ≅
      F ⋙ rhoOrdinary C τ B φ hφ Y)
    (he : ∀ (M : Modules C τ X) (n : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ ((e.hom.app M).app (op n)).val.app (op U) x)
        (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)) :
    ∃ (aX : D.rho X ≅ rhoOrdinary C τ B φ hφ X)
      (aY : D.rho Y ≅ rhoOrdinary C τ B φ hφ Y),
      HEq ((mateEquiv (Adjunction.ofIsRightAdjoint F)
        (VaryingRing.scalarTowerAdj B f)).symm e.inv)
        (Functor.whiskerRight aY.inv (StrictTower.towerPullback B f) ≫
          (G.b f).inv ≫ Functor.whiskerLeft (VaryingRing.pull C τ f) aX.hom) := by
  subst F
  exact restriction_pull_mate_normalization_canonical C τ B φ hφ D G f e he

/-- The ordinary inverse-image scalar comparison is the transpose of the uniquely
section-normalized direct-image comparison. -/
def rhoPullInv {X Y : Scheme.{u}} (f : X ⟶ Y) :
    rhoOrdinary C τ B φ hφ Y ⋙ StrictTower.towerPullback B f ⟶
      pull C τ f ⋙ rhoOrdinary C τ B φ hφ X :=
  (mateEquiv (ordinaryAdj C τ f)
    ((proEtaleRingModuleAdjunction f (StrictTower.coefficients B Y)
      (StrictTower.coefficients B X) (StrictTower.constantRingIso B f)).whiskerRight ℕᵒᵖ)).symm
    (rhoPushOrdinary_existsUnique C τ B φ hφ f).choose.inv

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The identified-coefficient inverse-image scalar comparison is invertible. -/
theorem rhoPullInv_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (rhoPullInv C τ B φ hφ f) := by
  have hψ : ∀ n, CommRingCat.ofHom (φ (n + 1)) ≫ τ n = CommRingCat.ofHom (φ n) :=
    fun n ↦ CommRingCat.hom_ext (hφ n)
  obtain ⟨D⟩ := VaryingRing.ordinaryScalarRestriction C τ B
    (fun n ↦ CommRingCat.ofHom (φ n)) hψ
  obtain ⟨G⟩ := VaryingRing.ordinaryScalarAdjunctions C τ B
    (fun n ↦ CommRingCat.ofHom (φ n)) hψ D
  obtain ⟨aX, aY, h⟩ := restriction_pull_mate_normalization C τ B φ hφ D G f
    (push C τ f) (push_eq C τ f)
    (rhoPushOrdinary_existsUnique C τ B φ hφ f).choose
    (rhoPushOrdinary_existsUnique C τ B φ hφ f).choose_spec.1
  let b := Functor.isoWhiskerRight aY.symm (StrictTower.towerPullback B f) ≪≫
    (G.b f).symm ≪≫ Functor.isoWhiskerLeft (VaryingRing.pull C τ f) aX
  let g := b.hom
  have hg : IsIso g := b.isIso_hom
  exact @isIso_of_heq _ _ _ _ _ _ _
    (congrArg (fun F ↦ F ⋙ rhoOrdinary C τ B φ hφ X) (pull_eq C τ f))
    (rhoPullInv C τ B φ hφ f) g h hg

/-- The canonical scalar-restriction inverse-image comparison after exact localization. -/
def rhoP {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P C τ f ⋙ rho C τ B φ hφ X ≅ rho C τ B φ hφ Y ⋙ StrictTower.G B f :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
  Functor.mapDerivedCategoryNatIso
    (@asIso _ _ _ _ (rhoPullInv C τ B φ hφ f) (rhoPullInv_isIso C τ B φ hφ f)).symm ≪≫
  (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The direct-image comparison is the actual derived mate of rhoP inverse. -/
def rhoR {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R C τ f ⋙ rho C τ B φ hφ Y ⟶ rho C τ B φ hφ X ⋙ StrictTower.R B f :=
  mateEquiv (adj C τ f) (StrictTower.adj B f) (rhoP C τ B φ hφ f).inv

section ScalarOpenComparison

end ScalarOpenComparison

end ScalarRestriction

end AlgebraicGeometry.ProEtale.SemilinearProperOpen

namespace SemilinearProperOpenScalarAliases
private alias normalized_apply :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.normalized_apply
end SemilinearProperOpenScalarAliases

end ProofEnvironment
