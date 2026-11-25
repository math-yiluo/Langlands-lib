/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIsomorphismInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Compatibility of inverse-image roots of unity

Source: Deligne, Weil I, (2.2), pp. 280--281; Stacks Project, Tags 03PK, 00WX and 03CY
(blueprint: lem-pur-roots-of-unity-inverse-image-iso).

## Main statements

- `proEtaleRootsOfUnityInverseImageIso`: the three comparison properties.
- `existsUnique_proEtaleRootsOfUnityInverseImageAction`: the induced module action.

The inverse-image action is specified on every adjunction-unit section and commutes with
restrictions. These conditions uniquely fix the action produced by inverse image.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem roots_constant_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ℕ) (hN : 0 < N) :
    IsIso (proEtaleConstantInverseImageMap f RingCat.{u + 1}
      (RingCat.of (ULift.{u + 1} (ZMod N)))) := by
  let : HasSheafify (ProEt.topology X) RingCat.{u + 1} := inferInstance
  let : HasSheafify (ProEt.topology Y) RingCat.{u + 1} := inferInstance
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let : TopologicalSpace (ULift.{u + 1} (ZMod N)) := ⊥
  let : DiscreteTopology (ULift.{u + 1} (ZMod N)) := ⟨rfl⟩
  let c := proEtaleConstantInverseImageMap f RingCat.{u + 1}
    (RingCat.of (ULift.{u + 1} (ZMod N)))
  have := (ProEtale.finiteCoefficientConstantComparison_isIso
    (ULift.{u + 1} (ZMod N)) X).1
  have := (ProEtale.finiteCoefficientConstantComparison_isIso
    (ULift.{u + 1} (ZMod N)) Y).1
  have := ProEtale.finiteCoefficientInverseImageMap_isIso f
    (ULift.{u + 1} (ZMod N))
  have hs := ProEtale.finiteCoefficientInverseImageMap_constant f
    (ULift.{u + 1} (ZMod N))
  have : IsIso (c ≫ ProEtale.finiteCoefficientConstantComparison
      (ULift.{u + 1} (ZMod N)) X) := by
    rw [← hs]
    infer_instance
  exact IsIso.of_isIso_comp_right c
    (ProEtale.finiteCoefficientConstantComparison (ULift.{u + 1} (ZMod N)) X)

private theorem roots_inverse_torsion {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ) :
    ∀ (U : X.ProEtᵒᵖ)
      (x : ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf Y N)).obj.obj U), N • x = 0 := by
  let : (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).Additive := ⟨by
    intro A B g h
    ext V x
    rfl⟩
  have : (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).Additive :=
    (proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).left_adjoint_additive
  have hy : N • 𝟙 (proEtaleRootsOfUnitySheaf Y N) = 0 := by
    ext V x
    exact proEtaleRootsOfUnity_nsmul Y N V x
  have hx := congrArg (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map hy
  rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero] at hx
  intro U x
  exact congrArg (fun g ↦ g.hom.app U x) hx

@[instance_reducible]
private noncomputable def roots_restrict_module {S : Scheme.{u}}
    [HasSheafify (ProEt.topology S) RingCat.{u + 1}] (N : ℕ)
    (F : Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1})
    (R : Sheaf (ProEt.topology S) RingCat.{u + 1})
    (g : constantZModRingSheaf (ProEt.topology S) N ⟶ R)
    (M : ∀ U : S.ProEtᵒᵖ, Module (R.obj.obj U) (F.obj.obj U)) (U : S.ProEtᵒᵖ) :
    Module ((constantZModRingSheaf (ProEt.topology S) N).obj.obj U) (F.obj.obj U) := by
  let := M U
  exact Module.compHom (F.obj.obj U) (g.hom.app U).hom

private theorem roots_restrict_spec {S : Scheme.{u}}
    [HasSheafify (ProEt.topology S) RingCat.{u + 1}] (N : ℕ)
    (F : Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1})
    (R : Sheaf (ProEt.topology S) RingCat.{u + 1})
    (g : constantZModRingSheaf (ProEt.topology S) N ⟶ R)
    (M : ∀ U : S.ProEtᵒᵖ, Module (R.obj.obj U) (F.obj.obj U))
    (hM : ∀ (U V : S.ProEtᵒᵖ) (b : U ⟶ V) (a : R.obj.obj U) (x : F.obj.obj U),
      F.obj.map b (@SMul.smul _ _ (M U).toSMul a x) =
        @SMul.smul _ _ (M V).toSMul (R.obj.map b a) (F.obj.map b x)) :
    IsConstantZModSheafModuleStructure (ProEt.topology S) N F
      (roots_restrict_module N F R g M) := by
  constructor
  · intro U z x
    let := M U
    change (g.hom.app U)
      ((toSheafify (ProEt.topology S)
        ((Functor.const S.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod N))))).app U
          (z : ULift.{u + 1} (ZMod N))) • x = z • x
    rw [map_intCast, map_intCast, Int.cast_smul_eq_zsmul]
  · intro U V b a x
    change F.obj.map b (@SMul.smul _ _ (M U).toSMul (g.hom.app U a) x) =
      @SMul.smul _ _ (M V).toSMul
        (g.hom.app V ((constantZModRingSheaf (ProEt.topology S) N).obj.map b a))
        (F.obj.map b x)
    rw [hM U V b]
    have hn := ConcreteCategory.congr_hom (g.hom.naturality b) a
    exact congrArg (fun z ↦ @SMul.smul _ _ (M V).toSMul z (F.obj.map b x)) hn.symm

private theorem proEtaleRootsComparison_normalizedAction_linear
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ) (hN : 0 < N)
    (M : ∀ U : X.ProEtᵒᵖ, Module
      (((proEtaleSheafInverseImage f RingCat.{u + 1}).obj
        (proEtaleRootsOfUnityCoefficientRing Y N)).obj.obj U)
      (((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf Y N)).obj.obj U))
    (hM : (∀ (V : Y.ProEtᵒᵖ) (a : (proEtaleRootsOfUnityCoefficientRing Y N).obj.obj V)
    (x : (proEtaleRootsOfUnitySheaf Y N).obj.obj V),
    ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
      (proEtaleRootsOfUnitySheaf Y N)).hom.app V
        (@SMul.smul _ _ (torsionSheafModuleStructure.{u + 1} (ProEt.topology Y) N hN
          (proEtaleRootsOfUnitySheaf Y N) (proEtaleRootsOfUnity_nsmul Y N) V).toSMul a x) =
      @SMul.smul _ _ (M ((proEtaleBaseChange f).op.obj V)).toSMul
        (((proEtaleSheafAdjunction f RingCat.{u + 1}).unit.app
          (proEtaleRootsOfUnityCoefficientRing Y N)).hom.app V a)
        (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
          (proEtaleRootsOfUnitySheaf Y N)).hom.app V x)) ∧
  ∀ (U V : X.ProEtᵒᵖ) (b : U ⟶ V)
    (a : ((proEtaleSheafInverseImage f RingCat.{u + 1}).obj
      (proEtaleRootsOfUnityCoefficientRing Y N)).obj.obj U)
    (x : ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
      (proEtaleRootsOfUnitySheaf Y N)).obj.obj U),
    ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf Y N)).obj.map b
          (@SMul.smul _ _ (M U).toSMul a x) =
      @SMul.smul _ _ (M V).toSMul
        (((proEtaleSheafInverseImage f RingCat.{u + 1}).obj
      (proEtaleRootsOfUnityCoefficientRing Y N)).obj.map b a)
        (((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
          (proEtaleRootsOfUnitySheaf Y N)).obj.map b x) ) :
    ∀ (U : X.ProEtᵒᵖ)
      (a : ((proEtaleSheafInverseImage f RingCat.{u + 1}).obj
        (proEtaleRootsOfUnityCoefficientRing Y N)).obj.obj U)
      (x : ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf Y N)).obj.obj U),
      (proEtaleRootsOfUnityInverseImageMap f N).hom.app U
          (@SMul.smul _ _ (M U).toSMul a x) =
        @SMul.smul _ _ (torsionSheafModuleStructure.{u + 1} (ProEt.topology X) N hN
          (proEtaleRootsOfUnitySheaf X N) (proEtaleRootsOfUnity_nsmul X N) U).toSMul
          ((proEtaleConstantInverseImageMap f RingCat.{u + 1}
            (RingCat.of (ULift.{u + 1} (ZMod N)))).hom.app U a)
          ((proEtaleRootsOfUnityInverseImageMap f N).hom.app U x) := by
  let : HasSheafify (ProEt.topology X) RingCat.{u + 1} := inferInstance
  let c := proEtaleConstantInverseImageMap f RingCat.{u + 1}
    (RingCat.of (ULift.{u + 1} (ZMod N)))
  have : IsIso c := roots_constant_iso f N hN
  let F := (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
    (proEtaleRootsOfUnitySheaf Y N)
  let M' (U : X.ProEtᵒᵖ) :
      Module ((constantZModRingSheaf (ProEt.topology X) N).obj.obj U) (F.obj.obj U) :=
    by
      let := M U
      exact Module.compHom (F.obj.obj U) ((inv c).hom.app U).hom
  have hM' : IsConstantZModSheafModuleStructure (ProEt.topology X) N F M' := by
    constructor
    · intro U z x
      let := M U
      change ((inv c).hom.app U)
        ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod N))))).app U
            (ULift.up (z : ZMod N))) • x = z • x
      change ((inv c).hom.app U)
        ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod N))))).app U
            (z : ULift.{u + 1} (ZMod N))) • x = z • x
      rw [map_intCast, map_intCast, Int.cast_smul_eq_zsmul]
    · intro U V b a x
      change F.obj.map b (@SMul.smul _ _ (M U).toSMul ((inv c).hom.app U a) x) =
        @SMul.smul _ _ (M V).toSMul
          ((inv c).hom.app V ((constantZModRingSheaf (ProEt.topology X) N).obj.map b a))
          (F.obj.map b x)
      rw [hM.2 U V b]
      have hn := ConcreteCategory.congr_hom ((inv c).hom.naturality b) a
      exact congrArg (fun z ↦ @SMul.smul _ _ (M V).toSMul z (F.obj.map b x)) hn.symm
  have hF : ∀ (U : X.ProEtᵒᵖ) (x : F.obj.obj U), N • x = 0 := by
    intro U x
    let := M' U
    have hn : (N : (constantZModRingSheaf (ProEt.topology X) N).obj.obj U) = 0 := by
      have h := congrArg
        ((toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod N))))).app U)
        (show (N : ULift.{u + 1} (ZMod N)) = 0 by
          apply ULift.ext
          exact ZMod.natCast_self N)
      simpa only [map_natCast, map_zero] using h
    rw [← Nat.cast_smul_eq_nsmul
      ((constantZModRingSheaf (ProEt.topology X) N).obj.obj U), hn, zero_smul]
  have hl := torsionSheaf_hom_linear (ProEt.topology X) N hN F
    (proEtaleRootsOfUnitySheaf X N) hF (proEtaleRootsOfUnity_nsmul X N)
    (proEtaleRootsOfUnityInverseImageMap f N) M'
    (torsionSheafModuleStructure (ProEt.topology X) N hN
      (proEtaleRootsOfUnitySheaf X N) (proEtaleRootsOfUnity_nsmul X N))
    hM' (torsionSheafModuleStructure_spec (ProEt.topology X) N hN
      (proEtaleRootsOfUnitySheaf X N) (proEtaleRootsOfUnity_nsmul X N))
  intro U a x
  have hi := ConcreteCategory.congr_hom
    (congrArg (fun z ↦ z.hom.app U) (IsIso.hom_inv_id c)) a
  change (inv c).hom.app U (c.hom.app U a) = a at hi
  have hh := hl U (c.hom.app U a) x
  change (proEtaleRootsOfUnityInverseImageMap f N).hom.app U
      (@SMul.smul _ _ (M U).toSMul ((inv c).hom.app U (c.hom.app U a)) x) = _ at hh
  rw [hi] at hh
  exact hh

private theorem roots_sections_inclusion (S : Scheme.{u}) (N : ℕ)
    (U : S.ProEtᵒᵖ) (x : (proEtaleRootsOfUnitySheaf S N).obj.obj U) :
    (proEtaleRootsOfUnityInclusion S N).hom.app U x =
      ULift.up (Additive.ofMul
        (Additive.toMul (proEtaleRootsOfUnitySections S N U x)).val) :=
  ((existsUnique_proEtaleRootsOfUnitySections S N U).exists.choose_spec x).symm

private theorem roots_transition_inclusion (S : Scheme.{u}) (N N' : ℕ)
    (hN : 0 < N) (hN' : 0 < N') (h : N ∣ N')
    (U : S.ProEtᵒᵖ) (x : (proEtaleRootsOfUnitySheaf S N').obj.obj U) :
    (proEtaleRootsOfUnityInclusion S N).hom.app U
      ((proEtaleRootsOfUnityTransition S N N' hN hN' h).hom.app U x) =
        (N' / N) • (proEtaleRootsOfUnityInclusion S N').hom.app U x := by
  have w := kernel.lift_ι (proEtaleUnitsPower S N)
    (proEtaleRootsOfUnityInclusion S N' ≫ ((N' / N) • 𝟙 (proEtaleUnitsSheaf S)))
    (proEtaleRootsOfUnityTransition_condition S N N' hN hN' h)
  exact congrArg (fun a ↦ a.hom.app U x) w

private theorem roots_direct_formula {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ)
    (V : Y.ProEtᵒᵖ) (x : (proEtaleRootsOfUnitySheaf Y N).obj.obj V) :
    proEtaleRootsOfUnitySections X N ((proEtaleBaseChange f).op.obj V)
      ((proEtaleRootsOfUnityDirectImageMap f N).hom.app V x) =
        Additive.ofMul (restrictRootsOfUnity (pullback.fst V.unop.hom f).appTop.hom N
          (Additive.toMul (proEtaleRootsOfUnitySections Y N V x))) :=
  (existsUnique_proEtaleRootsOfUnityDirectImageMap f N).exists.choose_spec V x

private theorem roots_transition_value (S : Scheme.{u}) (N N' : ℕ)
    (hN : 0 < N) (hN' : 0 < N') (h : N ∣ N')
    (U : S.ProEtᵒᵖ) (x : (proEtaleRootsOfUnitySheaf S N').obj.obj U) :
    (Additive.toMul (proEtaleRootsOfUnitySections S N U
      ((proEtaleRootsOfUnityTransition S N N' hN hN' h).hom.app U x))).val =
        (Additive.toMul (proEtaleRootsOfUnitySections S N' U x)).val ^ (N' / N) := by
  have w := roots_transition_inclusion S N N' hN hN' h U x
  rw [roots_sections_inclusion, roots_sections_inclusion] at w
  exact congrArg (fun z ↦ Additive.toMul z.down) w

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem roots_direct_transition {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N N' : ℕ) (hN : 0 < N) (hN' : 0 < N') (h : N ∣ N') :
    proEtaleRootsOfUnityTransition Y N N' hN hN' h ≫
        proEtaleRootsOfUnityDirectImageMap f N =
      proEtaleRootsOfUnityDirectImageMap f N' ≫
        (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map
          (proEtaleRootsOfUnityTransition X N N' hN hN' h) := by
  ext V x
  apply (proEtaleRootsOfUnitySections X N ((proEtaleBaseChange f).op.obj V)).injective
  apply Additive.toMul.injective
  apply Subtype.val_injective
  change (Additive.toMul (proEtaleRootsOfUnitySections X N _
      ((proEtaleRootsOfUnityDirectImageMap f N).hom.app V
        ((proEtaleRootsOfUnityTransition Y N N' hN hN' h).hom.app V x)))).val =
    (Additive.toMul (proEtaleRootsOfUnitySections X N _
      ((proEtaleRootsOfUnityTransition X N N' hN hN' h).hom.app _
        ((proEtaleRootsOfUnityDirectImageMap f N').hom.app V x)))).val
  have h1 := roots_direct_formula f N V
    ((proEtaleRootsOfUnityTransition Y N N' hN hN' h).hom.app V x)
  have h2 := roots_transition_value X N N' hN hN' h
    ((proEtaleBaseChange f).op.obj V)
    ((proEtaleRootsOfUnityDirectImageMap f N').hom.app V x)
  have h3 := roots_direct_formula f N' V x
  refine (congrArg (fun z ↦ (Additive.toMul z).val) h1).trans (Eq.trans ?_ h2.symm)
  apply Units.ext
  have w := congrArg Units.val (roots_transition_value Y N N' hN hN' h V x)
  have w' := congrArg (fun z ↦ (Additive.toMul z).val.val) h3
  change (pullback.fst V.unop.hom f).appTop.hom
      (Additive.toMul (proEtaleRootsOfUnitySections Y N V
        ((proEtaleRootsOfUnityTransition Y N N' hN hN' h).hom.app V x))).val.val =
    (Additive.toMul (proEtaleRootsOfUnitySections X N' _
      ((proEtaleRootsOfUnityDirectImageMap f N').hom.app V x))).val.val ^ (N' / N)
  exact (congrArg (pullback.fst V.unop.hom f).appTop.hom w).trans
    ((map_pow _ _ _).trans (congrArg (fun z ↦ z ^ (N' / N)) w'.symm))

private theorem roots_inverse_transition {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N N' : ℕ) (hN : 0 < N) (hN' : 0 < N') (h : N ∣ N') :
    (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
        (proEtaleRootsOfUnityTransition Y N N' hN hN' h) ≫
      proEtaleRootsOfUnityInverseImageMap f N =
    proEtaleRootsOfUnityInverseImageMap f N' ≫
      proEtaleRootsOfUnityTransition X N N' hN hN' h :=
  (proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv_naturality_right_square
    _ _ _ _ (roots_direct_transition f N N' hN hN' h)

private theorem roots_tower_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ c : proEtaleRootsOfUnityTower Y ℓ hℓ ⋙
        proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} ⟶
      proEtaleRootsOfUnityTower X ℓ hℓ,
      ∀ r : ℕ, c.app (op r) = proEtaleRootsOfUnityInverseImageMap f (ℓ ^ (r + 1)) := by
  refine ⟨NatTrans.ofOpSequence
    (fun r ↦ proEtaleRootsOfUnityInverseImageMap f (ℓ ^ (r + 1))) ?_, fun _ ↦ rfl⟩
  intro r
  simpa only [Functor.comp_map, proEtaleRootsOfUnityTower,
    Functor.ofOpSequence_map_homOfLE_succ] using
      roots_inverse_transition f (ℓ ^ (r + 1)) (ℓ ^ (r + 2))
        (pow_pos hℓ.pos _) (pow_pos hℓ.pos _)
        (pow_dvd_pow ℓ (Nat.le_succ (r + 1)))

private theorem roots_restrict_value (S : Scheme.{u}) (N : ℕ)
    {U V : S.ProEtᵒᵖ} (b : U ⟶ V)
    (x : (proEtaleRootsOfUnitySheaf S N).obj.obj U) :
    (Additive.toMul (proEtaleRootsOfUnitySections S N V
      ((proEtaleRootsOfUnitySheaf S N).obj.map b x))).val.val =
    b.unop.left.appTop.hom
      (Additive.toMul (proEtaleRootsOfUnitySections S N U x)).val.val := by
  have w := ConcreteCategory.congr_hom
    ((proEtaleRootsOfUnityInclusion S N).hom.naturality b) x
  change (proEtaleRootsOfUnityInclusion S N).hom.app V
    ((proEtaleRootsOfUnitySheaf S N).obj.map b x) =
    (proEtaleUnitsSheaf S).obj.map b
      ((proEtaleRootsOfUnityInclusion S N).hom.app U x) at w
  rw [roots_sections_inclusion, roots_sections_inclusion] at w
  exact congrArg (fun z ↦ (Additive.toMul z.down).val) w

private theorem roots_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ)
    (V : Y.ProEtᵒᵖ) (x : (proEtaleRootsOfUnitySheaf Y N).obj.obj V) :
    (proEtaleRootsOfUnityInverseImageMap f N).hom.app ((proEtaleBaseChange f).op.obj V)
      (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
        (proEtaleRootsOfUnitySheaf Y N)).hom.app V x) =
    (proEtaleRootsOfUnityDirectImageMap f N).hom.app V x := by
  have w := ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).apply_symm_apply
    (proEtaleRootsOfUnityDirectImageMap f N)
  exact congrArg (fun a ↦ a.hom.app V x) w

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem roots_iso_value {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (N : ℕ)
    (U : X.ProEtᵒᵖ)
    (y : (proEtaleRootsOfUnitySheaf Y N).obj.obj ((proEtaleIsoPostcompose f).op.obj U)) :
    proEtaleRootsOfUnitySections X N U
      ((proEtaleRootsOfUnityInverseImageMap f N).hom.app U
        (((proEtaleIsoInverseImageIdentification f AddCommGrpCat.{u + 1}).inv.app
          (proEtaleRootsOfUnitySheaf Y N)).app U y)) =
      proEtaleRootsOfUnitySections Y N ((proEtaleIsoPostcompose f).op.obj U) y := by
  have he := (existsUnique_proEtaleIsoInverseImageIdentification
    f AddCommGrpCat.{u + 1}).exists.choose_spec (proEtaleRootsOfUnitySheaf Y N) U.unop
  have hn := ConcreteCategory.congr_hom
    ((proEtaleRootsOfUnityInverseImageMap f N).hom.naturality
      (proEtaleIsoCommaArrow f U.unop).op)
    (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
      (proEtaleRootsOfUnitySheaf Y N)).hom.app
        ((proEtaleIsoPostcompose f).op.obj U) y)
  have hv := roots_unit f N ((proEtaleIsoPostcompose f).op.obj U) y
  change (((proEtaleIsoInverseImageIdentification f AddCommGrpCat.{u + 1}).inv.app
    (proEtaleRootsOfUnitySheaf Y N)).app U) = _ at he
  rw [he]
  change proEtaleRootsOfUnitySections X N U
    ((proEtaleRootsOfUnityInverseImageMap f N).hom.app U
      (((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf Y N)).obj.map (proEtaleIsoCommaArrow f U.unop).op
          (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
            (proEtaleRootsOfUnitySheaf Y N)).hom.app
              ((proEtaleIsoPostcompose f).op.obj U) y))) = _
  change (proEtaleRootsOfUnityInverseImageMap f N).hom.app U
    (((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
      (proEtaleRootsOfUnitySheaf Y N)).obj.map (proEtaleIsoCommaArrow f U.unop).op
        (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
          (proEtaleRootsOfUnitySheaf Y N)).hom.app
            ((proEtaleIsoPostcompose f).op.obj U) y)) = _ at hn
  rw [hn]
  change proEtaleRootsOfUnitySections X N U
    ((proEtaleRootsOfUnitySheaf X N).obj.map (proEtaleIsoCommaArrow f U.unop).op
      ((proEtaleRootsOfUnityInverseImageMap f N).hom.app
        ((proEtaleBaseChange f).op.obj ((proEtaleIsoPostcompose f).op.obj U))
          (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
            (proEtaleRootsOfUnitySheaf Y N)).hom.app
              ((proEtaleIsoPostcompose f).op.obj U) y))) = _
  rw [hv]
  apply Additive.toMul.injective
  apply Subtype.val_injective
  apply Units.ext
  have hr := roots_restrict_value X N (proEtaleIsoCommaArrow f U.unop).op
    ((proEtaleRootsOfUnityDirectImageMap f N).hom.app
      ((proEtaleIsoPostcompose f).op.obj U) y)
  have hd := roots_direct_formula f N ((proEtaleIsoPostcompose f).op.obj U) y
  have hd' := congrArg (fun z ↦ (Additive.toMul z).val.val) hd
  refine hr.trans ?_
  change (proEtaleIsoCommaArrow f U.unop).left.appTop.hom
    (Additive.toMul (proEtaleRootsOfUnitySections X N _
      ((proEtaleRootsOfUnityDirectImageMap f N).hom.app
        ((proEtaleIsoPostcompose f).op.obj U) y))).val.val = _
  rw [hd']
  change (((pullback.fst ((proEtaleIsoPostcompose f).obj U.unop).hom f).appTop ≫
    (proEtaleIsoCommaArrow f U.unop).left.appTop).hom
      (Additive.toMul (proEtaleRootsOfUnitySections Y N _ y)).val.val) = _
  rw [← Hom.comp_appTop]
  have hp : (proEtaleIsoCommaArrow f U.unop).left ≫
      pullback.fst ((proEtaleIsoPostcompose f).obj U.unop).hom f = 𝟙 U.unop.left := by
    exact pullback.lift_fst _ _ _
  rw [hp]
  rfl

private theorem roots_iso_clause {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (N : ℕ) :
    IsIso (proEtaleRootsOfUnityInverseImageMap f N) ∧
      ∀ (U : X.ProEtᵒᵖ)
        (x : ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
          (proEtaleRootsOfUnitySheaf Y N)).obj.obj U),
        proEtaleRootsOfUnitySections X N U
            ((proEtaleRootsOfUnityInverseImageMap f N).hom.app U x) =
          proEtaleRootsOfUnitySections Y N ((proEtaleIsoPostcompose f).op.obj U)
            (((proEtaleIsoInverseImageIdentification f AddCommGrpCat.{u + 1}).hom.app
              (proEtaleRootsOfUnitySheaf Y N)).app U x) := by
  have he (U : X.ProEtᵒᵖ) :
      Function.Bijective (((proEtaleIsoInverseImageIdentification
        f AddCommGrpCat.{u + 1}).inv.app (proEtaleRootsOfUnitySheaf Y N)).app U) :=
    ConcreteCategory.bijective_of_isIso _
  have hv (U : X.ProEtᵒᵖ)
      (x : ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf Y N)).obj.obj U) :
      proEtaleRootsOfUnitySections X N U
          ((proEtaleRootsOfUnityInverseImageMap f N).hom.app U x) =
        proEtaleRootsOfUnitySections Y N ((proEtaleIsoPostcompose f).op.obj U)
          (((proEtaleIsoInverseImageIdentification f AddCommGrpCat.{u + 1}).hom.app
            (proEtaleRootsOfUnitySheaf Y N)).app U x) := by
    obtain ⟨y, rfl⟩ := (he U).surjective x
    have hi := congrArg (fun a ↦ (a.app (proEtaleRootsOfUnitySheaf Y N)).app U y)
      (proEtaleIsoInverseImageIdentification f AddCommGrpCat.{u + 1}).inv_hom_id
    change (((proEtaleIsoInverseImageIdentification f AddCommGrpCat.{u + 1}).hom.app
      (proEtaleRootsOfUnitySheaf Y N)).app U
        ((((proEtaleIsoInverseImageIdentification f AddCommGrpCat.{u + 1}).inv.app
          (proEtaleRootsOfUnitySheaf Y N)).app U) y)) = y at hi
    rw [hi]
    exact roots_iso_value f N U y
  refine ⟨?_, hv⟩
  have hc (U : X.ProEtᵒᵖ) :
      Function.Bijective ((proEtaleRootsOfUnityInverseImageMap f N).hom.app U) := by
    constructor
    · intro x x' h
      have hh := (hv U x).symm.trans
        ((congrArg (proEtaleRootsOfUnitySections X N U) h).trans (hv U x'))
      apply (ConcreteCategory.bijective_of_isIso
        (((proEtaleIsoInverseImageIdentification f AddCommGrpCat.{u + 1}).hom.app
          (proEtaleRootsOfUnitySheaf Y N)).app U)).injective
      exact (proEtaleRootsOfUnitySections Y N _).injective hh
    · intro z
      let y := (proEtaleRootsOfUnitySections Y N
        ((proEtaleIsoPostcompose f).op.obj U)).symm (proEtaleRootsOfUnitySections X N U z)
      refine ⟨(((proEtaleIsoInverseImageIdentification f AddCommGrpCat.{u + 1}).inv.app
        (proEtaleRootsOfUnitySheaf Y N)).app U) y, ?_⟩
      apply (proEtaleRootsOfUnitySections X N U).injective
      exact (roots_iso_value f N U y).trans (AddEquiv.apply_symm_apply _ _)
  have : ∀ U, IsIso ((proEtaleRootsOfUnityInverseImageMap f N).hom.app U) :=
    fun U ↦ (ConcreteCategory.isIso_iff_bijective _).2 (hc U)
  have : IsIso (proEtaleRootsOfUnityInverseImageMap f N).hom :=
    NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).map
      (proEtaleRootsOfUnityInverseImageMap f N)) := ‹IsIso
        (proEtaleRootsOfUnityInverseImageMap f N).hom›
  exact isIso_of_reflects_iso (proEtaleRootsOfUnityInverseImageMap f N)
    (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1})

/-- The inverse-image coefficient ring for the roots-of-unity sheaf.
Source: Stacks Project, Tags 00YV and 03CY
(blueprint: lem-pur-roots-of-unity-inverse-image-iso). -/
noncomputable abbrev proEtaleRootsOfUnityInverseImageRing {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ℕ) : Sheaf (ProEt.topology X) RingCat.{u + 1} :=
  (proEtaleSheafInverseImage f RingCat.{u + 1}).obj
    (proEtaleRootsOfUnityCoefficientRing Y N)

/-- The induced action is normalized on the actual inverse-image adjunction units and
commutes with all restrictions. This is the coefficient action on the inverse image,
with the underlying ring and abelian sheaf kept fixed.
Source: Stacks Project, Tags 00YV and 03CY
(blueprint: lem-pur-roots-of-unity-inverse-image-iso). -/
def IsProEtaleRootsOfUnityInverseImageAction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ℕ) (hN : 0 < N)
    (M : ∀ U : X.ProEtᵒᵖ, Module
      ((proEtaleRootsOfUnityInverseImageRing f N).obj.obj U)
      (((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf Y N)).obj.obj U)) : Prop :=
  (∀ (V : Y.ProEtᵒᵖ) (a : (proEtaleRootsOfUnityCoefficientRing Y N).obj.obj V)
    (x : (proEtaleRootsOfUnitySheaf Y N).obj.obj V),
    ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
      (proEtaleRootsOfUnitySheaf Y N)).hom.app V
        (@SMul.smul _ _ (torsionSheafModuleStructure.{u + 1} (ProEt.topology Y) N hN
          (proEtaleRootsOfUnitySheaf Y N) (proEtaleRootsOfUnity_nsmul Y N) V).toSMul a x) =
      @SMul.smul _ _ (M ((proEtaleBaseChange f).op.obj V)).toSMul
        (((proEtaleSheafAdjunction f RingCat.{u + 1}).unit.app
          (proEtaleRootsOfUnityCoefficientRing Y N)).hom.app V a)
        (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
          (proEtaleRootsOfUnitySheaf Y N)).hom.app V x)) ∧
  ∀ (U V : X.ProEtᵒᵖ) (b : U ⟶ V)
    (a : (proEtaleRootsOfUnityInverseImageRing f N).obj.obj U)
    (x : ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
      (proEtaleRootsOfUnitySheaf Y N)).obj.obj U),
    ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf Y N)).obj.map b
          (@SMul.smul _ _ (M U).toSMul a x) =
      @SMul.smul _ _ (M V).toSMul
        ((proEtaleRootsOfUnityInverseImageRing f N).obj.map b a)
        (((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
          (proEtaleRootsOfUnitySheaf Y N)).obj.map b x)

/-- The inverse image of the coefficient action is uniquely determined by unit sections.
Source: Stacks Project, Tags 00YV and 03CY
(blueprint: lem-pur-roots-of-unity-inverse-image-iso).
Proof: apply the finite-product-preserving set inverse image to the original scalar
multiplication, addition and zero. Preservation of products transports the module axioms.
The adjunction unit preserves these operations and restrictions commute with them.
Conversely, unit sections and their restrictions generate the left Kan extension;
sheafification is locally generated by that presheaf. Hence the unit normalization and
restriction compatibility force the action on all local sections, proving uniqueness. -/
theorem existsUnique_proEtaleRootsOfUnityInverseImageAction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ℕ) (hN : 0 < N) :
    ∃! M : ∀ U : X.ProEtᵒᵖ, Module
      ((proEtaleRootsOfUnityInverseImageRing f N).obj.obj U)
      (((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf Y N)).obj.obj U),
      IsProEtaleRootsOfUnityInverseImageAction f N hN M := by
  let : HasSheafify (ProEt.topology X) RingCat.{u + 1} := inferInstance
  let : HasSheafify (ProEt.topology Y) RingCat.{u + 1} := inferInstance
  let R := proEtaleRootsOfUnityInverseImageRing f N
  let F := (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
    (proEtaleRootsOfUnitySheaf Y N)
  let c := proEtaleConstantInverseImageMap f RingCat.{u + 1}
    (RingCat.of (ULift.{u + 1} (ZMod N)))
  have : IsIso c := roots_constant_iso f N hN
  have hF : ∀ (U : X.ProEtᵒᵖ) (x : F.obj.obj U), N • x = 0 :=
    roots_inverse_torsion f N
  let K := torsionSheafModuleStructure (ProEt.topology X) N hN F hF
  have hK := torsionSheafModuleStructure_spec (ProEt.topology X) N hN F hF
  let M (U : X.ProEtᵒᵖ) : Module (R.obj.obj U) (F.obj.obj U) := by
    let := K U
    exact Module.compHom (F.obj.obj U) (c.hom.app U).hom
  have hres : ∀ (U V : X.ProEtᵒᵖ) (b : U ⟶ V)
      (a : R.obj.obj U) (x : F.obj.obj U),
      F.obj.map b (@SMul.smul _ _ (M U).toSMul a x) =
        @SMul.smul _ _ (M V).toSMul (R.obj.map b a) (F.obj.map b x) := by
    intro U V b a x
    change F.obj.map b (@SMul.smul _ _ (K U).toSMul (c.hom.app U a) x) =
      @SMul.smul _ _ (K V).toSMul (c.hom.app V (R.obj.map b a)) (F.obj.map b x)
    rw [hK.2 b]
    have hn := ConcreteCategory.congr_hom (c.hom.naturality b) a
    exact congrArg (fun z ↦ @SMul.smul _ _ (K V).toSMul z (F.obj.map b x)) hn.symm
  refine ⟨M, ⟨?_, hres⟩, ?_⟩
  · let D := (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj F
    let RD := (proEtaleSheafDirectImage f RingCat.{u + 1}).obj R
    let g : constantZModRingSheaf (ProEt.topology Y) N ⟶ RD :=
      (proEtaleSheafAdjunction f RingCat.{u + 1}).unit.app
        (proEtaleRootsOfUnityCoefficientRing Y N)
    let L (V : Y.ProEtᵒᵖ) : Module (RD.obj.obj V) (D.obj.obj V) :=
      M ((proEtaleBaseChange f).op.obj V)
    have hL : ∀ (U V : Y.ProEtᵒᵖ) (b : U ⟶ V)
        (a : RD.obj.obj U) (x : D.obj.obj U),
        D.obj.map b (@SMul.smul _ _ (L U).toSMul a x) =
          @SMul.smul _ _ (L V).toSMul (RD.obj.map b a) (D.obj.map b x) := by
      intro U V b a x
      exact hres _ _ ((proEtaleBaseChange f).op.map b) a x
    have hD : ∀ (V : Y.ProEtᵒᵖ) (x : D.obj.obj V), N • x = 0 :=
      fun V x ↦ hF ((proEtaleBaseChange f).op.obj V) x
    have hl := torsionSheaf_hom_linear (ProEt.topology Y) N hN
      (proEtaleRootsOfUnitySheaf Y N) D (proEtaleRootsOfUnity_nsmul Y N) hD
      ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
        (proEtaleRootsOfUnitySheaf Y N))
      (torsionSheafModuleStructure (ProEt.topology Y) N hN
        (proEtaleRootsOfUnitySheaf Y N) (proEtaleRootsOfUnity_nsmul Y N))
      (roots_restrict_module N D RD g L)
      (torsionSheafModuleStructure_spec (ProEt.topology Y) N hN
        (proEtaleRootsOfUnitySheaf Y N) (proEtaleRootsOfUnity_nsmul Y N))
      (roots_restrict_spec N D RD g L hL)
    exact hl
  · intro M' hM'
    let K' := roots_restrict_module N F R (inv c) M'
    have hK' : IsConstantZModSheafModuleStructure (ProEt.topology X) N F K' :=
      roots_restrict_spec N F R (inv c) M' hM'.2
    have he : K' = K :=
      (existsUnique_constantZModSheafModuleStructure (ProEt.topology X) N hN F hF).unique
        hK' hK
    funext U
    apply Module.ext'
    intro a x
    have hi := ConcreteCategory.congr_hom
      (congrArg (fun z ↦ z.hom.app U) (IsIso.hom_inv_id c)) a
    change (inv c).hom.app U (c.hom.app U a) = a at hi
    have hev := congrArg
      (fun A ↦ @SMul.smul _ _ (A U).toSMul (c.hom.app U a) x) he
    change @SMul.smul _ _ (M' U).toSMul
      ((inv c).hom.app U (c.hom.app U a)) x =
        @SMul.smul _ _ (K U).toSMul (c.hom.app U a) x at hev
    rw [hi] at hev
    exact hev

/-- The actual inverse-image action, selected from its uniquely normalized construction.
Source: Stacks Project, Tags 00YV and 03CY
(blueprint: lem-pur-roots-of-unity-inverse-image-iso). -/
@[instance_reducible]
noncomputable def proEtaleRootsOfUnityInverseImageAction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : ℕ) (hN : 0 < N) (U : X.ProEtᵒᵖ) :
    Module ((proEtaleRootsOfUnityInverseImageRing f N).obj.obj U)
      (((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf Y N)).obj.obj U) :=
  (existsUnique_proEtaleRootsOfUnityInverseImageAction f N hN).exists.choose U

/-- All three compatibility clauses for the canonical comparison on roots of unity.
Source: Deligne, Weil I, (2.2), pp. 280--281; Stacks Project, Tags 03PK, 00WX and 03CY
(blueprint: lem-pur-roots-of-unity-inverse-image-iso).
Proof: (1) write `k=N'/N`. Pullback of functions commutes with `v ↦ v^k`, and
`k*N=N'` shows both values are `N`-th roots. Equality sectionwise gives equality of
adjuncts. Naturality of the adjunction unit and injectivity of its hom equivalence give
the transition square. Applying this to consecutive prime powers gives a tower map.
(2) The constant-ring comparison is invertible, by
`prop-weil-pbc-proetale-constant-ring-map`. Transport the inverse-image action
along its inverse; constants represented by integers act by integer multiples. The
constant class of `N` is zero, so `N` kills every section of the inverse image. The
unique constant `Z/N` action on torsion sheaves is therefore this transported action.
An additive root comparison is linear for these actions by
`definition-tate-twists`.
Substitution of `c(a)` gives semilinearity for every local scalar, including nonconstant
ones. (3) Use `lem-weil-proetale-isomorphism-inverse-image`: for an isomorphism the
distinguished comma object `(u,id)` computes inverse
image before sheafification; the transported presheaf is already a sheaf since coverings
and overlaps are unchanged. At that object the adjunct formula is pullback along the
identity on the underlying scheme. Thus the root comparison is the identity under the
specified identification and is an isomorphism. No invertibility of `N` is needed. -/
theorem proEtaleRootsOfUnityInverseImageIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ (N N' : ℕ) (hN : 0 < N) (hN' : 0 < N') (h : N ∣ N'),
      (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
            (proEtaleRootsOfUnityTransition Y N N' hN hN' h) ≫
          proEtaleRootsOfUnityInverseImageMap f N =
        proEtaleRootsOfUnityInverseImageMap f N' ≫
          proEtaleRootsOfUnityTransition X N N' hN hN' h) ∧
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime),
      ∃ c : proEtaleRootsOfUnityTower Y ℓ hℓ ⋙
          proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} ⟶
          proEtaleRootsOfUnityTower X ℓ hℓ,
        ∀ r : ℕ, c.app (op r) = proEtaleRootsOfUnityInverseImageMap f (ℓ ^ (r + 1))) ∧
    (∀ (N : ℕ) (hN : 0 < N) (U : X.ProEtᵒᵖ)
      (a : (proEtaleRootsOfUnityInverseImageRing f N).obj.obj U)
      (x : ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (proEtaleRootsOfUnitySheaf Y N)).obj.obj U),
      (proEtaleRootsOfUnityInverseImageMap f N).hom.app U
          (@SMul.smul _ _ (proEtaleRootsOfUnityInverseImageAction f N hN U).toSMul a x) =
        @SMul.smul _ _ (torsionSheafModuleStructure.{u + 1} (ProEt.topology X) N hN
            (proEtaleRootsOfUnitySheaf X N) (proEtaleRootsOfUnity_nsmul X N) U).toSMul
          ((proEtaleConstantInverseImageMap f RingCat.{u + 1}
            (RingCat.of (ULift.{u + 1} (ZMod N)))).hom.app U a)
          ((proEtaleRootsOfUnityInverseImageMap f N).hom.app U x)) ∧
    (∀ (_hf : IsIso f) (N : ℕ) (_hN : 0 < N),
      IsIso (proEtaleRootsOfUnityInverseImageMap f N) ∧
        ∀ (U : X.ProEtᵒᵖ)
          (x : ((proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
            (proEtaleRootsOfUnitySheaf Y N)).obj.obj U),
          proEtaleRootsOfUnitySections X N U
              ((proEtaleRootsOfUnityInverseImageMap f N).hom.app U x) =
            proEtaleRootsOfUnitySections Y N ((proEtaleIsoPostcompose f).op.obj U)
              (((proEtaleIsoInverseImageIdentification f AddCommGrpCat.{u + 1}).hom.app
                (proEtaleRootsOfUnitySheaf Y N)).app U x)) := by
  refine ⟨fun N N' hN hN' h ↦ roots_inverse_transition f N N' hN hN' h,
    fun ℓ hℓ ↦ roots_tower_map f ℓ hℓ, ?_, ?_⟩
  · intro N hN
    exact proEtaleRootsComparison_normalizedAction_linear f N hN
      (proEtaleRootsOfUnityInverseImageAction f N hN)
      (existsUnique_proEtaleRootsOfUnityInverseImageAction f N hN).exists.choose_spec
  · intro hf N _
    exact roots_iso_clause f N

end AlgebraicGeometry.Scheme
