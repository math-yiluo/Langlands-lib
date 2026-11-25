/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionSiteBasic
import WeilConjectures.CategoryTheory.InternalActionSite.TwistedModulePresheafEquivalence
import WeilConjectures.CategoryTheory.InternalActionSite.EquivariantModuleSheafificationReflector
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits

/-!
# Internal action site presentation

Source: the action-site construction, Stacks 00VH, 00WJ, 00YR, 03CY and 03DA
(blueprint: lem-sfb-internal-action-site-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C] (K : Cᵒᵖ ⥤ GrpCat.{u})

/-- The precise presentation data and all its required properties.
Source: action-site construction and Stacks 00VH, 00WJ, 00YR, 03CY, 03DA
(blueprint: lem-sfb-internal-action-site-presentation).

The equivalences are characterized on sections and maps. The two sheafification
comparisons commute with their units on underlying abelian presheaves; consequently
they specify the canonical comparisons. Creation of kernels and cokernels uses
Mathlib's ordinary module kernels and sheafified presheaf cokernels. -/
structure Presentation [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings)
    (S : Sheaf J.toGrothendieck CommRingCat.{u}) where
  /-- The equivalence before imposing the sheaf condition. -/
  presheafEquivalence : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj ≌
    PresheafOfModules.{u} (twistedRing K J hJ S).obj
  /-- Addition of component maps is preserved. -/
  presheaf_additive : presheafEquivalence.functor.Additive
  /-- The equivalence keeps the section modules. -/
  sections (M : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj) (X : C) :
    (presheafEquivalence.functor.obj M).obj (op (Object.mk (K := K) X)) ≃ₗ[
      (baseRing J.toGrothendieck S).obj.obj (op X)] M.val.obj (op X)
  /-- Twisted restriction is the action after ordinary restriction. -/
  restriction (M : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj)
      {X Y : C} (f : X ⟶ Y) (a : K.obj (op X))
      (m : (presheafEquivalence.functor.obj M).obj (op (Object.mk (K := K) Y))) :
    sections M X ((presheafEquivalence.functor.obj M).map (opArrow K f a) m) =
      M.action.act (op X) a (M.val.map f.op (sections M Y m))
  /-- Morphisms have the same sectionwise linear maps. -/
  morphisms {M N : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj} (f : M ⟶ N)
      (X : C) (m : (presheafEquivalence.functor.obj M).obj (op (Object.mk (K := K) X))) :
    sections N X ((presheafEquivalence.functor.map f).app _ m) =
      f.val.app (op X) (sections M X m)
  /-- The additive equivalence on sheaves. -/
  sheafEquivalence : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S) ≌
    ringedSiteModules (twistedRing K J hJ S)
  /-- The sheaf equivalence is additive. -/
  sheaf_additive : sheafEquivalence.functor.Additive
  /-- It is the restriction of the presheaf equivalence. -/
  underlying : inclusion J.toGrothendieck (baseRing J.toGrothendieck S) ⋙
      presheafEquivalence.functor ≅
    sheafEquivalence.functor ⋙ SheafOfModules.forget (twistedRing K J hJ S)
  /-- Inverse section modules, displaying restriction to normalized arrows. -/
  inverseSections (N : ringedSiteModules (twistedRing K J hJ S)) (X : C) :
    (sheafEquivalence.inverse.obj N).obj.val.obj (op X) ≃ₗ[
      (baseRing J.toGrothendieck S).obj.obj (op X)] N.val.obj (op (Object.mk (K := K) X))
  /-- The inverse restricts along (f,1). -/
  inverse_restriction (N : ringedSiteModules (twistedRing K J hJ S))
      {X Y : C} (f : X ⟶ Y)
      (m : (sheafEquivalence.inverse.obj N).obj.val.obj (op Y)) :
    inverseSections N X ((sheafEquivalence.inverse.obj N).obj.val.map f.op m) =
      N.val.map (opArrow K f 1) (inverseSections N Y m)
  /-- The inverse recovers the action from (1,a). -/
  inverse_action (N : ringedSiteModules (twistedRing K J hJ S)) (X : C)
      (a : K.obj (op X)) (m : (sheafEquivalence.inverse.obj N).obj.val.obj (op X)) :
    inverseSections N X ((sheafEquivalence.inverse.obj N).obj.action.act (op X) a m) =
      N.val.map (opArrow K (𝟙 X) a) (inverseSections N X m)
  /-- Inverse section identifications are natural in module morphisms. -/
  inverse_morphisms {M N : ringedSiteModules (twistedRing K J hJ S)} (f : M ⟶ N)
      (X : C) (m : (sheafEquivalence.inverse.obj M).obj.val.obj (op X)) :
    inverseSections N X ((sheafEquivalence.inverse.map f).hom.val.app (op X) m) =
      f.val.app (op (Object.mk (K := K) X)) (inverseSections M X m)
  /-- Module sheafification equipped with the induced group action. -/
  equivariantSheafification : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj ⥤
    EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S)
  /-- Its universal property is among equivariant maps. -/
  adjunction : equivariantSheafification ⊣ inclusion J.toGrothendieck (baseRing J.toGrothendieck S)
  /-- After forgetting the action it is ordinary module sheafification on C. -/
  baseComparison : equivariantSheafification ⋙
      forgetSheaf J.toGrothendieck (baseRing J.toGrothendieck S) ≅
    forgetPresheaf ⋙ PresheafOfModules.sheafification (𝟙 (baseRing J.toGrothendieck S).obj)
  /-- The comparison keeps the ordinary sheafification unit. -/
  base_unit (M : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj) :
    (PresheafOfModules.toPresheaf (baseRing J.toGrothendieck S).obj).map
        (forgetPresheaf.map (adjunction.unit.app M)) ≫
      ((SheafOfModules.toSheaf (baseRing J.toGrothendieck S)).map (baseComparison.hom.app M)).hom =
        toSheafify J.toGrothendieck M.val.presheaf
  /-- Sheafification on the action site agrees with equivariant sheafification. -/
  siteComparison : presheafEquivalence.functor ⋙
      PresheafOfModules.sheafification (𝟙 (twistedRing K J hJ S).obj) ≅
    equivariantSheafification ⋙ sheafEquivalence.functor
  /-- This comparison too is the canonical one commuting with the unit. -/
  site_unit (M : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj) :
    (PresheafOfModules.toPresheaf (twistedRing K J hJ S).obj).map
        (presheafEquivalence.functor.map (adjunction.unit.app M) ≫
          underlying.hom.app (equivariantSheafification.obj M)) =
      toSheafify (topology K J) (presheafEquivalence.functor.obj M).presheaf ≫
        ((SheafOfModules.toSheaf (twistedRing K J hJ S)).map
          (siteComparison.hom.app M)).hom
  /-- Forgetting the group creates kernels. -/
  createsKernels
      (M N : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S))
      (f : M ⟶ N) :
    Nonempty (CreatesLimit (parallelPair f 0)
      (forgetSheaf J.toGrothendieck (baseRing J.toGrothendieck S)))
  /-- Forgetting the group creates cokernels. -/
  createsCokernels
      (M N : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S))
      (f : M ⟶ N) :
    Nonempty (CreatesColimit (parallelPair f 0)
      (forgetSheaf J.toGrothendieck (baseRing J.toGrothendieck S)))
  /-- Zero is detected after restricting to the base site. -/
  zero_iff (N : ringedSiteModules (twistedRing K J hJ S)) :
    IsZero N ↔ IsZero ((forgetSheaf J.toGrothendieck (baseRing J.toGrothendieck S)).obj
      (sheafEquivalence.inverse.obj N))

private theorem cast_apply {A : Type u} {B : Type u} [Ring A] [Ring B]
    {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (hm : M = M') (hn : N = N') (f : M → N) (g : M' → N') (h : HEq f g) (m : M) :
    (eqToIso hn).hom (f m) = g ((eqToIso hm).hom m) := by
  cases hm
  cases hn
  cases h
  rfl

private def comparisonIso {A B : Type*} [Category A] [Category B]
    (F G : A ⥤ B) (ho : ∀ X, F.obj X = G.obj X)
    (hm : ∀ {X Y} (f : X ⟶ Y), HEq (F.map f) (G.map f)) : F ≅ G :=
  NatIso.ofComponents (fun X ↦ eqToIso (ho X)) (fun {X Y} f ↦ by
    change F.map f ≫ eqToHom (ho Y) = eqToHom (ho X) ≫ G.map f
    rw [comp_eqToHom_iff]
    simpa only [Category.assoc] using
      (conj_eqToHom_iff_heq (F.map f) (G.map f) (ho X) (ho Y)).2 (hm f))

private theorem preservesColimits_reflection {A B D : Type*}
    [Category A] [Category B] [Category D]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) [G.Full] [G.Faithful]
    (V : B ⥤ D) {I : Type*} [Category* I]
    [HasColimitsOfShape I A] [PreservesColimitsOfShape I (F ⋙ V)] :
    PreservesColimitsOfShape I V := by
  let := adj.isLeftAdjoint
  constructor
  intro T
  have : PreservesColimit ((T ⋙ G) ⋙ F) V :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves F (colimit.isColimit (T ⋙ G)))
      (isColimitOfPreserves (F ⋙ V) (colimit.isColimit (T ⋙ G)))
  let : PreservesColimit (T ⋙ G ⋙ F) V :=
    preservesColimit_of_iso_diagram V (Functor.associator T G F)
  exact preservesColimit_of_iso_diagram V
    (Functor.isoWhiskerLeft T (asIso adj.counit))

private theorem forgetPresheaf_reflects {R : Cᵒᵖ ⥤ RingCat.{u}} :
    (forgetPresheaf (K := K) (R := R)).ReflectsIsomorphisms := by
  constructor
  intro M N f hf
  have : IsIso f.val := hf
  let g : N ⟶ M := ⟨inv f.val, by
    intro X a m
    have hfm : Function.Injective (f.val.app X) := by
      intro x y h
      have := congrArg (fun q ↦ (inv f.val).app X q) h
      simpa only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app, IsIso.hom_inv_id,
        PresheafOfModules.id_app, ModuleCat.id_apply] using this
    apply hfm
    simpa only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app, IsIso.inv_hom_id,
      PresheafOfModules.id_app, ModuleCat.id_apply] using
      (f.property X a ((inv f.val).app X m)).symm⟩
  exact ⟨⟨g, by apply Subtype.ext; exact IsIso.hom_inv_id f.val,
    by apply Subtype.ext; exact IsIso.inv_hom_id f.val⟩⟩

/-- Internal actions are modules on the displayed twisted-arrow ringed site,
compatibly with sheafification, kernels, cokernels and detection of zero.

Source: agent-formulated categorical input to main-20261015,
sk-thm-sf-ctf-stability-direct-images, paragraph (3)
(blueprint: lem-sfb-internal-action-site-presentation).

Proof: construct the category with labels b g*a; associativity is functoriality
of the group sheaf. The pullback of (f,a),(g,b) has legs (p,1) and
(q,p*a (q*b)^-1); the cone equation determines its unique factor. These pullbacks
give covering pullbacks by the base covering-pullback axiom. Projection also
gives isomorphism covers. A sieve contains (f,a) exactly when it contains (f,1),
by invertibility of (1,a); its label-1 arrows form a base sieve. The generated
topology is precisely the sieves whose label-1 sieve is J-covering, by transporting
the Grothendieck axioms and comparing normalized generators in both directions.
The image precoverage need not be closed under bind. Normalize covers using (1,a_i), whose
inverses have labels a_i^-1. Extend a module by restrictions a f*m; naturality
of its action gives contravariant composition. Recover the ordinary restrictions
from (f,1) and the action from (1,a); these constructions are inverse on objects
and maps and preserve addition. On normalized covers the matching diagrams are
the original matching diagrams, so this equivalence restricts to sheaves and
makes the coefficient presheaf a sheaf. For sheafification, sheafify K times P
to P on underlying sets. Finite-product preservation (Stacks 00WJ) and the
underlying-set comparison (00YR) produce the action on P-sharp. Sheafifying
the action-law and linearity diagrams proves its laws. Maps from P extend
uniquely and equivariantly since maps from K times P-sharp are determined by
their composites with the sheafification unit. The resulting reflection is
therefore module sheafification on the twisted site (03CY), giving the two
unit-compatible natural comparisons. Kernels are sectionwise stable under the
action, and the sectionwise cokernel inherits an action whose sheafification
has the equivariant cokernel universal property (03DA). Thus forgetting creates
both. Finally all section modules are unchanged, so zero is detected on C.
The construction covers trivial groups, zero rings, and empty covers. -/
theorem presentation [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings)
    (hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u}))
    (S : Sheaf J.toGrothendieck CommRingCat.{u}) : Nonempty (Presentation K J hJ S) := by
  classical
  obtain ⟨_, e, hea, _, hsec, hres, hmap, hisec, hires, hiact, himap, _, _, _, _, _, _, _,
    es, hesa, heisa, hso, hsm, hio, hsmap⟩ := module_presheaf_equivalence K J hJ hK S
  obtain ⟨_, F, adj, bc, hbc⟩ :=
    equivariantModuleSheafification_reflector J.toGrothendieck K hK S
  let V := forgetPresheaf (K := K) (R := (baseRing J.toGrothendieck S).obj)
  let U := forgetSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S)
  let ev (X : Cᵒᵖ) : e.functor ⋙ PresheafOfModules.evaluation
      (twistedRing K J hJ S).obj (op (Object.mk (K := K) X.unop)) ≅
      V ⋙ PresheafOfModules.evaluation (baseRing J.toGrothendieck S).obj X :=
    NatIso.ofComponents (fun M ↦ eqToIso (hsec M X.unop)) (fun {M N} f ↦ by
      ext m
      exact cast_apply (hsec M X.unop) (hsec N X.unop) _ _ (hmap M N f X.unop) m)
  have vpL {I : Type} [SmallCategory I] : PreservesLimitsOfShape I V := by
    constructor
    intro T
    constructor
    intro c hc
    refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦ ?_)⟩
    let : PreservesLimit T (V ⋙ PresheafOfModules.evaluation _ X) :=
      preservesLimit_of_natIso T (ev X)
    exact isLimitOfPreserves (V ⋙ PresheafOfModules.evaluation _ X) hc
  have vpC {I : Type} [SmallCategory I] : PreservesColimitsOfShape I V := by
    constructor
    intro T
    constructor
    intro c hc
    refine ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ ?_)⟩
    let : PreservesColimit T (V ⋙ PresheafOfModules.evaluation _ X) :=
      preservesColimit_of_natIso T (ev X)
    exact isColimitOfPreserves (V ⋙ PresheafOfModules.evaluation _ X) hc
  let : V.ReflectsIsomorphisms := forgetPresheaf_reflects K
  let : (U ⋙ SheafOfModules.forget (baseRing J.toGrothendieck S)).ReflectsIsomorphisms :=
    by
      change ((ObjectProperty.ι _) ⋙ V).ReflectsIsomorphisms
      infer_instance
  let : U.ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_comp U (SheafOfModules.forget _)
  let : U.Faithful := ⟨fun h ↦ by
    ext1
    apply Subtype.ext
    exact congrArg SheafOfModules.Hom.val h⟩
  let : U.Additive := ⟨by intros; rfl⟩
  let : es.inverse.Additive := heisa
  let : (inclusion (K := K) J.toGrothendieck (baseRing J.toGrothendieck S)).Full :=
    inferInstanceAs ((ObjectProperty.ι _).Full)
  let : (inclusion (K := K) J.toGrothendieck (baseRing J.toGrothendieck S)).Faithful :=
    inferInstanceAs ((ObjectProperty.ι _).Faithful)
  let : F.IsLeftAdjoint := adj.isLeftAdjoint
  let : (inclusion J.toGrothendieck (baseRing J.toGrothendieck S)).IsRightAdjoint :=
    adj.isRightAdjoint
  let : HasLimitsOfShape WalkingParallelPair
      (EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S)) :=
    Adjunction.hasLimitsOfShape_of_equivalence es.functor
  let : HasColimitsOfShape WalkingParallelPair
      (EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S)) :=
    Adjunction.hasColimitsOfShape_of_equivalence es.functor
  let : HasColimitsOfShape WalkingParallelPair
      (EquivariantPresheaf K (baseRing J.toGrothendieck S).obj) :=
    Adjunction.hasColimitsOfShape_of_equivalence e.functor
  let : PreservesLimitsOfShape WalkingParallelPair V := vpL
  let : PreservesColimitsOfShape WalkingParallelPair V := vpC
  let : PreservesLimitsOfShape WalkingParallelPair
      (U ⋙ SheafOfModules.forget (baseRing J.toGrothendieck S)) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingParallelPair
      (inclusion J.toGrothendieck (baseRing J.toGrothendieck S) ⋙ V))
  let : PreservesLimitsOfShape WalkingParallelPair U :=
    preservesLimitsOfShape_of_reflects_of_preserves U (SheafOfModules.forget _)
  let : PreservesColimitsOfShape WalkingParallelPair (F ⋙ U) :=
    preservesColimitsOfShape_of_natIso bc.symm
  let : PreservesColimitsOfShape WalkingParallelPair U :=
    preservesColimits_reflection adj U
  let under : inclusion J.toGrothendieck (baseRing J.toGrothendieck S) ⋙ e.functor ≅
      es.functor ⋙ SheafOfModules.forget (twistedRing K J hJ S) :=
    comparisonIso _ _ (fun M ↦ (hso M).symm) (fun {M N} f ↦ (hsm M N f).symm)
  let sadj : PresheafOfModules.sheafification (𝟙 (twistedRing K J hJ S).obj) ⊣
      SheafOfModules.forget (twistedRing K J hJ S) :=
    PresheafOfModules.sheafificationAdjunction (𝟙 (twistedRing K J hJ S).obj)
  let beta := TwoSquare.mk _ _ _ _ under.hom
  let alpha := (mateEquiv adj sadj).symm beta
  have halpha : IsIso alpha := by
    let gamma := mateEquiv es.toAdjunction e.toAdjunction beta
    have : IsIso gamma := by
      dsimp [gamma, mateEquiv]
      infer_instance
    have he := iterated_mateEquiv_conjugateEquiv_symm adj sadj
      e.toAdjunction es.toAdjunction gamma
    have hi : IsIso (((mateEquiv adj sadj).symm
        ((mateEquiv es.toAdjunction e.toAdjunction).symm gamma))) := by
      rw [he]
      change IsIso ((conjugateEquiv (adj.comp es.toAdjunction)
        (e.toAdjunction.comp sadj)).symm gamma)
      infer_instance
    simpa only [gamma, Equiv.symm_apply_apply] using hi
  let sc := asIso alpha
  refine ⟨{
    presheafEquivalence := e
    presheaf_additive := hea
    sections := fun M X ↦ (eqToIso (hsec M X)).toLinearEquiv
    restriction := ?_
    morphisms := ?_
    sheafEquivalence := es
    sheaf_additive := hesa
    underlying := under
    inverseSections := fun N X ↦ (eqToIso
      ((congrArg (fun P ↦ P.val.obj (op X)) (hio N)).trans (hisec N.val X))).toLinearEquiv
    inverse_restriction := ?_
    inverse_action := ?_
    inverse_morphisms := ?_
    equivariantSheafification := F
    adjunction := adj
    baseComparison := bc
    base_unit := hbc
    siteComparison := sc
    site_unit := ?_
    createsKernels := ?_
    createsCokernels := ?_
    zero_iff := ?_ }⟩
  · intro M X Y f a m
    exact cast_apply (hsec M Y) (hsec M X) _ _ (hres M X Y f a) m
  · intro M N f X m
    exact cast_apply (hsec M X) (hsec N X) _ _ (hmap M N f X) m
  · intro N X Y f m
    have helper : ∀ (Q : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj)
        (hi : Q = e.inverse.obj N.val) (m : Q.val.obj (op Y)),
        (eqToIso ((congrArg (fun P ↦ P.val.obj (op X)) hi).trans (hisec N.val X))).hom
            (Q.val.map f.op m) =
          N.val.map (opArrow K f 1)
            ((eqToIso ((congrArg (fun P ↦ P.val.obj (op Y)) hi).trans
              (hisec N.val Y))).hom m) := by
      intro Q hi
      subst Q
      exact fun m ↦ cast_apply (hisec N.val Y) (hisec N.val X) _ _
        (hires N.val X Y f) m
    exact helper _ (hio N) m
  · intro N X a m
    have helper : ∀ (Q : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj)
        (hi : Q = e.inverse.obj N.val) (m : Q.val.obj (op X)),
        (eqToIso ((congrArg (fun P ↦ P.val.obj (op X)) hi).trans (hisec N.val X))).hom
            (Q.action.act (op X) a m) =
          N.val.map (opArrow K (𝟙 X) a)
            ((eqToIso ((congrArg (fun P ↦ P.val.obj (op X)) hi).trans
              (hisec N.val X))).hom m) := by
      intro Q hi
      subst Q
      exact fun m ↦ cast_apply (hisec N.val X) (hisec N.val X) _ _
        (hiact N.val X a) m
    exact helper _ (hio N) m
  · intro M N f X m
    have helper : ∀ (Q Q' : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj)
        (hm : Q = e.inverse.obj M.val) (hn : Q' = e.inverse.obj N.val)
        (g : Q ⟶ Q') (hg : HEq g (e.inverse.map f.val)) (m : Q.val.obj (op X)),
        (eqToIso ((congrArg (fun P ↦ P.val.obj (op X)) hn).trans (hisec N.val X))).hom
            (g.val.app (op X) m) =
          f.val.app (op (Object.mk (K := K) X))
            ((eqToIso ((congrArg (fun P ↦ P.val.obj (op X)) hm).trans
              (hisec M.val X))).hom m) := by
      intro Q Q' hm hn g hg
      subst Q
      subst Q'
      cases hg
      exact fun m ↦ cast_apply (hisec M.val X) (hisec N.val X) _ _
        (himap M.val N.val f.val X) m
    exact helper _ _ (hio M) (hio N) (es.inverse.map f).hom (hsmap M N f) m
  · intro M
    have h := unit_mateEquiv_symm adj sadj beta M
    exact (congrArg (PresheafOfModules.toPresheaf _).map h).trans (by
      simp only [Functor.map_comp]
      rfl)
  · intro M N f
    exact ⟨createsLimitOfReflectsIsomorphismsOfPreserves⟩
  · intro M N f
    exact ⟨createsColimitOfReflectsIsomorphismsOfPreserves⟩
  · intro N
    rw [IsZero.iff_id_eq_zero, IsZero.iff_id_eq_zero, ← U.map_id,
      U.map_eq_zero_iff, ← es.inverse.map_id, es.inverse.map_eq_zero_iff]

end CategoryTheory.InternalActionSite
