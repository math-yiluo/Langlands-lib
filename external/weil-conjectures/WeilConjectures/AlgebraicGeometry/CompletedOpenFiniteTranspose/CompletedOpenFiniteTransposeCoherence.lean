/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerRealizationComparisons
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Sheafification
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearEvaluationDerivedAdjunction
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.CategoryTheory.ExactCube
import WeilConjectures.AlgebraicGeometry.Constant.ConstantTowerSquareNormalization
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization

/-! # Finite reduction and the strict open transpose

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md, finite-exchange paragraph;
Stacks 03DI, 03CY, 03DJ, 06YY and 07A4.
(blueprint: lem-cbc-completed-open-finite-transpose-coherence).

All objects below belong to derived categories of strict towers. The published
section-normalized comparisons are reused, including their quotient transitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
universe t
namespace AlgebraicGeometry.Scheme
section RestoredRestrictionSquare
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleRingCompositeCoefficients exchangeModuleComposition

section
variable {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW SW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ SZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (aV : RV ⟶ SV) (aW : RW ⟶ SW) (aZ : RZ ⟶ SZ)
    (ckR : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (chR : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ)
    (ckS : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj SV ≅ SW)
    (chS : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj SW ≅ SZ)
    (hk : ckR.hom ≫ aW = (proEtaleSheafInverseImage k CommRingCat.{u + 1}).map aV ≫ ckS.hom)
    (hh : chR.hom ≫ aZ = (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map aW ≫ chS.hom)

include hk hh in
private theorem restrictionComposite_comm :
    (proEtaleRingCompositeCoefficients h k RV RW RZ ckR chR).hom ≫ aZ =
      (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).map aV ≫
        (proEtaleRingCompositeCoefficients h k SV SW SZ ckS chS).hom := by
  simp only [proEtaleRingCompositeCoefficients, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [hh, ← Functor.map_comp_assoc, hk, Functor.map_comp]
  simp only [Category.assoc, Iso.app_hom]
  rw [← reassoc_of% ((proEtaleRingInverseImageComp h k).hom.naturality aV)]




private def restrictionRComp
    (T0 : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (T1 : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (T2 : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c1 : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj T0 ≅ T1)
    (c2 : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj T1 ≅ T2) :=
  conjugateIsoEquiv
    ((proEtaleRingModuleAdjunction k T0 T1 c1).comp
      (proEtaleRingModuleAdjunction h T1 T2 c2))
    (proEtaleRingModuleAdjunction (h ≫ k) T0 T2
      (proEtaleRingCompositeCoefficients h k T0 T1 T2 c1 c2))
    (exchangeModuleComposition h k T0 T1 T2 c1 c2)

private theorem restrictionRComp_apply
    (T0 : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (T1 : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (T2 : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c1 : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj T0 ≅ T1)
    (c2 : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj T1 ≅ T2)
    (N : proEtaleRingModules Z T2) (U : V.ProEt)
    (m : ((proEtaleRingModuleDirectImage h T1 T2 c2 ⋙
      proEtaleRingModuleDirectImage k T0 T1 c1).obj N).val.obj (op U)) :
    ((restrictionRComp h k T0 T1 T2 c1 c2).hom.app N).val.app (op U) m =
      N.val.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U).op m :=
  by
    simpa only [restrictionRComp, exchangeModuleComposition] using
      (exchangeModuleComposition_existsUnique h k T0 T1 T2 c1 c2).choose_spec.1 N U m

private theorem restrictionDirect_apply
    {U T : Scheme.{u}} (f : U ⟶ T)
    (R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (R' S' : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (a : R ⟶ S) (b : R' ⟶ S')
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ R')
    (c' : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj S ≅ S')
    (hc : c.hom ≫ b = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map a ≫ c'.hom)
    (N : proEtaleRingModules U S') (Y : T.ProEtᵒᵖ)
    (n : N.val.obj ((proEtaleBaseChange f).op.obj Y)) :
    ((proEtaleRingRestrictionDirectImage f R S R' S' a b c c' hc).hom.app N).val.app Y n = n :=
  (proEtaleRingRestrictionDirectImage_existsUnique f R S R' S' a b c c' hc).choose_spec.1 N Y n

private theorem restrictionComparison_comp
    (M : proEtaleRingModules V SV) :
    (exchangeModuleComposition h k RV RW RZ ckR chR).hom.app
        ((proEtaleRingRestrictScalars aV).obj M) ≫
      (proEtaleRingModulePullback h RW RZ chR).map
        ((proEtaleRingRestrictionPullbackInv k RV SV RW SW aV aW ckR ckS hk).app M) ≫
      (proEtaleRingRestrictionPullbackInv h RW SW RZ SZ aW aZ chR chS hh).app
        ((proEtaleRingModulePullback k SV SW ckS).obj M) =
    (proEtaleRingRestrictionPullbackInv (h ≫ k) RV SV RZ SZ aV aZ
        (proEtaleRingCompositeCoefficients h k RV RW RZ ckR chR)
        (proEtaleRingCompositeCoefficients h k SV SW SZ ckS chS)
        (restrictionComposite_comm h k RV SV RW SW RZ SZ aV aW aZ ckR chR ckS chS hk hh)).app M ≫
      (proEtaleRingRestrictScalars aZ).map
        ((exchangeModuleComposition h k SV SW SZ ckS chS).hom.app M) := by
  let q := (TwoSquare.mk _ _ _ _
    (proEtaleRingRestrictionPullbackInv k RV SV RW SW aV aW ckR ckS hk)).vComp
    (TwoSquare.mk _ _ _ _
      (proEtaleRingRestrictionPullbackInv h RW SW RZ SZ aW aZ chR chS hh))
  let r := TwoSquare.mk _ _ _ _
    (proEtaleRingRestrictionPullbackInv (h ≫ k) RV SV RZ SZ aV aZ
      (proEtaleRingCompositeCoefficients h k RV RW RZ ckR chR)
      (proEtaleRingCompositeCoefficients h k SV SW SZ ckS chS)
      (restrictionComposite_comm h k RV SV RW SW RZ SZ aV aW aZ ckR chR ckS chS hk hh))
  have hc : q.whiskerRight (exchangeModuleComposition h k RV RW RZ ckR chR).hom =
      r.whiskerLeft (exchangeModuleComposition h k SV SW SZ ckS chS).hom := by
    apply AlgebraicGeometry.ProEtale.mateSquare
      ((proEtaleRingModuleAdjunction k SV SW ckS).comp
        (proEtaleRingModuleAdjunction h SW SZ chS))
      (proEtaleRingModuleAdjunction (h ≫ k) SV SZ
        (proEtaleRingCompositeCoefficients h k SV SW SZ ckS chS))
      ((proEtaleRingModuleAdjunction k RV RW ckR).comp
        (proEtaleRingModuleAdjunction h RW RZ chR))
      (proEtaleRingModuleAdjunction (h ≫ k) RV RZ
        (proEtaleRingCompositeCoefficients h k RV RW RZ ckR chR))
    dsimp only [q]
    rw [mateEquiv_hcomp]
    have hk' := restrictionPullback_mate k RV SV RW SW aV aW ckR ckS hk
    have hh' := restrictionPullback_mate h RW SW RZ SZ aW aZ chR chS hh
    have hc' := restrictionPullback_mate (h ≫ k) RV SV RZ SZ aV aZ
      (proEtaleRingCompositeCoefficients h k RV RW RZ ckR chR)
      (proEtaleRingCompositeCoefficients h k SV SW SZ ckS chS)
      (restrictionComposite_comm h k RV SV RW SW RZ SZ aV aW aZ ckR chR ckS chS hk hh)
    change _ = _ at hk' hh' hc'
    have hkq : mateEquiv (proEtaleRingModuleAdjunction k SV SW ckS)
        (proEtaleRingModuleAdjunction k RV RW ckR)
        (TwoSquare.mk _ _ _ _
          (proEtaleRingRestrictionPullbackInv k RV SV RW SW aV aW ckR ckS hk)) =
        TwoSquare.mk _ _ _ _
          (proEtaleRingRestrictionDirectImage k RV SV RW SW aV aW ckR ckS hk).hom := by
      refine NatTrans.ext (funext fun N ↦ ?_)
      exact congrArg (fun z ↦ z.app N) hk'
    have hhq : mateEquiv (proEtaleRingModuleAdjunction h SW SZ chS)
        (proEtaleRingModuleAdjunction h RW RZ chR)
        (TwoSquare.mk _ _ _ _
          (proEtaleRingRestrictionPullbackInv h RW SW RZ SZ aW aZ chR chS hh)) =
        TwoSquare.mk _ _ _ _
          (proEtaleRingRestrictionDirectImage h RW SW RZ SZ aW aZ chR chS hh).hom := by
      refine NatTrans.ext (funext fun N ↦ ?_)
      exact congrArg (fun z ↦ z.app N) hh'
    have hcq : mateEquiv
        (proEtaleRingModuleAdjunction (h ≫ k) SV SZ
          (proEtaleRingCompositeCoefficients h k SV SW SZ ckS chS))
        (proEtaleRingModuleAdjunction (h ≫ k) RV RZ
          (proEtaleRingCompositeCoefficients h k RV RW RZ ckR chR))
        r = TwoSquare.mk _ _ _ _
          (proEtaleRingRestrictionDirectImage (h ≫ k) RV SV RZ SZ aV aZ
            (proEtaleRingCompositeCoefficients h k RV RW RZ ckR chR)
            (proEtaleRingCompositeCoefficients h k SV SW SZ ckS chS)
            (restrictionComposite_comm h k RV SV RW SW RZ SZ
              aV aW aZ ckR chR ckS chS hk hh)).hom := by
      refine NatTrans.ext (funext fun N ↦ ?_)
      exact congrArg (fun z ↦ z.app N) hc'
    rw [hkq, hhq, hcq]
    change ((TwoSquare.mk _ _ _ _ _).hComp (TwoSquare.mk _ _ _ _ _)).whiskerBottom
        (restrictionRComp h k RV RW RZ ckR chR).hom =
      (TwoSquare.mk _ _ _ _ _).whiskerTop (restrictionRComp h k SV SW SZ ckS chS).hom
    refine NatTrans.ext (funext fun N ↦ ?_)
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro Y
    ext n
    simp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, SheafOfModules.comp_val, PresheafOfModules.comp_app]
    simp only [ModuleCat.comp_apply]
    erw [restrictionDirect_apply k RV SV RW SW aV aW ckR ckS hk _ Y n]
    change ((restrictionRComp h k RV RW RZ ckR chR).hom.app
        ((proEtaleRingRestrictScalars aZ).obj N)).val.app Y
        (((proEtaleRingRestrictionDirectImage h RW SW RZ SZ aW aZ chR chS hh).hom.app
          N).val.app ((proEtaleBaseChange k).op.obj Y) n) =
      ((proEtaleRingRestrictionDirectImage (h ≫ k) RV SV RZ SZ aV aZ
        (proEtaleRingCompositeCoefficients h k RV RW RZ ckR chR)
        (proEtaleRingCompositeCoefficients h k SV SW SZ ckS chS)
        (restrictionComposite_comm h k RV SV RW SW RZ SZ aV aW aZ ckR chR ckS chS hk hh)).hom.app
          N).val.app Y (((restrictionRComp h k SV SW SZ ckS chS).hom.app N).val.app Y n)
    erw [restrictionDirect_apply h RW SW RZ SZ aW aZ chR chS hh N _ n,
      restrictionDirect_apply (h ≫ k) RV SV RZ SZ aV aZ _ _ _ N Y _]
    obtain ⟨Y⟩ := Y
    erw [restrictionRComp_apply h k RV RW RZ ckR chR
        ((proEtaleRingRestrictScalars aZ).obj N) Y n,
      restrictionRComp_apply h k SV SW SZ ckS chS N Y n]
    rfl
  have hm := congrArg (fun z ↦ z.app M) hc
  simpa only [q, r, TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc] using hm
end

private theorem compatible_sigma_eq {ι : Type*} {B C : ι → Type*}
    (P : ∀ i, B i → C i → Prop) {i j : ι}
    {b : B i} {b' : B j} {c : C i} {c' : C j}
    (h : i = j) (hb : HEq b b') (hc : HEq c c')
    (p : P i b c) (q : P j b' c') :
    (⟨i, ⟨(b, c), p⟩⟩ : Σ k, {v : B k × C k // P k v.1 v.2}) =
      ⟨j, ⟨(b', c'), q⟩⟩ := by
  subst j
  cases hb
  cases hc
  rfl

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

/-- Restriction of compatible coefficient systems respects the normalized ordinary
pullback-square compositor. This involves neither derived functors nor exchange mates.
Source: Stacks Project, Tags 03D7, 03D8 and 0D6D
(blueprint: lem-weil-pbc-ring-restriction-pullback-square).

Proof: take right-adjoint mates of the restriction/pullback comparisons along each
of the two composable paths. The ordinary restriction/direct-image comparisons are
identity on all sections. The right-adjoint conjugate of exchangeModuleComposition
is restriction along Over.pullbackComp, by its normalization. Restriction of scalars
changes neither sections nor these restriction maps. Consequently the two composites
involving direct-image composition and scalar restriction agree on every section.
The mate-pasting laws and injectivity of the mate bijections give compatibility with
each inverse-image compositor. Paste the two resulting equations across the equality
of the coefficient-decorated composite scheme morphisms supplied by the two coherent
ringed squares. Equality transport is natural in the scalar map; its proof components
agree by proof irrelevance. Cancel the first compositor to obtain the displayed
square. The argument applies to arbitrary coefficients, zero rings and empty schemes. -/
private theorem proEtaleRingRestriction_square
    (r s : StrictTowerRingedSquare sq)
    (aY : r.RY ⟶ s.RY) (aX : r.RX ⟶ s.RX)
    (aY' : r.RY' ⟶ s.RY') (aX' : r.RX' ⟶ s.RX')
    (hf : r.cf.hom ≫ aX =
      (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map aY ≫ s.cf.hom)
    (hg : r.cg.hom ≫ aY' =
      (proEtaleSheafInverseImage g CommRingCat.{t + 1}).map aY ≫ s.cg.hom)
    (hg' : r.cg'.hom ≫ aX' =
      (proEtaleSheafInverseImage g' CommRingCat.{t + 1}).map aX ≫ s.cg'.hom)
    (hf' : r.cf'.hom ≫ aX' =
      (proEtaleSheafInverseImage f' CommRingCat.{t + 1}).map aY' ≫ s.cf'.hom)
    (M : proEtaleRingModules Y s.RY) :
    r.exchangeModuleSquare.hom.app ((proEtaleRingRestrictScalars aY).obj M) ≫
      (proEtaleRingModulePullback g' r.RX r.RX' r.cg').map
        ((proEtaleRingRestrictionPullbackInv f r.RY s.RY r.RX s.RX
          aY aX r.cf s.cf hf).app M) ≫
      (proEtaleRingRestrictionPullbackInv g' r.RX s.RX r.RX' s.RX'
        aX aX' r.cg' s.cg' hg').app
        ((proEtaleRingModulePullback f s.RY s.RX s.cf).obj M) =
    (proEtaleRingModulePullback f' r.RY' r.RX' r.cf').map
        ((proEtaleRingRestrictionPullbackInv g r.RY s.RY r.RY' s.RY'
          aY aY' r.cg s.cg hg).app M) ≫
      (proEtaleRingRestrictionPullbackInv f' r.RY' s.RY' r.RX' s.RX'
        aY' aX' r.cf' s.cf' hf').app
        ((proEtaleRingModulePullback g s.RY s.RY' s.cg).obj M) ≫
      (proEtaleRingRestrictScalars aX').map (s.exchangeModuleSquare.hom.app M) := by
  let B (u : X' ⟶ Y) :=
    (proEtaleSheafInverseImage u CommRingCat.{t + 1}).obj r.RY ≅ r.RX'
  let C (u : X' ⟶ Y) :=
    (proEtaleSheafInverseImage u CommRingCat.{t + 1}).obj s.RY ≅ s.RX'
  let compatible (u : X' ⟶ Y) (b : B u) (c : C u) :=
    b.hom ≫ aX' = (proEtaleSheafInverseImage u CommRingCat.{t + 1}).map aY ≫ c.hom
  let E := Σ u : X' ⟶ Y, {v : B u × C u // compatible u v.1 v.2}
  let left : E := ⟨f' ≫ g, ⟨
    (proEtaleRingCompositeCoefficients f' g r.RY r.RY' r.RX' r.cg r.cf',
     proEtaleRingCompositeCoefficients f' g s.RY s.RY' s.RX' s.cg s.cf'),
    restrictionComposite_comm f' g r.RY s.RY r.RY' s.RY' r.RX' s.RX'
      aY aY' aX' r.cg r.cf' s.cg s.cf' hg hf'⟩⟩
  let right : E := ⟨g' ≫ f, ⟨
    (proEtaleRingCompositeCoefficients g' f r.RY r.RX r.RX' r.cf r.cg',
     proEtaleRingCompositeCoefficients g' f s.RY s.RX s.RX' s.cf s.cg'),
    restrictionComposite_comm g' f r.RY s.RY r.RX s.RX r.RX' s.RX'
      aY aX aX' r.cf r.cg' s.cf s.cg' hf hg'⟩⟩
  have h : left = right :=
    compatible_sigma_eq compatible sq.w.symm r.coherent.symm s.coherent.symm _ _
  let P (z : E) := proEtaleRingModulePullback z.1 r.RY r.RX' z.2.1.1
  let Q (z : E) := proEtaleRingModulePullback z.1 s.RY s.RX' z.2.1.2
  let q (z : E) := proEtaleRingRestrictionPullbackInv z.1 r.RY s.RY r.RX' s.RX'
    aY aX' z.2.1.1 z.2.1.2 z.2.2
  have hz : r.exchangeModuleSquare.symm =
      (exchangeModuleComposition g' f r.RY r.RX r.RX' r.cf r.cg').symm ≪≫
        eqToIso (congrArg P h.symm) ≪≫
        exchangeModuleComposition f' g r.RY r.RY' r.RX' r.cg r.cf' := by
    have he : congrArg P h.symm = congrArg
        (fun z : (Σ u : X' ⟶ Y, B u) ↦
          proEtaleRingModulePullback z.1 r.RY r.RX' z.2)
        r.exchangeCoefficients_eq.symm := rfl
    rw [he]
    apply Iso.ext
    simp only [StrictTowerRingedSquare.exchangeModuleSquare, Iso.symm_hom,
      Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, eqToIso.inv, eqToIso.hom]
  have hw : s.exchangeModuleSquare.symm =
      (exchangeModuleComposition g' f s.RY s.RX s.RX' s.cf s.cg').symm ≪≫
        eqToIso (congrArg Q h.symm) ≪≫
        exchangeModuleComposition f' g s.RY s.RY' s.RX' s.cg s.cf' := by
    have he : congrArg Q h.symm = congrArg
        (fun z : (Σ u : X' ⟶ Y, C u) ↦
          proEtaleRingModulePullback z.1 s.RY s.RX' z.2)
        s.exchangeCoefficients_eq.symm := rfl
    rw [he]
    apply Iso.ext
    simp only [StrictTowerRingedSquare.exchangeModuleSquare, Iso.symm_hom,
      Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, eqToIso.inv, eqToIso.hom]
  exact AlgebraicGeometry.ProEtale.pasteTransport P Q
    (proEtaleRingRestrictScalars aY) (proEtaleRingRestrictScalars aX') q h
    (exchangeModuleComposition f' g r.RY r.RY' r.RX' r.cg r.cf')
    (exchangeModuleComposition g' f r.RY r.RX r.RX' r.cf r.cg')
    (exchangeModuleComposition f' g s.RY s.RY' s.RX' s.cg s.cf')
    (exchangeModuleComposition g' f s.RY s.RX s.RX' s.cf s.cg')
    (Functor.whiskerRight
      (proEtaleRingRestrictionPullbackInv g r.RY s.RY r.RY' s.RY'
        aY aY' r.cg s.cg hg)
      (proEtaleRingModulePullback f' r.RY' r.RX' r.cf'))
    (Functor.whiskerLeft (proEtaleRingModulePullback g s.RY s.RY' s.cg)
      (proEtaleRingRestrictionPullbackInv f' r.RY' s.RY' r.RX' s.RX'
        aY' aX' r.cf' s.cf' hf'))
    (Functor.whiskerRight
      (proEtaleRingRestrictionPullbackInv f r.RY s.RY r.RX s.RX
        aY aX r.cf s.cf hf)
      (proEtaleRingModulePullback g' r.RX r.RX' r.cg'))
    (Functor.whiskerLeft (proEtaleRingModulePullback f s.RY s.RX s.cf)
      (proEtaleRingRestrictionPullbackInv g' r.RX s.RX r.RX' s.RX'
        aX aX' r.cg' s.cg' hg'))
    (restrictionComparison_comp f' g r.RY s.RY r.RY' s.RY' r.RX' s.RX'
      aY aY' aX' r.cg r.cf' s.cg s.cf' hg hf')
    (restrictionComparison_comp g' f r.RY s.RY r.RX s.RX r.RX' s.RX'
      aY aX aX' r.cf r.cg' s.cf s.cg' hf hg')
    r.exchangeModuleSquare.symm s.exchangeModuleSquare.symm hz hw M

private def termwiseSquareHom
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    (q : F ⋙ G ⟶ H ⋙ I) :
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj F ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj G ⟶
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj H ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj I where
  app M := Functor.whiskerLeft M q
  naturality {M N} a := by
    apply NatTrans.ext
    funext n
    exact q.naturality (a.app n)

private def termwiseSquareIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    (e : F ⋙ G ≅ H ⋙ I) :
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj F ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj G ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj H ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj I where
  hom := termwiseSquareHom e.hom
  inv := termwiseSquareHom e.inv
  hom_inv_id := by
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    exact e.hom_inv_id_app (M.obj n)
  inv_hom_id := by
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    exact e.inv_hom_id_app (M.obj n)

private theorem towerCube
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {R₀ : D₀ ⥤ C₀} {R₁ : D₁ ⥤ C₁} {R₂ : D₂ ⥤ C₂} {R₃ : D₃ ⥤ C₃}
    {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
    {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
    (qJ : R₀ ⋙ J ⟶ J' ⋙ R₁) (qH : R₁ ⋙ H ⟶ H' ⋙ R₃)
    (qG : R₀ ⋙ G ⟶ G' ⋙ R₂) (qI : R₂ ⋙ I ⟶ I' ⋙ R₃)
    (c : J ⋙ H ⟶ G ⋙ I) (d : J' ⋙ H' ⟶ G' ⋙ I')
    (hc : ∀ N, c.app (R₀.obj N) ≫ I.map (qG.app N) ≫ qI.app (G'.obj N) =
      H.map (qJ.app N) ≫ qH.app (J'.obj N) ≫ R₃.map (d.app N)) :
    Functor.whiskerLeft ((Functor.whiskeringRight ℕᵒᵖ _ _).obj R₀)
        (termwiseSquareHom c) ≫
      Functor.whiskerRight (termwiseSquareHom qG)
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj I) ≫
      Functor.whiskerLeft ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G')
        (termwiseSquareHom qI) =
    Functor.whiskerRight (termwiseSquareHom qJ)
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj H) ≫
      Functor.whiskerLeft ((Functor.whiskeringRight ℕᵒᵖ _ _).obj J')
        (termwiseSquareHom qH) ≫
      Functor.whiskerRight (termwiseSquareHom d)
        ((Functor.whiskeringRight ℕᵒᵖ _ _).obj R₃) := by
  apply NatTrans.ext
  funext N
  apply NatTrans.ext
  funext n
  exact hc (N.obj n)

-- Inferred proposition keeps the normalized termwise interfaces shared.
set_option linter.defProp false in
private def restrictionTowerCube_nat
    (r s : StrictTowerRingedSquare sq)
    (aY : r.RY ⟶ s.RY) (aX : r.RX ⟶ s.RX)
    (aY' : r.RY' ⟶ s.RY') (aX' : r.RX' ⟶ s.RX')
    (hf : r.cf.hom ≫ aX =
      (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map aY ≫ s.cf.hom)
    (hg : r.cg.hom ≫ aY' =
      (proEtaleSheafInverseImage g CommRingCat.{t + 1}).map aY ≫ s.cg.hom)
    (hg' : r.cg'.hom ≫ aX' =
      (proEtaleSheafInverseImage g' CommRingCat.{t + 1}).map aX ≫ s.cg'.hom)
    (hf' : r.cf'.hom ≫ aX' =
      (proEtaleSheafInverseImage f' CommRingCat.{t + 1}).map aY' ≫ s.cf'.hom) :=
  towerCube
    (C₀ := proEtaleRingModules Y r.RY)
    (C₁ := proEtaleRingModules Y' r.RY')
    (C₂ := proEtaleRingModules X r.RX)
    (C₃ := proEtaleRingModules X' r.RX')
    (D₀ := proEtaleRingModules Y s.RY)
    (D₁ := proEtaleRingModules Y' s.RY')
    (D₂ := proEtaleRingModules X s.RX)
    (D₃ := proEtaleRingModules X' s.RX')
    (R₀ := proEtaleRingRestrictScalars aY)
    (R₁ := proEtaleRingRestrictScalars aY')
    (R₂ := proEtaleRingRestrictScalars aX)
    (R₃ := proEtaleRingRestrictScalars aX')
    (J := proEtaleRingModulePullback g r.RY r.RY' r.cg)
    (H := proEtaleRingModulePullback f' r.RY' r.RX' r.cf')
    (G := proEtaleRingModulePullback f r.RY r.RX r.cf)
    (I := proEtaleRingModulePullback g' r.RX r.RX' r.cg')
    (J' := proEtaleRingModulePullback g s.RY s.RY' s.cg)
    (H' := proEtaleRingModulePullback f' s.RY' s.RX' s.cf')
    (G' := proEtaleRingModulePullback f s.RY s.RX s.cf)
    (I' := proEtaleRingModulePullback g' s.RX s.RX' s.cg')
    (proEtaleRingRestrictionPullbackInv g r.RY s.RY r.RY' s.RY'
      aY aY' r.cg s.cg hg)
    (proEtaleRingRestrictionPullbackInv f' r.RY' s.RY' r.RX' s.RX'
      aY' aX' r.cf' s.cf' hf')
    (proEtaleRingRestrictionPullbackInv f r.RY s.RY r.RX s.RX
      aY aX r.cf s.cf hf)
    (proEtaleRingRestrictionPullbackInv g' r.RX s.RX r.RX' s.RX'
      aX aX' r.cg' s.cg' hg')
    r.exchangeModuleSquare.hom s.exchangeModuleSquare.hom
    (proEtaleRingRestriction_square r s aY aX aY' aX' hf hg hg' hf')

private instance termwise_preservesFiniteLimits
    {C D : Type*} [Category C] [Category D] [HasFiniteLimits C]
    (F : C ⥤ D) [PreservesFiniteLimits F] :
    PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) :=
  ⟨fun J _ _ ↦ whiskeringRight_preservesLimitsOfShape (C := ℕᵒᵖ) (J := J) F⟩

private instance termwise_preservesFiniteColimits
    {C D : Type*} [Category C] [Category D] [HasFiniteColimits C]
    (F : C ⥤ D) [PreservesFiniteColimits F] :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ C D).obj F) :=
  ⟨fun J _ _ ↦ whiskeringRight_preservesColimitsOfShape (C := ℕᵒᵖ) (J := J) F⟩

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem localizeTowerSquare_eq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    [HasDerivedCategory (ℕᵒᵖ ⥤ C)] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : F ⋙ G ≅ H ⋙ I) :
    Functor.mapDerivedCategorySquareIso
      (F₁ := (Functor.whiskeringRight ℕᵒᵖ _ _).obj F)
      (F₂ := (Functor.whiskeringRight ℕᵒᵖ _ _).obj G)
      (G₁ := (Functor.whiskeringRight ℕᵒᵖ _ _).obj H)
      (G₂ := (Functor.whiskeringRight ℕᵒᵖ _ _).obj I)
      (termwiseSquareIso e) =
    Functor.mapDerivedCategoryCompIso
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj F)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj G) ≪≫
    Functor.mapDerivedCategoryNatIso
      (F := (Functor.whiskeringRight ℕᵒᵖ _ _).obj F ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj G)
      (G := (Functor.whiskeringRight ℕᵒᵖ _ _).obj H ⋙
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj I)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso e) ≪≫
    (Functor.mapDerivedCategoryCompIso
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj H)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).obj I)).symm := rfl

private theorem towerSquare_localization (r : StrictTowerRingedSquare sq) :
    Functor.mapDerivedCategorySquareIso
      (F₁ := exchangeTowerModulePull g r.RY r.RY' r.cg)
      (F₂ := exchangeTowerModulePull f' r.RY' r.RX' r.cf')
      (G₁ := exchangeTowerModulePull f r.RY r.RX r.cf)
      (G₂ := exchangeTowerModulePull g' r.RX r.RX' r.cg')
        (termwiseSquareIso r.exchangeModuleSquare) =
      r.exchangeTowerSquare := by
  exact localizeTowerSquare_eq
    (F := proEtaleRingModulePullback g r.RY r.RY' r.cg)
    (G := proEtaleRingModulePullback f' r.RY' r.RX' r.cf')
    (H := proEtaleRingModulePullback f r.RY r.RX r.cf)
    (I := proEtaleRingModulePullback g' r.RX r.RX' r.cg') r.exchangeModuleSquare

private theorem derivedCube_nat
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
  [Category C₀] [Category C₁] [Category C₂] [Category C₃]
  [Category D₀] [Category D₁] [Category D₂] [Category D₃]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [Abelian D₀] [Abelian D₁] [Abelian D₂] [Abelian D₃]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁]
  [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁]
  [HasDerivedCategory D₂] [HasDerivedCategory D₃]
  {R₀ : D₀ ⥤ C₀} {R₁ : D₁ ⥤ C₁} {R₂ : D₂ ⥤ C₂} {R₃ : D₃ ⥤ C₃}
  {J : C₀ ⥤ C₁} {H : C₁ ⥤ C₃} {G : C₀ ⥤ C₂} {I : C₂ ⥤ C₃}
  {J' : D₀ ⥤ D₁} {H' : D₁ ⥤ D₃} {G' : D₀ ⥤ D₂} {I' : D₂ ⥤ D₃}
  [R₀.Additive] [R₁.Additive] [R₂.Additive] [R₃.Additive]
  [J.Additive] [H.Additive] [G.Additive] [I.Additive]
  [J'.Additive] [H'.Additive] [G'.Additive] [I'.Additive]
  [PreservesFiniteLimits R₀] [PreservesFiniteColimits R₀]
  [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [PreservesFiniteLimits R₃] [PreservesFiniteColimits R₃]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
  [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits I'] [PreservesFiniteColimits I']
    (qJ : R₀ ⋙ J ≅ J' ⋙ R₁) (qH : R₁ ⋙ H ≅ H' ⋙ R₃)
    (qG : R₀ ⋙ G ≅ G' ⋙ R₂) (qI : R₂ ⋙ I ≅ I' ⋙ R₃)
    (c : J ⋙ H ≅ G ⋙ I) (d : J' ⋙ H' ≅ G' ⋙ I')
    (hc : Functor.whiskerLeft R₀ c.hom ≫ Functor.whiskerRight qG.hom I ≫
        Functor.whiskerLeft G' qI.hom =
      Functor.whiskerRight qJ.hom H ≫ Functor.whiskerLeft J' qH.hom ≫
        Functor.whiskerRight d.hom R₃) :
    Functor.whiskerLeft R₀.mapDerivedCategory (Functor.mapDerivedCategorySquareIso c).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso qG).hom I.mapDerivedCategory ≫
      Functor.whiskerLeft G'.mapDerivedCategory (Functor.mapDerivedCategorySquareIso qI).hom =
    Functor.whiskerRight (Functor.mapDerivedCategorySquareIso qJ).hom H.mapDerivedCategory ≫
      Functor.whiskerLeft J'.mapDerivedCategory (Functor.mapDerivedCategorySquareIso qH).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategorySquareIso d).hom R₃.mapDerivedCategory := by
  apply NatTrans.ext
  funext M
  exact Functor.exactDerivedCube qJ qH qG qI c d
    (fun N ↦ congrArg (fun z ↦ z.app N) hc) M


end RestoredRestrictionSquare

section ExactDerivedMate
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
omit [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D] in
private theorem exactDerivedSquare_symm
    (s : G ⋙ L' ≅ L ⋙ H) :
    (Functor.mapDerivedCategorySquareIso s.symm).hom =
      (Functor.mapDerivedCategorySquareIso s).inv := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

end ExactDerivedMate

section RestoredExchangeResPull
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] completedAdicDerivedChange

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

private theorem termwisePull_additive {U V : Scheme.{t}} (u : U ⟶ V)
    (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (e : (proEtaleSheafInverseImage u CommRingCat.{t + 1}).obj R ≅ S) :
    (exchangeTowerModulePull u R S e).Additive := by
  infer_instance

attribute [local instance] termwisePull_additive

-- Keep the standard tower localization visible when specializing the ringed square.
attribute [local instance 2000] exchangeTowers_hasDerived

private theorem exchangeResPull_square
    (sq : ChosenCartesianSquare g' f' f g) :
    Functor.whiskerRight (exchangeResPull d g).inv (exchangeConstantPull (A := A) f') ≫
      Functor.whiskerLeft (d.towerPull g) (exchangeResPull d f').inv ≫
      Functor.whiskerRight (d.integralTowerRingedSquare sq).exchangeTowerSquare.hom
        (exchangeTowerRes d X') =
    Functor.whiskerLeft (exchangeTowerRes d Y)
        (exchangeConstantSquare (A := A) sq).exchangeTowerSquare.hom ≫
      Functor.whiskerRight (exchangeResPull d f).inv (exchangeConstantPull (A := A) g') ≫
      Functor.whiskerLeft (d.towerPull f) (exchangeResPull d g').inv := by
  let r := exchangeConstantSquare (A := A) sq
  let s := d.integralTowerRingedSquare sq
  have ho := restrictionTowerCube_nat r s
    (exchangeScalar d Y) (exchangeScalar d X)
    (exchangeScalar d Y') (exchangeScalar d X')
    (exchangeScalar_comm d f) (exchangeScalar_comm d g)
    (exchangeScalar_comm d g') (exchangeScalar_comm d f')
  have hd := derivedCube_nat
    (C₀ := exchangeTowers Y (exchangeConstantRing Y A))
    (C₁ := exchangeTowers Y' (exchangeConstantRing Y' A))
    (C₂ := exchangeTowers X (exchangeConstantRing X A))
    (C₃ := exchangeTowers X' (exchangeConstantRing X' A))
    (D₀ := exchangeTowers Y (d.completedRing Y))
    (D₁ := exchangeTowers Y' (d.completedRing Y'))
    (D₂ := exchangeTowers X (d.completedRing X))
    (D₃ := exchangeTowers X' (d.completedRing X'))
    (R₀ := exchangeTowerModuleRes d Y) (R₁ := exchangeTowerModuleRes d Y')
    (R₂ := exchangeTowerModuleRes d X) (R₃ := exchangeTowerModuleRes d X')
    (J := exchangeTowerModulePull g (exchangeConstantRing Y A)
      (exchangeConstantRing Y' A) (exchangeConstantIso g A))
    (H := exchangeTowerModulePull f' (exchangeConstantRing Y' A)
      (exchangeConstantRing X' A) (exchangeConstantIso f' A))
    (G := exchangeTowerModulePull f (exchangeConstantRing Y A)
      (exchangeConstantRing X A) (exchangeConstantIso f A))
    (I := exchangeTowerModulePull g' (exchangeConstantRing X A)
      (exchangeConstantRing X' A) (exchangeConstantIso g' A))
    (J' := d.towerModulePull g) (H' := d.towerModulePull f')
    (G' := d.towerModulePull f) (I' := d.towerModulePull g')
    (exchangeModuleResPull d g).symm (exchangeModuleResPull d f').symm
    (exchangeModuleResPull d f).symm (exchangeModuleResPull d g').symm
    (termwiseSquareIso r.exchangeModuleSquare)
    (termwiseSquareIso s.exchangeModuleSquare) ho
  erw [towerSquare_localization r, towerSquare_localization s] at hd
  simpa only [exchangeResPull, exactDerivedSquare_symm, r, s] using hd.symm
end RestoredExchangeResPull
end AlgebraicGeometry.Scheme

-- Keep localized comparison constructions folded while elaborating their equations.
attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryNatIso
namespace AlgebraicGeometry.Scheme.CompletedOpenFiniteTranspose

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U T' T : Scheme.{u}} {v : U' ⟶ U} {j' : U' ⟶ T'}
  {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']

/-- The source Q: reduce the open extension, then pull the entire strict tower back.
Source: blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
abbrev source :=
  cbcDerivedOpenShriek d j inferInstance ⋙ completedReductionTower T d ⋙
    completedTowerPullback g d

/-- The open object C: strict derived pullback of the reduction tower of K.
Source: blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
abbrev corner := completedReductionTower U d ⋙ completedTowerPullback v d

/-- M is scalar restriction of the strict reduction tower, without completeness.
Source: blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
abbrev restricted := completedReductionTower U d ⋙ exchangeTowerRes d U

/-- H is constant-coefficient inverse image of M.
Source: blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
abbrev openTarget := restricted d (U := U) ⋙ ProEtale.StrictTower.G A v

/-- N is constant-coefficient inverse image of the open extension of M.
Source: blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
abbrev ambientTarget :=
  restricted d (U := U) ⋙ ProEtale.StrictTower.J A j ⋙ ProEtale.StrictTower.G A g

/-- The fixed comparison a uses the normalized pullback transport, scalar comparison,
and quotient/open identification, in that order. No isomorphism is freely chosen.
Source: blueprint finite-exchange paragraph; Stacks 099N and 03DI
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
def sourceComparison (K : d.derived U) :
    (exchangeTowerRes d T').obj ((source d (j := j) (g := g)).obj K) ≅
      (ambientTarget d (j := j) (g := g)).obj K :=
  (exchangeTowerRes d T').mapIso
      ((cbcDatumTowerTransport d g).app
        ((completedReductionTower T d).obj
          ((cbcDerivedOpenShriek d j inferInstance).obj K))) ≪≫
    (exchangeResPull d g).app _ ≪≫
    (ProEtale.StrictTower.G A g).mapIso (cbcRealizationQuotientOpen d j K)

/-- The fixed finite-reduction/scalar comparison d at the open corner.
Source: blueprint finite-exchange paragraph; Stacks 099N
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
def cornerComparison (K : d.derived U) :
    (exchangeTowerRes d U').obj ((corner d (v := v)).obj K) ≅
      (openTarget d (v := v)).obj K :=
  (exchangeTowerRes d U').mapIso
      ((cbcDatumTowerTransport d v).app ((completedReductionTower U d).obj K)) ≪≫
    (exchangeResPull d v).app _

/-- b = J(d)e, with e the published presheaf-identity scalar/open comparison.
Source: Stacks 03DI and 03CY, blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
def extensionComparison (K : d.derived U) :
    (exchangeTowerRes d T').obj
        ((cbcRealizationJ d j').obj ((corner d (v := v)).obj K)) ≅
      (ProEtale.StrictTower.J A j').obj ((openTarget d (v := v)).obj K) :=
  (cbcRealizationTowerScalarOpen d j').app _ ≪≫
    (ProEtale.StrictTower.J A j').mapIso (cornerComparison d (v := v) K)

/-- The transported arrow Psi(x), with the canonical scalar/restriction map c inserted.
Source: blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
def psi (K : d.derived U)
    (x : (corner d (v := v)).obj K ⟶
      (d.towerPull j').obj ((source d (j := j) (g := g)).obj K)) :
    (openTarget d (v := v)).obj K ⟶
      (ProEtale.StrictTower.G A j').obj ((ambientTarget d (j := j) (g := g)).obj K) :=
  (cornerComparison d (v := v) K).inv ≫ (exchangeTowerRes d U').map x ≫
    (exchangeResPull d j').hom.app ((source d (j := j) (g := g)).obj K) ≫
    (ProEtale.StrictTower.G A j').map (sourceComparison d (j := j) (g := g) K).hom

/-- The specified inverse-image square compositor for constant strict towers.
Source: Stacks 07A7; the unit-preserving compositors of strict tower operations
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
def constantSquare (sq : OpenImmersionSquare v j' j g) :
    ProEtale.StrictTower.G A j ⋙ ProEtale.StrictTower.G A v ≅
      ProEtale.StrictTower.G A g ⋙ ProEtale.StrictTower.G A j' :=
  (ProEtale.StrictTower.gComp A v j).symm ≪≫
    eqToIso (congrArg (fun f ↦ ProEtale.StrictTower.G A f) sq.w) ≪≫
    ProEtale.StrictTower.gComp A j' g

/-- The special x is pullback of the completed open unit, followed by the canonical
square compositor and the inverse quotient/open source identification. The actual
K-flat pullback presentations are transported by their universal counits.
Source: Stacks 03DI and 07A7, blueprint finite-exchange paragraph
(blueprint: lem-cbc-completed-open-finite-transpose-coherence). -/
def unitArrow (sq : OpenImmersionSquare v j' j g) (K : d.derived U) :
    (corner d (v := v)).obj K ⟶
      (d.towerPull j').obj ((source d (j := j) (g := g)).obj K) :=
  (cbcDatumTowerTransport d v).hom.app ((completedReductionTower U d).obj K) ≫
    (d.towerPull v).map
      ((cbcRealizationTowerAdj d j).unit.app ((completedReductionTower U d).obj K)) ≫
    ({ RY := d.completedRing T,
        RX := d.completedRing U,
        RY' := d.completedRing T',
        RX' := d.completedRing U',
        cf := d.integralRingIso j,
        cg := d.integralRingIso g,
        cg' := d.integralRingIso v,
        cf' := d.integralRingIso j',
        coherent := d.integral_coherent sq.toChosenCartesianSquare } :
        StrictTowerRingedSquare sq.toChosenCartesianSquare).exchangeTowerSquare.inv.app
      ((cbcRealizationJ d j).obj ((completedReductionTower U d).obj K)) ≫
    (d.towerPull j').map
      ((d.towerPull g).map (cbcRealizationReduction d j K).inv ≫
        (cbcDatumTowerTransport d g).inv.app
          ((completedReductionTower T d).obj
            ((cbcDerivedOpenShriek d j inferInstance).obj K)))

attribute [local irreducible] constantSquare

private theorem scalarTranspose
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {r : C ⥤ E} {s : D ⥤ F} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L ⋙ s ≅ r ⋙ L') (c : R ⋙ r ≅ s ⋙ R')
    (he : ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ c.hom)) = e.inv)
    {X : C} {Y : D} (x : X ⟶ R.obj Y) :
    e.inv.app X ≫ s.map ((a.homEquiv X Y).symm x) =
      L'.map (r.map x ≫ c.hom.app Y) ≫ b.counit.app (s.obj Y) := by
  rw [Adjunction.homEquiv_counit, Functor.map_comp, ← Category.assoc]
  erw [← e.inv.naturality x]
  simp only [Functor.comp_map, Category.assoc]
  have hc := mateEquiv_counit_symm a b (TwoSquare.mk _ _ _ _ c.hom) Y
  change L'.map (c.hom.app Y) ≫ b.counit.app (s.obj Y) =
    (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ c.hom)).app _) ≫
      s.map (a.counit.app Y) at hc
  rw [he] at hc
  rw [← hc, Functor.map_comp, Category.assoc]

private theorem termwiseMate
    {C D E F I : Type*} [Category C] [Category D] [Category E] [Category F]
    [Category I] {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {r : C ⥤ E} {s : D ⥤ F} (a : L ⊣ R) (b : L' ⊣ R')
    (c : R ⋙ r ≅ s ⋙ R') (M : I ⥤ C) (n : I) :
    (((mateEquiv (a.whiskerRight I) (b.whiskerRight I)).symm
      (TwoSquare.mk _ _ _ _
        (Functor.whiskeringRightObjCompIso _ _ ≪≫
          (Functor.whiskeringRight I _ _).mapIso c ≪≫
            (Functor.whiskeringRightObjCompIso _ _).symm).hom)).app M).app n =
      (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ c.hom)).app (M.obj n)) := by
  simp [mateEquiv, Adjunction.whiskerRight]

private theorem localizedMate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {r : C ⥤ E} {s : D ⥤ F}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [r.Additive] [s.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    (a : L ⊣ R) (b : L' ⊣ R') (e : L ⋙ s ≅ r ⋙ L') (c : R ⋙ r ≅ s ⋙ R')
    (he : ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ c.hom)) = e.inv) :
    ((mateEquiv
      (a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory)
      (b.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R'.rightDerivedFunctorIsoMapDerivedCategory)).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso c).hom)) =
      (Functor.mapDerivedCategorySquareIso e).inv := by
  have : IsIso ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ c.hom)) := by
    rw [he]
    infer_instance
  have hd := (exact_localization_inverse_mate a b c).2.1
  have hi : asIso ((mateEquiv a b).symm
      (TwoSquare.mk _ _ _ _ c.hom)) = e.symm := Iso.ext he
  rw [hi] at hd
  rw [ProEtale.SemilinearProperOpen.exact_adjunction_eq a,
    ProEtale.SemilinearProperOpen.exact_adjunction_eq b]
  simpa only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc] using hd

private theorem scalarMate {V W : Scheme.{u}} (i : V ⟶ W) [IsOpenImmersion i] :
    ((mateEquiv (cbcRealizationTowerAdj d i)
      (ProEtale.StrictTower.jAdj A i)).symm
      (TwoSquare.mk _ _ _ _ (exchangeResPull d i).hom)) =
      (cbcRealizationTowerScalarOpen d i).inv := by
  let a := (cbcRealizationOpenAdj d i).whiskerRight ℕᵒᵖ
  let b := (ProEtale.StrictTower.moduleJAdj A i).whiskerRight ℕᵒᵖ
  let e := Functor.whiskeringRightObjCompIso _ _ ≪≫
    (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (cbcRealizationScalarOpen d i) ≪≫
    (Functor.whiskeringRightObjCompIso _ _).symm
  have hm : ((mateEquiv a b).symm
      (TwoSquare.mk _ _ _ _ (exchangeModuleResPull d i).hom)) = e.inv := by
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    have h := termwiseMate (cbcRealizationOpenAdj d i)
      (ProEtale.StrictTower.moduleJAdj A i) (exchangeOrdinaryResPull d i) M n
    exact h
  have hd := localizedMate a b e (exchangeModuleResPull d i) hm
  simp only [cbcRealizationTowerAdj, ProEtale.StrictTower.jAdj, exchangeResPull,
    cbcRealizationTowerScalarOpen, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, e, a, b, Category.assoc] at hd ⊢
  dsimp only [cbcRealizationJ, cbcRealizationTowerJ, cbcRealizationRes,
    exchangeTowerRes, exchangeTowerModuleRes, exchangeTowerModulePull,
    AdicCoefficientDatum.towerModulePull, AdicCoefficientDatum.towerPull,
    ProEtale.StrictTower.J, ProEtale.StrictTower.towerJ, ProEtale.StrictTower.G,
    ProEtale.StrictTower.towerPullback, exchangeConstantPull, exchangeTowerPull,
    ProEtale.StrictTower.modulePullback, ProEtale.StrictTower.Modules,
    ProEtale.StrictTower.coefficients, ProEtale.StrictTower.constantRingIso,
    exchangeConstantIso, proEtaleConstantComparison, exchangeConstantRing,
    adicLisseConstantRing, exchangeTowers, pbcTowers, ProEtale.StrictTower.Towers,
    pbcModules, proEtaleRingModules, reductionTowerCategory, reductionModuleRing,
    pbcAdicCompletion, pbcTowers_hasDerivedCategory, exchangeTowers_hasDerived,
    ProEtale.StrictTower.towers_hasDerivedCategory, reductionTowerHasDerivedCategory] at hd ⊢
  exact hd

private theorem scalarUnit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {r : C ⥤ E} {s : D ⥤ F} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L ⋙ s ≅ r ⋙ L') (c : R ⋙ r ≅ s ⋙ R')
    (he : ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ c.hom)) = e.inv)
    (X : C) :
    r.map (a.unit.app X) ≫ c.hom.app (L.obj X) ≫ R'.map (e.hom.app X) =
      b.unit.app (r.obj X) := by
  have hu := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ c.hom) X
  change r.map (a.unit.app X) ≫ c.hom.app (L.obj X) =
    b.unit.app (r.obj X) ≫ R'.map
      (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ c.hom)).app X) at hu
  rw [he] at hu
  rw [reassoc_of% hu, ← R'.map_comp, Iso.inv_hom_id_app]
  erw [R'.map_id, Category.comp_id]

private theorem sourceTransport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (r : C ⥤ C') (s : D ⥤ D') (P : D ⥤ C) (Q : D' ⥤ C')
    (c : P ⋙ r ≅ s ⋙ Q) {X₀ : C} {Y₀ Y : D} {N : D'}
    (δ : X₀ ≅ P.obj Y₀) (ρ : Y₀ ≅ Y) (ε : s.obj Y ≅ N) :
    r.mapIso (δ ≪≫ P.mapIso ρ) ≪≫ (c.app Y ≪≫ Q.mapIso ε) =
      r.mapIso δ ≪≫ c.app Y₀ ≪≫ Q.mapIso (s.mapIso ρ ≪≫ ε) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Iso.app_hom, Category.assoc]
  have hn := c.hom.naturality ρ.hom
  dsimp only [Functor.comp_map] at hn
  simpa only [Category.assoc] using
    congrArg (fun f ↦ r.map δ.hom ≫ f ≫ Q.map ε.hom) hn

private theorem transportArrow
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (r : C ⥤ C') (s : D ⥤ D') (P : D ⥤ C) (Q : D' ⥤ C')
    (c : P ⋙ r ≅ s ⋙ Q)
    {X₀ X : C} {Y₀ Y : D} {H : C'} {N : D'}
    (δ : X₀ ≅ X) (α : Y₀ ≅ Y) (β : r.obj X ≅ H) (a : s.obj Y ≅ N)
    (x : X ⟶ P.obj Y) :
    (r.mapIso δ ≪≫ β).inv ≫ r.map (δ.hom ≫ x ≫ P.map α.inv) ≫
        c.hom.app Y₀ ≫ Q.map (s.mapIso α ≪≫ a).hom =
      β.inv ≫ r.map x ≫ c.hom.app Y ≫ Q.map a.hom := by
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← r.map_comp_assoc, Iso.inv_hom_id]
  erw [r.map_id, Category.id_comp]
  have hn := c.hom.naturality α.inv
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← Q.map_comp_assoc, ← s.map_comp, Iso.inv_hom_id]
  erw [s.map_id, Q.map_id, Category.id_comp]

private theorem restrictionSquare (sq : OpenImmersionSquare v j' j g)
    (Y : DerivedCategory (exchangeTowers T (d.completedRing T))) :
    (exchangeTowerRes d U').map
        ((d.integralTowerRingedSquare sq.toChosenCartesianSquare).exchangeTowerSquare.inv.app Y) ≫
      (exchangeResPull d j').hom.app ((d.towerPull g).obj Y) ≫
      (ProEtale.StrictTower.G A j').map ((exchangeResPull d g).hom.app Y) =
    (exchangeResPull d v).hom.app ((d.towerPull j).obj Y) ≫
      (ProEtale.StrictTower.G A v).map ((exchangeResPull d j).hom.app Y) ≫
      (exchangeConstantSquare (A := A) sq.toChosenCartesianSquare).exchangeTowerSquare.inv.app
        ((exchangeTowerRes d T).obj Y) := by
  let σ := (d.integralTowerRingedSquare sq.toChosenCartesianSquare).exchangeTowerSquare
  let τ := (exchangeConstantSquare (A := A) sq.toChosenCartesianSquare).exchangeTowerSquare
  let l := (ProEtale.StrictTower.G A j').mapIso ((exchangeResPull d g).app Y).symm ≪≫
    ((exchangeResPull d j').app ((d.towerPull g).obj Y)).symm
  let p := (exchangeTowerRes d U').mapIso (σ.app Y)
  let q := (τ.app ((exchangeTowerRes d T).obj Y)) ≪≫
    (ProEtale.StrictTower.G A v).mapIso ((exchangeResPull d j).app Y).symm ≪≫
      ((exchangeResPull d v).app ((d.towerPull j).obj Y)).symm
  have hh := congrArg (fun z ↦ z.app Y) (exchangeResPull_square d sq.toChosenCartesianSquare)
  have h : (l ≪≫ p).hom = q.hom := by
    simp only [l, p, q, σ, τ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.app_hom, Iso.app_inv, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
      ] at hh ⊢
    with_unfolding_all exact hh
  have hi := congrArg Iso.inv (Iso.ext h : l ≪≫ p = q)
  simpa only [l, p, q, σ, τ, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Category.assoc] using hi

attribute [local irreducible] cbcDatumTowerTransport cbcRealizationReduction
  cbcRealizationTowerScalarOpen exchangeResPull

end AlgebraicGeometry.Scheme.CompletedOpenFiniteTranspose
