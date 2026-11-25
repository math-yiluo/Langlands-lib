/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientBasicSupplement
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.Topology.Category.TopCat.Basic
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientPullback

/-! # Canonical pullback of continuous coefficient sections

Source: Bhatt--Scholze, Definition 6.8.1 and the paragraph before Definition 6.8.6.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Precomposition with the first projection, as a map to direct image. -/
noncomputable def continuousCoefficientDirectMap (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    {Z X : Scheme.{u}} (h : Z ⟶ X) :
    continuousCoefficientSheaf X T ⟶
      (proEtaleSheafDirectImage h CommRingCat.{u + 1}).obj
        (continuousCoefficientSheaf Z T) :=
  ⟨{ app U := CommRingCat.ofHom
       (continuousMapRestrictionRingHom T (pullback.fst U.unop.hom h))
     naturality := by
       intro U V f
       apply CommRingCat.hom_ext
       apply RingHom.ext
       intro s
       change C(U.unop.left, T) at s
       apply ContinuousMap.ext
       intro x
       change s _ = s _
       congr 1
       have hp : ((proEtaleBaseChange h).map f.unop).left ≫
           pullback.fst U.unop.hom h = pullback.fst V.unop.hom h ≫ f.unop.left :=
         pullback.lift_fst _ _ _
       simpa only [proEtaleBaseChange, ProEt.forget, Functor.op_map, Functor.op_obj,
         MorphismProperty.Over.pullback_obj_hom, Quiver.Hom.unop_op,
         Functor.comp_map, MorphismProperty.Comma.forget_map,
         Over.forget_map, Over.Hom.left, MorphismProperty.Comma.Hom.hom_left,
         NatTrans.op_app,
         Iso.symm_inv, Scheme.Hom.comp_base, TopCat.comp_app, TopCat.Hom.hom] using!
         (congrArg (fun g : ((proEtaleBaseChange h).obj V.unop).left ⟶ U.unop.left ↦
           g.base.hom x) hp).symm }⟩

/-- The canonical continuous coefficient pullback map, defined by adjunction. -/
noncomputable def continuousCoefficientPullback (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    {Z X : Scheme.{u}} (h : Z ⟶ X) :
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
      (continuousCoefficientSheaf X T) ⟶ continuousCoefficientSheaf Z T :=
  ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).homEquiv _ _).symm
    (continuousCoefficientDirectMap T h)

/-- The canonical pullback has the prescribed value on every continuous function. -/
theorem continuousCoefficientPullback_normalized (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    {Z X : Scheme.{u}} (h : Z ⟶ X) :
    continuousCoefficientRestrictionNormalized T h (continuousCoefficientPullback T h) := by
  unfold continuousCoefficientRestrictionNormalized continuousCoefficientPullback
  rw [Equiv.apply_symm_apply]
  intro U s x
  rfl

private theorem adjunct_comp_comparison {C D E : Type*}
    [Category C] [Category D] [Category E]
    {Lg : C ⥤ D} {Rg : D ⥤ C} {Lf : D ⥤ E} {Rf : E ⥤ D}
    {L : C ⥤ E} {R : E ⥤ C}
    (adjg : Lg ⊣ Rg) (adjf : Lf ⊣ Rf) (adj : L ⊣ R)
    (e : Rf ⋙ Rg ≅ R) {A : C} {B : D} {T : E}
    (h : A ⟶ Rg.obj B) (k : B ⟶ Rf.obj T) :
    (adj.homEquiv A T).symm (h ≫ Rg.map k ≫ e.hom.app T) =
      ((conjugateEquiv (adjg.comp adjf) adj).symm e.hom).app A ≫
        Lf.map ((adjg.homEquiv A B).symm h) ≫ (adjf.homEquiv B T).symm k := by
  apply (adj.homEquiv A T).injective
  rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_right]
  change _ = (adj.unit.app A ≫ R.map _) ≫ R.map _
  rw [← unit_conjugateEquiv_symm (adjg.comp adjf) adj e.hom A,
    Category.assoc, ← e.hom.naturality]
  conv_rhs => rw [← Category.assoc]
  change _ = ((adjg.comp adjf).homEquiv A T)
    (Lf.map ((adjg.homEquiv A B).symm h) ≫ (adjf.homEquiv B T).symm k) ≫ _
  rw [Adjunction.comp_homEquiv]
  change _ = (adjg.homEquiv _ _) ((adjf.homEquiv _ _) _) ≫ _
  rw [adjf.homEquiv_naturality_left, Equiv.apply_symm_apply,
    adjg.homEquiv_naturality_right, Equiv.apply_symm_apply]
  simp only [Category.assoc]

/-- Successive continuous pullbacks agree with composite pullback under the
canonical inverse-image composition isomorphism. -/
theorem continuousCoefficientPullback_comp (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    {W Z X : Scheme.{u}} (k : W ⟶ Z) (h : Z ⟶ X) :
    continuousCoefficientPullback T (k ≫ h) =
      (proEtaleRingInverseImageComp k h).hom.app (continuousCoefficientSheaf X T) ≫
        (proEtaleSheafInverseImage k CommRingCat.{u + 1}).map
          (continuousCoefficientPullback T h) ≫ continuousCoefficientPullback T k := by
  let e := Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp
      (P := @WeaklyEtale) (Q := ⊤) k h).symm) CommRingCat.{u + 1}
        (ProEt.topology X) (ProEt.topology Z) (ProEt.topology W)
  have hρ : continuousCoefficientDirectMap T (k ≫ h) =
      continuousCoefficientDirectMap T h ≫
        (proEtaleSheafDirectImage h CommRingCat.{u + 1}).map
          (continuousCoefficientDirectMap T k) ≫
            e.hom.app (continuousCoefficientSheaf W T) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    change C(U.unop.left, T) at s
    apply ContinuousMap.ext
    intro x
    change s _ = s _
    congr 1
    simpa only [proEtaleBaseChange, ProEt.forget, Functor.op_map, Functor.op_obj,
         MorphismProperty.Over.pullback_obj_hom, Quiver.Hom.unop_op,
         Functor.comp_map, MorphismProperty.Comma.forget_map,
         Over.forget_map, Over.Hom.left, MorphismProperty.Comma.Hom.hom_left,
         NatTrans.op_app,
         Iso.symm_inv, Scheme.Hom.comp_base, TopCat.comp_app, TopCat.Hom.hom] using!
      (congrArg (fun g : pullback U.unop.hom (k ≫ h) ⟶ U.unop.left ↦ g.base.hom x)
        (MorphismProperty.Over.pullbackComp_left_fst_fst
          (P := @WeaklyEtale) (Q := ⊤) k h U.unop)).symm
  unfold continuousCoefficientPullback
  rw [hρ]
  exact adjunct_comp_comparison (proEtaleSheafAdjunction h CommRingCat.{u + 1})
    (proEtaleSheafAdjunction k CommRingCat.{u + 1})
    (proEtaleSheafAdjunction (k ≫ h) CommRingCat.{u + 1}) e
    (continuousCoefficientDirectMap T h) (continuousCoefficientDirectMap T k)

/-- Coefficient maps commute with pullback of continuous functions. -/
theorem continuousCoefficientPullback_naturality {T S : Type (u + 1)}
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TopologicalSpace S] [CommRing S] [IsTopologicalRing S]
    (φ : T →+* S) (hφ : Continuous φ) {Z X : Scheme.{u}} (h : Z ⟶ X) :
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (continuousCoefficientMap φ hφ X) ≫ continuousCoefficientPullback S h =
      continuousCoefficientPullback T h ≫ continuousCoefficientMap φ hφ Z := by
  let adj := proEtaleSheafAdjunction h CommRingCat.{u + 1}
  unfold continuousCoefficientPullback
  rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
  congr 1

/-- The actual inclusion of integral coefficients into rational coefficients. -/
noncomputable def integralRationalCoefficientMap (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) : integralCoefficientSheaf l X E ⟶ rationalCoefficientSheaf l X E := by
  letI := coefficientExtensionNormedField l E
  exact continuousCoefficientMap
    (RingHom.ulift (Padic.coefficientExtensionIntegers l E).subtype)
    (continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)) X

/-- The integral inclusion has its pointwise normalization. -/
theorem integralRationalCoefficientMap_normalized (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) :
    integralRationalCoefficientNormalized l E X (integralRationalCoefficientMap l E X) := by
  intro U s x
  rfl

end AlgebraicGeometry.Scheme
