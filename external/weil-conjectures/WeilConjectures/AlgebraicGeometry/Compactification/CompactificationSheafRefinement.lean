/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.Defs
import WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange

/-!
# The sheaf map along a cartesian compactification refinement

Source: Stacks Project, Tags 0F7B and 0F7I.
(blueprint: lem-sfb-compactification-sheaf-refinement).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A]
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
  (r : c.Refinement d) (hcart : IsPullback c.i (𝟙 X) r.hom d.i)

/-- The adjunct of inverse open base change, followed by direct-image composition.
Source: Stacks Project, Tags 0F7B and 0F7I.
(blueprint: lem-sfb-compactification-sheaf-refinement). -/
noncomputable def compactificationSheafRefinement :
    openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i ⋙
        lowerStar (ModuleCat.{u + 1} A) d.g ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g := by
  let B := ModuleCat.{u + 1} A
  have := r.isIso_openImmersionLowerShriekBaseChange B hcart
  exact
    Functor.whiskerRight
      (Functor.whiskerLeft (openImmersionLowerShriek B d.i)
          (upperStarLowerStarAdjunction B r.hom).unit ≫
        Functor.whiskerRight (asIso (r.openImmersionLowerShriekBaseChange B)).inv
          (lowerStar B r.hom)) (lowerStar B d.g) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (openImmersionLowerShriek B c.i) (refinementLowerStarComp B r).hom

private lemma map_lowerStarComp_counit (B : Type*) [Category.{u + 1} B]
    [Abelian B] [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    {U V W : Scheme.{u}} (j : U ⟶ V) (q : V ⟶ W) (k : U ⟶ W)
    (hk : k = j ≫ q) (M : Sheaf U.smallEtaleTopology B) :
    (upperStar B k).map
        ((lowerStarComp B j q k hk).hom.app M) ≫
      (upperStarLowerStarAdjunction B k).counit.app M =
    (upperStarComp B j q k hk).hom.app _ ≫
      (upperStar B j).map
        ((upperStarLowerStarAdjunction B q).counit.app
          ((lowerStar B j).obj M)) ≫
      (upperStarLowerStarAdjunction B j).counit.app M := by
  have he : conjugateEquiv
      ((upperStarLowerStarAdjunction B q).comp (upperStarLowerStarAdjunction B j))
      (upperStarLowerStarAdjunction B k) (upperStarComp B j q k hk).hom =
      (lowerStarComp B j q k hk).hom :=
    congrArg Iso.hom (conjugateIsoEquiv_upperStarComp B j q k hk)
  have h := conjugateEquiv_counit
    ((upperStarLowerStarAdjunction B q).comp (upperStarLowerStarAdjunction B j))
    (upperStarLowerStarAdjunction B k) (upperStarComp B j q k hk).hom M
  rw [he] at h
  simpa only [Adjunction.comp_counit_app, Functor.comp_obj] using h

private lemma open_inclusion_counit (B : Type*) [Category.{u + 1} B]
    [Abelian B] [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (M : Sheaf U.smallEtaleTopology B) :
    (upperStar B j).map
        ((openImmersionLowerShriekToLowerStar B j).app M) ≫
      (upperStarLowerStarAdjunction B j).counit.app M =
      inv ((openImmersionLowerShriekUpperStarAdjunction B j).unit.app M) := by
  apply (cancel_epi
    ((openImmersionLowerShriekUpperStarAdjunction B j).unit.app M)).1
  rw [unit_map_openImmersionLowerShriekToLowerStar_app_counit, IsIso.hom_inv_id]
  rfl

private lemma refinement_open_inclusion (B : Type*) [Category.{u + 1} B]
    [Abelian B] [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    [IsIso (r.openImmersionLowerShriekBaseChange B)]
    (M : Sheaf X.smallEtaleTopology B) :
    (upperStarLowerStarAdjunction B r.hom).unit.app
        ((openImmersionLowerShriek B d.i).obj M) ≫
      (lowerStar B r.hom).map
        ((asIso (r.openImmersionLowerShriekBaseChange B)).inv.app M ≫
          (openImmersionLowerShriekToLowerStar B c.i).app M) ≫
      (lowerStarComp B c.i r.hom d.i r.i_hom.symm).hom.app M =
      (openImmersionLowerShriekToLowerStar B d.i).app M := by
  apply ((upperStarLowerStarAdjunction B d.i).homEquiv _ _).symm.injective
  have hx := ((upperStarLowerStarAdjunction B r.hom).homEquiv_unit
    ((openImmersionLowerShriek B d.i).obj M) ((lowerStar B c.i).obj M)
    ((asIso (r.openImmersionLowerShriekBaseChange B)).inv.app M ≫
      (openImmersionLowerShriekToLowerStar B c.i).app M)).symm
  rw [← Category.assoc, hx]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [map_lowerStarComp_counit, open_inclusion_counit]
  have n := (upperStarComp B c.i r.hom d.i r.i_hom.symm).hom.naturality
    (((upperStarLowerStarAdjunction B r.hom).homEquiv
      ((openImmersionLowerShriek B d.i).obj M) ((lowerStar B c.i).obj M))
      ((asIso (r.openImmersionLowerShriekBaseChange B)).inv.app M ≫
        (openImmersionLowerShriekToLowerStar B c.i).app M))
  simp only [Functor.comp_map] at n
  have t := ((upperStarLowerStarAdjunction B r.hom).homEquiv_counit
    ((openImmersionLowerShriek B d.i).obj M) ((lowerStar B c.i).obj M)
    (((upperStarLowerStarAdjunction B r.hom).homEquiv
      ((openImmersionLowerShriek B d.i).obj M) ((lowerStar B c.i).obj M))
      ((asIso (r.openImmersionLowerShriekBaseChange B)).inv.app M ≫
        (openImmersionLowerShriekToLowerStar B c.i).app M)))
  rw [Equiv.symm_apply_apply] at t
  rw [reassoc_of% n, ← Functor.map_comp_assoc]
  erw [← t]
  simp only [Functor.map_comp, Category.assoc]
  rw [open_inclusion_counit]
  rw [← cancel_epi ((openImmersionLowerShriekUpperStarAdjunction B d.i).unit.app M),
    IsIso.hom_inv_id]
  have hb := unit_map_openImmersionLowerShriekBaseChange_app B c.i r.hom d.i r.i_hom M
  rw [upperStarCompIso_eq] at hb
  rw [← reassoc_of% hb, ← Functor.map_comp_assoc]
  have hi : (openImmersionLowerShriekBaseChange B c.i r.hom d.i r.i_hom).app M ≫
      (asIso (r.openImmersionLowerShriekBaseChange B)).inv.app M = 𝟙 _ := by
    change (asIso (r.openImmersionLowerShriekBaseChange B)).hom.app M ≫ _ = _
    exact Iso.hom_inv_id_app _ _
  rw [hi, CategoryTheory.Functor.map_id, Category.id_comp, IsIso.hom_inv_id]
  rfl

private lemma open_inclusion_mono (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (M : Sheaf U.smallEtaleTopology B) :
    Mono ((openImmersionLowerShriekToLowerStar B j).app M) := by
  let γ : (openImmersionLowerShriek B j).obj M ⟶ (lowerStar B j).obj M :=
    (openImmersionLowerShriekToLowerStar B j).app M
  have hj : IsIso ((upperStar B j).map γ) :=
    (NatIso.isIso_map_iff (upperStarIsoOpenImmersionRestriction B j) γ).2 inferInstance
  have hz := isZero_upperStar_openImmersionLowerShriek_of_disjoint_range B j
    j.closedComplement (by rw [j.range_closedComplement]; exact disjoint_compl_right) M
  have hc : Mono ((upperStar B j.closedComplement).map γ) := hz.mono _
  have hker {Z : Scheme.{u}}
      (q : Sheaf V.smallEtaleTopology B ⥤ Sheaf Z.smallEtaleTopology B)
      [PreservesFiniteLimits q] [Mono (q.map γ)] : IsZero (q.obj (kernel γ)) :=
    (isZero_kernel_of_mono (q.map γ)).of_iso (PreservesKernel.iso q γ)
  have h0 : IsZero (kernel γ) :=
    isZero_of_isZero_upperStar (A := B) (j := j) j.closedComplement j.range_closedComplement
      (hker (upperStar B j)) (hker (upperStar B j.closedComplement))
  exact Preadditive.mono_of_isZero_kernel γ h0

private lemma compactification_inclusion_mono
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    {U V : Scheme.{u}} {g : U ⟶ V} (e : Compactification g)
    (M : Sheaf U.smallEtaleTopology B) :
    Mono ((lowerStar B e.g).map ((openImmersionLowerShriekToLowerStar B e.i).app M) ≫
      (lowerStarComp B e.i e.g g e.comm).hom.app M) := by
  have := open_inclusion_mono B e.i M
  infer_instance

/-- The sheaf refinement preserves the inclusion into ordinary pushforward, whose
components are monomorphisms.
Source: Stacks Project, Tag 0F7I, and the sheaf comparison in Tag 0F7B.
(blueprint: lem-sfb-compactification-sheaf-refinement).

Proof: transpose the refinement map under inverse image/direct image. The mate identity
for open base change identifies its composite with the finer open inclusion, followed by
composition of direct images, with the coarser open inclusion. Associativity of direct-image
composition then gives the displayed equation after the proper pushforward to Y. To see
monicity, restrict the open inclusion j!M to j, where it is an isomorphism. On the closed
complement its source is zero. Exactness of both restrictions and their joint conservativity
show that its kernel is zero. Proper direct image preserves monomorphisms, and the final
composition comparison is invertible, proving monicity for the compactification inclusion. -/
theorem compactificationSheafRefinement_properties :
    compactificationSheafRefinement A r hcart ≫ compactificationSheafToDirectImage A c =
      compactificationSheafToDirectImage A d ∧
    ∀ M, Mono ((compactificationSheafToDirectImage A c).app M) := by
  let B := ModuleCat.{u + 1} A
  have := r.isIso_openImmersionLowerShriekBaseChange B hcart
  constructor
  · apply NatTrans.ext
    funext M
    have hassoc := congr_app (lowerStarComp_assoc' B c.i r.hom d.g d.i c.g f
      r.i_hom.symm r.hom_g.symm d.comm) M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at hassoc
    simp only [compactificationSheafRefinement, compactificationSheafToDirectImage,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.id_comp, Category.assoc]
    rw [← reassoc_of% (refinementLowerStarComp B r).hom.naturality
      ((openImmersionLowerShriekToLowerStar B c.i).app M)]
    rw [refinementLowerStarComp_eq, ← hassoc]
    simp only [← Functor.map_comp_assoc]
    rw [← Functor.map_comp_assoc]
    simp only [Category.assoc]
    rw [← (lowerStar B r.hom).map_comp_assoc, refinement_open_inclusion]
  · intro M
    exact compactification_inclusion_mono (ModuleCat.{u + 1} A) c M

end AlgebraicGeometry.Etale
