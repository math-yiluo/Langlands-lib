/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.StrictTower.OpenBetaSourceFactorization
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all Mathlib.Algebra.Homology.Localization

/-!
# The clopen section projector of a proper/open square

Source: Stacks Project, more-etale.tex, Tag 0F7B; morphisms.tex, Tag 01W6(2);
sites-modules.tex, Tag 03DI; derived.tex, Tag 015F, and the strict-tower refinement
(blueprint: lem-cbc-proper-open-clopen-projector).

All coefficient rings are arbitrary commutative rings. The categories and normalized
operations are the recorded constant-ring module and strict-tower constructions.
The declarations together state the geometry, the section formula, its adjunction
normalization, its termwise descent, and the comparison specializations.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u vC uC vD uD wC wD

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem inverse_mate_isIso
    {A D A' D' : Type*} [Category A] [Category D] [Category A'] [Category D']
    {L : A ⥤ D} {R : D ⥤ A} {L' : A' ⥤ D'} {R' : D' ⥤ A'}
    (a : L ⊣ R) (b : L' ⊣ R') (P : A ⥤ A') (Q : D ⥤ D')
    [P.IsEquivalence] [Q.IsEquivalence] (β : R ⋙ P ⟶ Q ⋙ R') [IsIso β] :
    IsIso ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ β)) := by
  let α := (mateEquiv a b).symm (TwoSquare.mk _ _ _ _ β)
  let γ : TwoSquare Q.op R.op R'.op P.op :=
    TwoSquare.mk _ _ _ _ (NatTrans.op β)
  have : IsIso γ := by dsimp [γ]; infer_instance
  have ho := isIso_mateEquiv_of_isEquivalence a.op b.op γ
  have hi (M : A) : IsIso (α.app M) := by
    have he : (mateEquiv a.op b.op γ).app (op M) = (α.app M).op := by
      simp [α, γ, mateEquiv, Adjunction.op, NatTrans.op_app, Functor.op_map,
        ← op_comp]
    have : IsIso ((α.app M).op) := by rw [← he]; infer_instance
    exact isIso_of_op _
  exact NatIso.isIso_of_isIso_app _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem projector_image
    {C D : Type*} [Category C] [Category D]
    {L : D ⥤ C} {G : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ G) (b : G ⊣ R) [IsIso a.unit]
    (t : L ⟶ R) [IsIso t]
    (ht : ∀ N, t.app N = b.unit.app (L.obj N) ≫ R.map ((inv a.unit).app N))
    (M : C) :
    G.map (b.unit.app M ≫ inv (t.app (G.obj M))) = a.unit.app (G.obj M) := by
  have he : t.app (G.obj M) = a.counit.app M ≫ b.unit.app M := by
    rw [ht]
    have htri : (inv a.unit).app (G.obj M) = G.map (a.counit.app M) := by
      apply (cancel_epi (a.unit.app (G.obj M))).1
      simpa only [NatIso.isIso_inv_app, IsIso.hom_inv_id, Functor.id_obj] using
        (a.right_triangle_components M).symm
    rw [htri]
    exact (b.unit.naturality (a.counit.app M)).symm
  rw [Functor.map_comp]
  apply (cancel_mono (G.map (t.app (G.obj M)))).1
  simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
    Category.comp_id]
  rw [he, Functor.map_comp, ← Category.assoc, a.right_triangle_components]
  exact (Category.id_comp _).symm

/-- The canonical lift is clopen, with the two prescribed projections and a complementary
open subscheme. Source: Stacks 0F7B and 01W6(2)
(blueprint: lem-cbc-proper-open-clopen-projector).
Proof: b is the base change of i, so W_S is the open p^{-1}(S) of W and s is the open
k(V) in that open. The pullback equations give bs=k and qs=r. The base change q of
p is proper, hence separated. Properness of qs=r and Tag 01W6(2) imply s proper.
Its image is closed; an open immersion with closed image is a closed immersion.
The complementary open subscheme supplies C and c, including the empty cases. -/
theorem properOpen_clopen_geometry {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    IsOpenImmersion (squareLift k r p i h) ∧
    IsClosedImmersion (squareLift k r p i h) ∧
    squareLift k r p i h ≫ pullback.fst p i = k ∧
    squareLift k r p i h ≫ pullback.snd p i = r ∧
    ∃ (C : Scheme.{u}) (c : C ⟶ pullback p i),
      IsOpenImmersion c ∧ Set.range c = (Set.range (squareLift k r p i h))ᶜ := by
  refine ⟨inferInstance, inferInstance, pullback.lift_fst k r h,
    pullback.lift_snd k r h, ?_⟩
  let O : (pullback p i).Opens :=
    ⟨(Set.range (squareLift k r p i h))ᶜ,
      (squareLift k r p i h).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  exact ⟨O.toScheme, O.ι, inferInstance, Scheme.Opens.range_ι O⟩

/-- The ordinary direct-image adjunction, using exactly the constant-ring comparison.
Source: Stacks 03DA and 03DI
(blueprint: lem-cbc-proper-open-clopen-projector). -/
abbrev clopenModuleAdj {U X : Scheme.{u}} (s : U ⟶ X) :
    modulePullback B s ⊣ moduleDirectImage B s :=
  Scheme.proEtaleRingModuleAdjunction s (coefficients B X) (coefficients B U)
    (constantRingIso B s)

/-- The ordinary open unit is invertible, including on the empty open.
Source: Stacks 03DI (blueprint: lem-cbc-proper-open-clopen-projector).
Proof: identify the small pro-etale site of U with the localization of X's site at U.
Restriction of extension by zero recovers the original sheaf, with its specified
unit. Transport along the unit-preserving adjoint identification. -/
theorem clopenModule_openUnit_isIso {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] : IsIso (moduleJAdj B s).unit := by
  let A := ModuleCat.{u + 1} B
  have : IsIso (openImmersionLowerShriekAdjunction A s).unit :=
    (openImmersionAdjunctionTriple A s).isIso_unit_iff_isIso_counit.mpr
      (isIso_openImmersionRestrictionLowerStarAdjunction_counit A s)
  let ff := (openImmersionLowerShriekAdjunction A s).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  exact unit_iso_of_comparison (L := moduleJ B s) (R := modulePullback B s)
    (moduleJAdj B s) (fixedRestriction B U) (fixedRestriction B X)
    (openImmersionLowerShriek A s) (fixedOpen B s)

/-- The direct-image transpose of the inverse ordinary open unit.
Source: Stacks 03DI (blueprint: lem-cbc-proper-open-clopen-projector). -/
def clopenModuleToDirect {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] :
    moduleJ B s ⟶ moduleDirectImage B s :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft (moduleJ B s) (clopenModuleAdj B s).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (@inv _ _ _ _ (moduleJAdj B s).unit (clopenModule_openUnit_isIso B s))
      (moduleDirectImage B s) ≫ (Functor.leftUnitor _).hom

/-- The canonical transpose is invertible for clopen immersions.
Source: Stacks 03DI (blueprint: lem-cbc-proper-open-clopen-projector).
Proof: for a sheaf N on U both extension by zero and direct image have sections
N(H_U). The extension adjunction is given by gluing a prescribed section on H_U
with zero on H_C. Its unit is identity under this model, so the displayed transpose
is identity on N(H_U). Therefore it is an isomorphism, for arbitrary B. -/
theorem clopenModuleToDirect_isIso {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] : IsIso (clopenModuleToDirect B s) := by
  let d := moduleClopenIso B s
  have := clopenModule_openUnit_isIso B s
  let ff := (moduleJAdj B s).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : (moduleDirectImage B s).Full := Functor.Full.of_iso d
  have : (moduleDirectImage B s).Faithful := Functor.Faithful.of_iso d
  have hi (M : Modules B U) : IsIso ((clopenModuleToDirect B s).app M) := by
    have hu : IsIso ((clopenModuleAdj B s).unit.app ((moduleJ B s).obj M)) :=
      (clopenModuleAdj B s).isIso_unit_app_of_iso (d.app M)
    have hv : IsIso ((inv (moduleJAdj B s).unit).app M) := inferInstance
    dsimp only [clopenModuleToDirect, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_inv_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app]
    simp only [Category.id_comp]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The ordinary intrinsic projector. Its section characterization is stated below;
no arbitrary splitting or map is chosen.
Source: Stacks 03DI (blueprint: lem-cbc-proper-open-clopen-projector). -/
def clopenModulePi {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (Modules B X) ⟶ modulePullback B s ⋙ moduleJ B s :=
  (clopenModuleAdj B s).unit ≫ Functor.whiskerLeft (modulePullback B s)
    (@inv _ _ _ _ (clopenModuleToDirect B s) (clopenModuleToDirect_isIso B s))

/-- The section projector is uniquely determined by its identity/zero restrictions,
and is the first factor of the section decomposition under the natural additive
identification of the target sections with F(H_U). Its composite with t is the
specified direct-image unit.
Source: Stacks 03DI and 09AE (blueprint: lem-cbc-proper-open-clopen-projector).
Proof: the disjoint-cover equalizer gives F(H)=F(H_U) times F(H_C). The model
I(N)(H)=N(H_U), with restricted scalar action, has the extension-by-zero adjunction:
glue the given map on H_U with zero on H_C. Adjoint uniqueness identifies it with
moduleJ preserving the unit. Direct image has the same model, and its unit is
restriction to H_U. Thus t is identity in this model, and unit followed by t inverse
is first-factor restriction. It is natural and additive. Restriction to U is the
open unit, and restriction to C has zero target. Maps with these two restrictions
coincide, since the two section factors detect equality. -/
theorem clopenModule_section_projector {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    [IsOpenImmersion c] (hc : Set.range c = (Set.range s)ᶜ) :
    clopenModulePi B s ≫
        Functor.whiskerLeft (modulePullback B s) (clopenModuleToDirect B s) =
      (clopenModuleAdj B s).unit ∧
    (∀ F : Modules B X,
      (modulePullback B s).map ((clopenModulePi B s).app F) =
        (moduleJAdj B s).unit.app ((modulePullback B s).obj F)) ∧
    (∀ F : Modules B X,
      IsZero ((modulePullback B c).obj ((moduleJ B s).obj ((modulePullback B s).obj F))) ∧
      (modulePullback B c).map ((clopenModulePi B s).app F) = 0) ∧
    (∀ τ : 𝟭 (Modules B X) ⟶ modulePullback B s ⋙ moduleJ B s,
      (∀ F, (modulePullback B s).map (τ.app F) =
        (moduleJAdj B s).unit.app ((modulePullback B s).obj F)) →
      (∀ F, (modulePullback B c).map (τ.app F) = 0) → τ = clopenModulePi B s) ∧
    (∀ (F : Modules B X) (H : X.ProEt),
      ∃ e : (((modulePullback B s ⋙ moduleJ B s).obj F).val.obj (op H)) ≃+
          F.val.obj (op ((MorphismProperty.Over.map ⊤
            (inferInstance : WeaklyEtale s)).obj (Scheme.ProEt.clopenTestPiece s H))),
        ∀ x : F.val.obj (op H),
          e (((clopenModulePi B s).app F).val.app (op H) x) =
            F.val.map (Scheme.ProEt.clopenTestInclusion s H).op x) := by
  have hu := clopenModule_openUnit_isIso B s
  have ht := clopenModuleToDirect_isIso B s
  have hcomp : clopenModulePi B s ≫
      Functor.whiskerLeft (modulePullback B s) (clopenModuleToDirect B s) =
        (clopenModuleAdj B s).unit := by
    simp [clopenModulePi, ← Functor.whiskerLeft_comp]
  have hopen (M : Modules B X) :
      (modulePullback B s).map ((clopenModulePi B s).app M) =
        (moduleJAdj B s).unit.app ((modulePullback B s).obj M) := by
    simp only [clopenModulePi, NatTrans.comp_app, Functor.whiskerLeft_app,
      NatIso.isIso_inv_app]
    apply projector_image (moduleJAdj B s) (clopenModuleAdj B s)
      (clopenModuleToDirect B s) _ M
    intro N
    simp only [clopenModuleToDirect, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
      Functor.associator_inv_app, Functor.leftUnitor_hom_app, Category.id_comp]
    rw [← Category.assoc]
    exact Category.comp_id _
  have hzero (M : Modules B X) :
      IsZero ((modulePullback B c).obj ((moduleJ B s).obj
        ((modulePullback B s).obj M))) := by
    let A := ModuleCat.{u + 1} B
    let N := (modulePullback B s).obj M
    let e := (fixedPull B c).app ((moduleJ B s).obj N) ≪≫
      (upperStar A c).mapIso ((fixedOpen B s).app N)
    have hd : Set.range s.base ∩ Set.range c.base = ∅ := by
      rw [hc, Set.inter_compl_self]
    have hz := isZero_upperStar_openImmersionLowerShriek A s c hd
      ((fixedRestriction B U).obj N)
    exact IsZero.of_full_of_faithful_of_isZero (fixedRestriction B C) _ (hz.of_iso e)
  refine ⟨hcomp, hopen, fun M ↦ ⟨hzero M, (hzero M).eq_zero_of_tgt _⟩, ?_, ?_⟩
  · intro τ hτ _
    apply NatTrans.ext
    funext M
    apply (cancel_mono ((clopenModuleToDirect B s).app
      ((modulePullback B s).obj M))).1
    apply ((clopenModuleAdj B s).homEquiv M ((modulePullback B s).obj M)).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp]
    rw [hτ M, hopen M]
  · intro M H
    let P := fixedRestriction B X
    let Q := fixedRestriction B U
    let a := clopenModuleAdj B s
    let b := openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) s
    let d := fixedDirect B s
    have : P.IsEquivalence := {}
    have : Q.IsEquivalence := {}
    let α := (mateEquiv a b).symm (TwoSquare.mk _ _ _ _ d.hom)
    have : IsIso α := inverse_mate_isIso a b P Q d.hom
    let V := Scheme.ProEt.clopenTestPiece s H
    let e₁ := ((PresheafOfModules.evaluation _ (op H)).mapIso
      ((SheafOfModules.forget _).mapIso
        ((asIso (clopenModuleToDirect B s)).app ((modulePullback B s).obj M))))
    let e₂ := (asIso α).symm.app M
    let e₂H := ((evaluation _ _).obj (op V)).mapIso
      ((sheafToPresheaf _ _).mapIso e₂)
    refine ⟨e₁.toLinearEquiv.toAddEquiv.trans e₂H.toLinearEquiv.toAddEquiv, ?_⟩
    intro x
    have he := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ d.hom) M
    have hh := congrArg (fun f ↦ f.hom.app (op H)) he
    have hp := congrArg (fun f ↦ f.val.app (op H)) (NatTrans.congr_app hcomp M)
    have hx := ConcreteCategory.congr_hom hh x
    have hpx := ConcreteCategory.congr_hom hp x
    have hb : (b.unit.app (P.obj M)).hom.app (op H) =
        (P.obj M).obj.map (Scheme.ProEt.clopenTestInclusion s H).op := by
      simp [b, openImmersionRestrictionLowerStarAdjunction,
        localizationRestrictionLowerStarAdjunction, Adjunction.sheafPushforwardContinuous,
        Scheme.ProEt.clopenTestInclusion]
    change ((d.hom.app ((modulePullback B s).obj M)).hom.app (op H))
        (((P.map (a.unit.app M)).hom.app (op H)) x) =
      (((lowerStar (ModuleCat.{u + 1} B) s).map (α.app M)).hom.app (op H))
        (((b.unit.app (P.obj M)).hom.app (op H)) x) at hx
    rw [hb] at hx
    change ((a.unit.app M).val.app (op H)) x =
      ((α.app M).hom.app (op V)) (M.val.map (Scheme.ProEt.clopenTestInclusion s H).op x)
      at hx
    change e₂H.hom (((clopenModuleToDirect B s).app
      ((modulePullback B s).obj M)).val.app (op H)
        (((clopenModulePi B s).app M).val.app (op H) x)) = _
    change ((clopenModuleToDirect B s).app
      ((modulePullback B s).obj M)).val.app (op H)
        (((clopenModulePi B s).app M).val.app (op H) x) =
          ((a.unit.app M).val.app (op H)) x at hpx
    rw [hpx, hx]
    exact ConcreteCategory.congr_hom (e₂H.inv_hom_id) _

/-- The ordinary projector applied termwise to strict inverse systems.
Source: Stacks 02MZ and 03DI (blueprint: lem-cbc-proper-open-clopen-projector). -/
def clopenTowerPi {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] :
    𝟭 (Towers B X) ⟶ towerPullback B s ⋙ towerJ B s :=
  (Functor.whiskeringRight ℕᵒᵖ (Modules B X) (Modules B X)).map (clopenModulePi B s)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- On towers and complexes the section identities hold before localization.
Source: Stacks 02MZ and 03DI (blueprint: lem-cbc-proper-open-clopen-projector).
Proof: naturality of the ordinary projector makes it commute with all transitions
and differentials. Apply the two ordinary restriction identities componentwise.
The zero target is zero at every level and degree. -/
theorem clopenTower_section_projector {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    [IsOpenImmersion c] (hc : Set.range c = (Set.range s)ᶜ) :
    (∀ M : Towers B X,
      (towerPullback B s).map ((clopenTowerPi B s).app M) =
        ((moduleJAdj B s).whiskerRight ℕᵒᵖ).unit.app ((towerPullback B s).obj M)) ∧
    (∀ M : Towers B X,
      IsZero ((towerPullback B c).obj ((towerJ B s).obj ((towerPullback B s).obj M))) ∧
      (towerPullback B c).map ((clopenTowerPi B s).app M) = 0) ∧
    (∀ K : CochainComplex (Towers B X) ℤ,
      ((towerPullback B s).mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (clopenTowerPi B s) (.up ℤ)).app K) =
        (((moduleJAdj B s).whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).unit.app
          (((towerPullback B s).mapHomologicalComplex (.up ℤ)).obj K)) ∧
    (∀ K : CochainComplex (Towers B X) ℤ,
      IsZero (((towerPullback B c).mapHomologicalComplex (.up ℤ)).obj
        (((towerJ B s).mapHomologicalComplex (.up ℤ)).obj
          (((towerPullback B s).mapHomologicalComplex (.up ℤ)).obj K))) ∧
      ((towerPullback B c).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (clopenTowerPi B s) (.up ℤ)).app K) = 0) := by
  obtain ⟨_, hopen, hzero, _, _⟩ := clopenModule_section_projector B s c hc
  have htopen (M : Towers B X) :
      (towerPullback B s).map ((clopenTowerPi B s).app M) =
        ((moduleJAdj B s).whiskerRight ℕᵒᵖ).unit.app ((towerPullback B s).obj M) := by
    apply NatTrans.ext
    funext n
    exact hopen (M.obj n)
  have htzero (M : Towers B X) :
      IsZero ((towerPullback B c).obj ((towerJ B s).obj ((towerPullback B s).obj M))) :=
    Functor.isZero _ (fun n ↦ (hzero (M.obj n)).1)
  refine ⟨htopen, fun M ↦ ⟨htzero M, (htzero M).eq_zero_of_tgt _⟩, ?_, ?_⟩
  · intro K
    apply HomologicalComplex.hom_ext
    intro n
    exact htopen (K.X n)
  · intro K
    have hz : IsZero (((towerPullback B c).mapHomologicalComplex (.up ℤ)).obj
        (((towerJ B s).mapHomologicalComplex (.up ℤ)).obj
          (((towerPullback B s).mapHomologicalComplex (.up ℤ)).obj K))) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply HomologicalComplex.hom_ext
      intro n
      exact (htzero (K.X n)).eq_zero_of_tgt _
    exact ⟨hz, hz.eq_zero_of_tgt _⟩

/-- Mathlib's abelian structure on strict towers, with the coefficient universe fixed.
This is the existing functor-category instance over the existing module-sheaf instance.
Source: Stacks 02MZ and 03DA (blueprint: lem-cbc-proper-open-clopen-projector). -/
abbrev clopenTowerAbelian (X : Scheme.{u}) : Abelian (Towers B X) :=
  @Abelian.functorCategoryAbelian ℕᵒᵖ inferInstance (Modules B X) inferInstance
    (@SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _ _ _
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X))
      (SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1})
      (SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1}))

/-- Compatibility of an exact natural transformation with localization on complexes.
This predicate records the representative equation using the existing exact-functor
factorizations; it introduces no new derived functor or map.
Source: Stacks 015F and localization's universal property
(blueprint: lem-cbc-proper-open-clopen-projector). -/
def ClopenProjectorDescent
    {A : Type uC} [Category.{vC} A] [aA : Abelian A] [HasDerivedCategory.{wC} A]
    {D : Type uD} [Category.{vD} D] [aD : Abelian D] [HasDerivedCategory.{wD} D]
    (F H : A ⥤ D) [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (τ : F ⟶ H) (δ : F.mapDerivedCategory ⟶ H.mapDerivedCategory) : Prop :=
  ∀ K : CochainComplex A ℤ,
    δ.app (DerivedCategory.Q.obj K) ≫ H.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app K)

attribute [local instance] clopenTowerAbelian
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem projector_factorsh
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory D]
    (F : A ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift, NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app, Iso.refl_hom, Iso.refl_inv, Functor.comp_obj]
  erw [F.mapDerivedCategory.map_id, Category.id_comp, DerivedCategory.Qh.map_id,
    Category.comp_id, Category.comp_id]

private theorem projector_unit_fac
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ D} {R : D ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ R) (K : CochainComplex A ℤ) :
    (exactAdj a).unit.app (DerivedCategory.Q.obj K) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  have h := exactAdj_unit a ((HomotopyCategory.quotient A (.up ℤ)).obj K)
  rw [projector_factorsh] at h
  change (exactAdj a).unit.app (DerivedCategory.Q.obj K) ≫
    R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
      R.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient D (.up ℤ)).obj
          ((L.mapHomologicalComplex (.up ℤ)).obj K)) = _ at h
  rw [projector_factorsh, Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  exact h

set_option backward.isDefEq.respectTransparency true in
private theorem projector_restriction_descent
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ D) (H : D ⥤ A) [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : H ⊣ F) (p : 𝟭 A ⟶ F ⋙ H)
    (d : 𝟭 (DerivedCategory A) ⟶ F.mapDerivedCategory ⋙ H.mapDerivedCategory)
    (hp : ∀ M, F.map (p.app M) = a.unit.app (F.obj M))
    (hd : ∀ K : CochainComplex A ℤ,
      d.app (DerivedCategory.Q.obj K) ≫
        H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex p (.up ℤ)).app K)) :
    ∀ M, F.mapDerivedCategory.map (d.app M) =
      (exactAdj a).unit.app (F.mapDerivedCategory.obj M) := by
  have he : Functor.whiskerRight d F.mapDerivedCategory =
      Functor.whiskerLeft F.mapDerivedCategory (exactAdj a).unit := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ))
    intro K
    change F.mapDerivedCategory.map (d.app (DerivedCategory.Q.obj K)) =
      (exactAdj a).unit.app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K))
    apply (cancel_mono
      (F.mapDerivedCategory.map
        (H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
          H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        F.mapDerivedCategoryFactors.hom.app
          ((H.mapHomologicalComplex (.up ℤ)).obj
            ((F.mapHomologicalComplex (.up ℤ)).obj K)))).1
    erw [← F.mapDerivedCategory.map_comp_assoc, hd,
      Functor.mapDerivedCategoryFactors_hom_naturality]
    simp only [Functor.map_comp, Category.assoc]
    have hn := (exactAdj a).unit.naturality (F.mapDerivedCategoryFactors.hom.app K)
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    erw [← reassoc_of% hn, projector_unit_fac]
    congr 2
    apply HomologicalComplex.hom_ext
    intro n
    exact hp (K.X n)
  intro M
  exact NatTrans.congr_app he M

section ProjectorLocalization

variable {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory D]
  (F : A ⥤ D) (H : D ⥤ A) [F.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H] (p : 𝟭 A ⟶ F ⋙ H)

@[irreducible] private def projector_lift :
    (𝟭 A).mapDerivedCategory ⟶ (F ⋙ H).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
    ((𝟭 A).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    ((F ⋙ H).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (𝟭 A).mapDerivedCategory (F ⋙ H).mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex p (.up ℤ)) DerivedCategory.Q)

omit [HasDerivedCategory D] in
private theorem projector_lift_fac (K : CochainComplex A ℤ) :
    (projector_lift F H p).app (DerivedCategory.Q.obj K) ≫
        (F ⋙ H).mapDerivedCategoryFactors.hom.app K =
      (𝟭 A).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex p (.up ℤ)).app K) := by
  rw [projector_lift, Localization.liftNatTrans_app]
  change (_ ≫ _ ≫ (F ⋙ H).mapDerivedCategoryFactors.inv.app K) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rfl

@[irreducible] private def projector_map :
    𝟭 (DerivedCategory A) ⟶ F.mapDerivedCategory ⋙ H.mapDerivedCategory :=
  (Functor.mapDerivedCategoryIdIso A).inv ≫ projector_lift F H p ≫
    (Functor.mapDerivedCategoryCompIso F H).inv

private theorem projector_map_fac (K : CochainComplex A ℤ) :
    (projector_map F H p).app (DerivedCategory.Q.obj K) ≫
        H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex p (.up ℤ)).app K) := by
  have hcomp := Functor.mapDerivedCategoryCompIso_hom_app_factors F H K
  have hi := Functor.mapDerivedCategoryIdIso_hom_app_Q_obj K
  calc
    _ = (Functor.mapDerivedCategoryIdIso A).inv.app (DerivedCategory.Q.obj K) ≫
        ((projector_lift F H p).app (DerivedCategory.Q.obj K) ≫
          (F ⋙ H).mapDerivedCategoryFactors.hom.app K) := by
      rw [projector_map]
      dsimp only [NatTrans.comp_app]
      simp only [Category.assoc]
      exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) hcomp)
    _ = _ := by
      rw [projector_lift_fac, ← hi]
      exact Iso.inv_hom_id_app_assoc _ _ _

private theorem projector_map_descent : ClopenProjectorDescent
    (𝟭 A) (F ⋙ H) p ((Functor.mapDerivedCategoryIdIso A).hom ≫
      projector_map F H p ≫ (Functor.mapDerivedCategoryCompIso F H).hom) := by
  have h : (Functor.mapDerivedCategoryIdIso A).hom ≫ projector_map F H p ≫
      (Functor.mapDerivedCategoryCompIso F H).hom = projector_lift F H p := by
    rw [projector_map]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h]
  exact projector_lift_fac F H p

private theorem projector_map_descent_eq
    (e : 𝟭 (DerivedCategory A) ⟶ F.mapDerivedCategory ⋙ H.mapDerivedCategory)
    (he : projector_map F H p = e) : ClopenProjectorDescent
    (𝟭 A) (F ⋙ H) p ((Functor.mapDerivedCategoryIdIso A).hom ≫
      e ≫ (Functor.mapDerivedCategoryCompIso F H).hom) := by
  rw [← he]
  exact projector_map_descent F H p

end ProjectorLocalization

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem projector_unique
    {C D : Type*} [Category C] [Category D]
    {L : D ⥤ C} {G : C ⥤ D} {R : D ⥤ C}
    (b : G ⊣ R) (t : L ⟶ R) [IsIso t]
    (d e : 𝟭 C ⟶ G ⋙ L) (h : ∀ M, G.map (d.app M) = G.map (e.app M)) : d = e := by
  apply NatTrans.ext
  funext M
  apply (cancel_mono (t.app (G.obj M))).1
  apply (b.homEquiv M (G.obj M)).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp]
  rw [h]

private theorem projector_descent_of_restriction
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ D) (H : D ⥤ A) [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : H ⊣ F) (R : DerivedCategory D ⥤ DerivedCategory A)
    (b : F.mapDerivedCategory ⊣ R) (t : H.mapDerivedCategory ⟶ R) (ht : IsIso t)
    (p : 𝟭 A ⟶ F ⋙ H)
    (e : 𝟭 (DerivedCategory A) ⟶ F.mapDerivedCategory ⋙ H.mapDerivedCategory)
    (hp : ∀ M, F.map (p.app M) = a.unit.app (F.obj M))
    (he : ∀ M, F.mapDerivedCategory.map (e.app M) =
      (exactAdj a).unit.app (F.mapDerivedCategory.obj M)) :
    ClopenProjectorDescent (𝟭 A) (F ⋙ H) p
      ((Functor.mapDerivedCategoryIdIso A).hom ≫ e ≫
        (Functor.mapDerivedCategoryCompIso F H).hom) := by
  have := ht
  have hd := projector_restriction_descent F H a p (projector_map F H p) hp
    (projector_map_fac F H p)
  exact projector_map_descent_eq F H p e
    (projector_unique b t _ e (fun M ↦ (hd M).trans (he M).symm))

private theorem projector_complement_zero
    {A D E : Type*} [Category A] [Category D] [Category E]
    [Abelian A] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E]
    (H : D ⥤ A) (F : A ⥤ E) [H.Additive] [F.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (h : ∀ N, IsZero ((H ⋙ F).obj N)) (M : DerivedCategory D) :
    IsZero (F.mapDerivedCategory.obj (H.mapDerivedCategory.obj M)) := by
  have hz := (H ⋙ F).isZero_mapDerivedCategory_obj M (fun _ ↦ h _)
  exact hz.of_iso ((Functor.mapDerivedCategoryCompIso H F).app M)

private theorem intrinsic_projector_restriction {U X : Scheme.{u}}
    (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s] (M : Derived B X) :
    (G B s).map ((pi B s).app M) = (jAdj B s).unit.app ((G B s).obj M) := by
  have hu := jAdj_unit_isIso B s
  have ht := openToR_isIso B s
  simp only [pi, NatTrans.comp_app, Functor.whiskerLeft_app, NatIso.isIso_inv_app]
  apply projector_image (jAdj B s) (adj B s) (openToR B s) _ M
  intro N
  simp only [openToR, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Category.id_comp]
  rw [← Category.assoc]
  exact Category.comp_id _

private theorem intrinsic_projector_normalization {U X : Scheme.{u}}
    (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s] :
    pi B s ≫ Functor.whiskerLeft (G B s) (openToR B s) = (adj B s).unit := by
  dsimp only [pi]
  rw [Category.assoc, ← Functor.whiskerLeft_comp]
  simp only [IsIso.inv_hom_id, Functor.whiskerLeft_id', Category.comp_id]

set_option backward.isDefEq.respectTransparency true in
/-- Localization gives the specified intrinsic projector and preserves the normalized
unit and both component equations as actual transformations on D(T_X).
Source: Stacks 015F, 0DVC, 0FND and localization's universal property
(blueprint: lem-cbc-proper-open-clopen-projector).
Proof: the ordinary clopen identification makes termwise direct image exact.
The exact-derived-functor theorem identifies its descent with total R_s. Use the
cochain-derived-adjunction unit equation for both adjunctions, with all complexes
as resolving class. Both comparisons are invertible, so the descended transpose
is precisely openToR and the descended section projection is pi. Localization
preserves the ordinary equations; its universal property identifies transformations
agreeing after the localization functor. The complementary target is the image
of a zero complex. No faithfulness of tower evaluations is used. -/
theorem clopenDerived_section_projector {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s]
    [IsOpenImmersion c] (hc : Set.range c = (Set.range s)ᶜ) :
    ClopenProjectorDescent (A := Towers B X) (D := Towers B X)
      (aA := clopenTowerAbelian B X) (aD := clopenTowerAbelian B X)
      (𝟭 (Towers B X)) (towerPullback B s ⋙ towerJ B s) (clopenTowerPi B s)
      ((@Functor.mapDerivedCategoryIdIso (Towers B X) inferInstance
        (clopenTowerAbelian B X) (towers_hasDerivedCategory B X)).hom ≫ pi B s ≫
        (@Functor.mapDerivedCategoryCompIso
          (Towers B X) inferInstance (clopenTowerAbelian B X) (towers_hasDerivedCategory B X)
          (Towers B U) inferInstance (clopenTowerAbelian B U) (towers_hasDerivedCategory B U)
          (Towers B X) inferInstance (clopenTowerAbelian B X) (towers_hasDerivedCategory B X)
          (towerPullback B s) inferInstance inferInstance inferInstance
          (towerJ B s) inferInstance inferInstance inferInstance).hom) ∧
    IsIso (openToR B s) ∧
    pi B s ≫ Functor.whiskerLeft (G B s) (openToR B s) =
      (adj B s).unit ∧
    (∀ M : Derived B X,
      (G B s).map ((pi B s).app M) =
        (jAdj B s).unit.app ((G B s).obj M)) ∧
    (∀ M : Derived B X,
      IsZero ((G B c).obj ((J B s).obj ((G B s).obj M))) ∧
      (G B c).map ((pi B s).app M) = 0) := by
  have ht := openToR_isIso B s
  have hpi := intrinsic_projector_restriction B s
  have hz (M : Derived B X) :
      IsZero ((G B c).obj ((J B s).obj ((G B s).obj M))) := by
    let E := towerJ B s ⋙ towerPullback B c
    have hmu := clopenModule_openUnit_isIso B s
    have htu := tower_unit_iso ((moduleJAdj B s))
    have hzE (N : Towers B U) : IsZero (E.obj N) := by
      have hzero := ((clopenTower_section_projector B s c hc).2.1
        ((towerJ B s).obj N)).1
      let e := (towerPullback B c).mapIso ((towerJ B s).mapIso
        ((asIso ((moduleJAdj B s).whiskerRight ℕᵒᵖ).unit).app N))
      exact hzero.of_iso e
    exact projector_complement_zero (towerJ B s) (towerPullback B c) hzE
      ((G B s).obj M)
  refine ⟨?_, ht, ?_, hpi, fun M ↦ ⟨hz M, (hz M).eq_zero_of_tgt _⟩⟩
  · apply projector_descent_of_restriction (towerPullback B s) (towerJ B s)
      ((moduleJAdj B s).whiskerRight ℕᵒᵖ) (R B s) (adj B s) (openToR B s) ht
      (clopenTowerPi B s) (pi B s) (clopenTower_section_projector B s c hc).1
    intro M
    rw [exactAdj_jAdj]
    exact hpi M
  · exact intrinsic_projector_normalization B s

private theorem projector_word_app
    {A D E F : Type*} [Category A] [Category D]
    [Category E] [Category F]
    (Z : A ⥤ F) (Q : A ⥤ D) (L : D ⥤ E) (U : E ⥤ D)
    (H : D ⥤ F) (K K₀ : E ⥤ F) (R R₀ : A ⥤ E)
    (b : Z ≅ Q ⋙ H) (d : 𝟭 D ⟶ L ⋙ U)
    (j₁ : U ⋙ H ≅ K₀) (j₂ : K₀ ≅ K)
    (c : R₀ ≅ Q ⋙ L) (t : R₀ ≅ R) (M : A) :
    (b.hom ≫ Functor.whiskerRight (Functor.whiskerLeft Q d) H ≫
      Functor.whiskerRight (Functor.associator Q L U).inv H ≫
      (Functor.associator (Q ⋙ L) U H).hom ≫
      Functor.whiskerLeft (Q ⋙ L) (j₁.hom ≫ j₂.hom) ≫
      Functor.whiskerRight (c.inv ≫ t.hom) K).app M =
      b.hom.app M ≫ H.map (d.app (Q.obj M)) ≫
        (j₁ ≪≫ j₂).hom.app _ ≫ K.map ((t.symm ≪≫ c).inv.app M) := by
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]
  dsimp only [Functor.comp_obj]
  simp only [Category.id_comp]

private theorem projector_beta_cancel
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (H : D ⥤ E) (K : C ⥤ E)
    {B₀ : D} {P Q : C} {X : E} (e : P ≅ Q) (j : F ⋙ H ≅ K)
    (b : X ≅ H.obj B₀) (c : X ≅ K.obj P)
    (d : B₀ ⟶ F.obj Q) (ε : F.obj Q ⟶ B₀) (h : d ≫ ε = 𝟙 B₀)
    (hz : c.inv = j.inv.app P ≫ H.map (F.map e.hom ≫ ε) ≫ b.inv) :
    b.hom ≫ H.map d ≫ j.hom.app Q ≫ K.map e.inv = c.hom := by
  apply (cancel_mono c.inv).1
  rw [c.hom_inv_id, hz]
  simp only [Category.assoc]
  rw [← reassoc_of% (j.hom.naturality e.inv)]
  rw [Iso.hom_inv_id_app_assoc]
  simp only [← Functor.map_comp_assoc]
  rw [e.inv_hom_id, F.map_id, Category.id_comp, h, H.map_id, Category.id_comp,
    b.hom_inv_id]

private theorem projector_word_cancel
    {A D E F : Type*} [Category A] [Category D] [Category E] [Category F]
    (Z : A ⥤ F) (Q : A ⥤ D) (L : D ⥤ E) (U : E ⥤ D)
    (H : D ⥤ F) (K K₀ : E ⥤ F) (R R₀ : A ⥤ E)
    (b : Z ≅ Q ⋙ H) (d : 𝟭 D ⟶ L ⋙ U) (ε : L ⋙ U ⟶ 𝟭 D)
    (j₁ : U ⋙ H ≅ K₀) (j₂ : K₀ ≅ K)
    (c : R₀ ≅ Q ⋙ L) (t : R₀ ≅ R) (z : Z ≅ R ⋙ K)
    (hd : ∀ M, d.app (Q.obj M) ≫ ε.app (Q.obj M) = 𝟙 _)
    (hz : ∀ M, z.inv.app M = (j₁ ≪≫ j₂).inv.app (R.obj M) ≫
      H.map (U.map ((t.symm ≪≫ c).hom.app M) ≫ ε.app (Q.obj M)) ≫ b.inv.app M) :
    b.hom ≫ Functor.whiskerRight (Functor.whiskerLeft Q d) H ≫
      Functor.whiskerRight (Functor.associator Q L U).inv H ≫
      (Functor.associator (Q ⋙ L) U H).hom ≫
      Functor.whiskerLeft (Q ⋙ L) (j₁.hom ≫ j₂.hom) ≫
      Functor.whiskerRight (c.inv ≫ t.hom) K = z.hom := by
  apply NatTrans.ext
  funext M
  exact (projector_word_app Z Q L U H K K₀ R R₀ b d j₁ j₂ c t M).trans
    (projector_beta_cancel U H K ((t.symm ≪≫ c).app M) (j₁ ≪≫ j₂)
      (b.app M) (z.app M) (d.app (Q.obj M)) (ε.app (Q.obj M)) (hd M) (hz M))

attribute [local irreducible] G J pi alpha gComp jComp jCongr beta betaInv
  jAdj adj towers_hasDerivedCategory

private theorem beta_inv_normalization {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : gU ≫ j = j' ≫ g)
    (hsq : IsPullback gU j' j g) :
    (beta B gU j' j g h hsq).inv = betaInv B gU j' j g h := by
  unfold beta
  rfl

private theorem faithful_family
    (C : Scheme.{u} → Type*) [∀ X, Category (C X)]
    (L : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → (C Y ⥤ C X))
    (κ : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      L (f ≫ g) ≅ L g ⋙ L f)
    (ι : ∀ X, L (𝟙 X) ≅ 𝟭 (C X))
    {U X : Scheme.{u}} (s : U ⟶ X) [IsIso s] : (L s).Faithful := by
  let e : L s ⋙ L (inv s) ≅ 𝟭 (C X) :=
    (κ (inv s) s).symm ≪≫
      eqToIso (congrArg L (IsIso.inv_hom_id s)) ≪≫ ι X
  exact Functor.Faithful.of_comp_iso e

private theorem iso_pullback_faithful {U X : Scheme.{u}}
    (s : U ⟶ X) [IsIso s] : (G B s).Faithful := by
  exact faithful_family (Derived B) (G B) (gComp B) (gId B) s

private theorem iso_projector_counit {U X : Scheme.{u}}
    (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s] [IsIso s]
    (M : Derived B X) :
    (pi B s).app M ≫ (jAdj B s).counit.app M = 𝟙 M := by
  have := iso_pullback_faithful B s
  apply (G B s).map_injective
  rw [Functor.map_comp, intrinsic_projector_restriction]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  exact ((jAdj B s).right_triangle_components M).trans ((G B s).map_id M).symm

/-- Alpha is beta followed by the descended section projection and the specified
open and inverse-image compositors. Cartesian squares recover beta; an identity
left vertical map makes the lift the indicated clopen section.
Source: Stacks 0F7B, with the arbitrary-ring strict-tower refinement
(blueprint: lem-cbc-proper-open-clopen-projector).
Proof: insert the section projection into the definition of alpha and use its
identification with pi. The equations bs=k and qs=r give the displayed final
compositors. In a cartesian square the canonical lift is the pullback isomorphism.
Its inverse-image functor is faithful, by the inverse-map and identity compositors.
The projector restriction and adjunction triangle then show that pi followed by
the open counit is identity. Source factorization of betaInv inserts this counit;
naturality and cancellation of the open and inverse-image compositors give beta.
For V=S and r=identity the pullback equations give qs=identity, so the same
projector selects the clopen section (k,identity). All equalities are equalities
of natural transformations on the whole unbounded derived category. -/
theorem properOpen_clopen_projector {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (alpha B k r p i h =
      (beta B (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom ≫
      Functor.whiskerRight (Functor.whiskerLeft (G B (pullback.snd p i))
        (pi B (squareLift k r p i h))) (J B (pullback.fst p i)) ≫
      Functor.whiskerRight
        (Functor.associator (G B (pullback.snd p i)) (G B (squareLift k r p i h))
          (J B (squareLift k r p i h))).inv (J B (pullback.fst p i)) ≫
      (Functor.associator (G B (pullback.snd p i) ⋙ G B (squareLift k r p i h))
        (J B (squareLift k r p i h)) (J B (pullback.fst p i))).hom ≫
      Functor.whiskerLeft (G B (pullback.snd p i) ⋙ G B (squareLift k r p i h))
        ((jComp B (squareLift k r p i h) (pullback.fst p i)).hom ≫
          (jCongr B (pullback.lift_fst k r h)).hom) ≫
      Functor.whiskerRight
        ((gComp B (squareLift k r p i h) (pullback.snd p i)).inv ≫
          (eqToIso (congrArg (G B) (pullback.lift_snd k r h))).hom) (J B k)) ∧
    (∀ hsq : IsPullback k r p i,
      IsIso (squareLift k r p i h) ∧
      alpha B k r p i h = (beta B r k i p h.symm hsq.flip).hom) ∧
    (∀ (k' : S ⟶ W) [IsOpenImmersion k'] [QuasiCompact k']
        (h' : k' ≫ p = (𝟙 S) ≫ i),
      squareLift k' (𝟙 S) p i h' ≫ pullback.snd p i = 𝟙 S ∧
      ∀ (C : Scheme.{u}) (c : C ⟶ pullback p i) [IsOpenImmersion c],
        Set.range c = (Set.range (squareLift k' (𝟙 S) p i h'))ᶜ →
        ∀ M : Derived B (pullback p i),
          (G B (squareLift k' (𝟙 S) p i h')).map
              ((pi B (squareLift k' (𝟙 S) p i h')).app M) =
            (jAdj B (squareLift k' (𝟙 S) p i h')).unit.app
              ((G B (squareLift k' (𝟙 S) p i h')).obj M) ∧
          (G B c).map ((pi B (squareLift k' (𝟙 S) p i h')).app M) = 0) := by
  refine ⟨by unfold alpha; rfl, ?_, ?_⟩
  · intro hsq
    have hs : squareLift k r p i h = hsq.isoPullback.hom := by
      apply pullback.hom_ext <;> simp [squareLift]
    have hi : IsIso (squareLift k r p i h) := by rw [hs]; infer_instance
    refine ⟨hi, ?_⟩
    unfold alpha
    apply projector_word_cancel (J B i ⋙ G B p) (G B (pullback.snd p i))
      (G B (squareLift k r p i h)) (J B (squareLift k r p i h))
      (J B (pullback.fst p i)) (J B k) (J B (squareLift k r p i h ≫ pullback.fst p i))
      (G B r) (G B (squareLift k r p i h ≫ pullback.snd p i))
      (beta B (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip)
      (pi B (squareLift k r p i h)) (jAdj B (squareLift k r p i h)).counit
      (jComp B (squareLift k r p i h) (pullback.fst p i))
      (jCongr B (pullback.lift_fst k r h))
      (gComp B (squareLift k r p i h) (pullback.snd p i))
      (eqToIso (congrArg (G B) (pullback.lift_snd k r h)))
      (beta B r k i p h.symm hsq.flip)
    · intro M
      exact iso_projector_counit B (squareLift k r p i h)
        ((G B (pullback.snd p i)).obj M)
    · intro M
      rw [beta_inv_normalization B r k i p h.symm hsq.flip,
        beta_inv_normalization B (pullback.snd p i) (pullback.fst p i) i p
          pullback.condition.symm (IsPullback.of_hasPullback p i).flip]
      exact betaInv_source_factorization B (squareLift k r p i h)
        (pullback.fst p i) (pullback.snd p i) k r i p
        (pullback.lift_fst k r h) (pullback.lift_snd k r h) h
        pullback.condition.symm M
  · intro k' _ _ h'
    refine ⟨pullback.lift_snd k' (𝟙 S) h', ?_⟩
    intro C c _ hc M
    have hp := clopenDerived_section_projector B
      (squareLift k' (𝟙 S) p i h') c hc
    exact ⟨hp.2.2.2.1 M, (hp.2.2.2.2 M).2⟩

end AlgebraicGeometry.ProEtale.StrictTower
