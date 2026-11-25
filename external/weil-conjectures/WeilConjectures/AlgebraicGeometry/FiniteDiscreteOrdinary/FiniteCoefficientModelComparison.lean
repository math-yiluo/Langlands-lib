/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingPullbackFixed
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteScalarConstantModels
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModulePullbackEncoding
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import all WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import all Mathlib.Algebra.Category.Ring.Colimits
import all Mathlib.FieldTheory.IsAlgClosed.Basic
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import all Mathlib.Algebra.Category.ModuleCat.AB
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Point.Over
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all Mathlib.CategoryTheory.Functor.TypeValuedFlat
import all Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite constant models and finite-stalk constructibility

Source: blueprint main-20261015, chap-The-pro-etale-site,
sk-prop-integral-criterion-reductions.proof.md, second paragraph; Stacks Tags 099Y and 09AJ
(blueprint: lem-pe-finite-coefficient-model-comparison).

The coefficient encoding is the normalized section-action equivalence already supplied by
FiniteDiscreteOrdinary. The witness clauses retain each stratum and each cover. Arbitrary
constant values on empty covering objects are discarded before asserting their finiteness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The finite geometric-stalk clause of the existing ordinary constructibility definition,
without its separate local-constancy clause. No field characteristic is excluded.
Source: Stacks Tag 09AJ, definition-constructible
(blueprint: lem-pe-finite-coefficient-model-comparison). -/
def ordinaryFiniteStalks (T : Scheme.{u}) (F : Ordinary A T) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T),
    Finite (Scheme.proEtaleGeometricModuleStalk x (Scheme.proEtaleConstantRing T A) F)

/-- The ordinary local condition on one stratum, using the recorded localized-site
local constancy and actual geometric stalks, rather than etale origin or finite Tor amplitude.
Source: Stacks Tag 09AJ, definition-constructible
(blueprint: lem-pe-finite-coefficient-model-comparison). -/
def ordinaryFiniteLocalCondition (T : Scheme.{u}) (F : Ordinary A T) : Prop :=
  Scheme.IsLocallyConstantProEtaleModuleSheaf T A F ∧ ordinaryFiniteStalks A T F

/-- Finite constant ordinary models on a specified cover. Module pullback uses the canonical
constant-coefficient comparison, and the constant model is simultaneous ring/module
sheafification. This spells out the ordinary side of the same-cover comparison.
Source: Stacks Tag 099Y, lemma-compare-locally-constant
(blueprint: lem-pe-finite-coefficient-model-comparison). -/
def ordinaryFiniteCoverModels (T : Scheme.{u}) (F : Ordinary A T)
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage T) : Prop :=
  ∀ i : C.I₀, ∃ P : ModuleCat.{u + 1} (ULift.{u + 1} A), Finite P ∧
    Nonempty (Scheme.proEtaleConstantModulePullback (C.f i) A F ≅
      Scheme.proEtaleConstantModuleSheaf (C.X i) A P)

/-- Bounded constructibility in the intrinsic ordinary constant-ring module category:
standard bounded cohomology and the existing finite-stalk constructibility predicate in
every degree. This is the ordinary target of the comparison, with no Tor restriction.
Source: blueprint definition-constructible-sheaves, final paragraph; Stacks Tag 09AL
(blueprint: lem-pe-finite-coefficient-model-comparison). -/
def ordinaryIntrinsicBoundedConstructible [Finite A] (T : Scheme.{u}) :
    ObjectProperty (Scheme.proEtaleDerivedCategory T A) :=
  DerivedCategory.TStructure.t.bounded ⊓ fun K ↦ ∀ q : ℤ,
    Scheme.IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor (Ordinary A T) q).obj K)

/-- All clauses of the finite-coefficient comparison for the specified normalized encoding.
The stratum clauses are pointwise, so zero strata and empty strata are included. The global
ordinary predicate retains its recorded convention of a positive number of strata.
Source: blueprint sk-prop-integral-criterion-reductions.proof.md, second paragraph;
Stacks Tags 099Y and 09AJ (blueprint: lem-pe-finite-coefficient-model-comparison). -/
structure FiniteCoefficientModelComparison [Finite A] (X : Scheme.{u}) (e : Encoding A X) :
    Prop where
  /-- Constructibility agrees for the original sheaf and its section-action image. -/
  constructible : ∀ M : Internal A X,
    IsConstantModelConstructible (coefficient A) X M ↔
      Scheme.IsConstructibleProEtaleModuleSheaf X A (e.ordinary.functor.obj M)
  /-- On every fixed stratification, exactly the same strata satisfy the local conditions. -/
  strata : ∀ (M : Internal A X) (S : Scheme.Stratification X),
    (∀ i : Fin S.n, HasFiniteConstantLocalModel (coefficient A) (S.domain i)
      ((CondensedRing.upperStar (coefficient A) (S.immersion i)).obj M)) ↔
    ∀ i : Fin S.n, ordinaryFiniteLocalCondition A (S.domain i)
      (Scheme.proEtaleConstantModulePullback (S.immersion i) A (e.ordinary.functor.obj M))
  /-- A finite model cover remains the very same finite model cover in ordinary coordinates. -/
  covers : ∀ (M : Internal A X) (S : Scheme.Stratification X) (i : Fin S.n)
      (C : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain i)),
    HasFiniteConstantLocalModelOnCover (coefficient A)
      ((CondensedRing.upperStar (coefficient A) (S.immersion i)).obj M) C ↔
    ordinaryFiniteCoverModels A (S.domain i)
      (Scheme.proEtaleConstantModulePullback (S.immersion i) A (e.ordinary.functor.obj M)) C
  /-- Every localized-site trivialization is retained on its nonempty members. This uses
  the full index universe of the recorded ordinary local-constancy definition. -/
  discardEmpty : ∀ (M : Internal A X) (S : Scheme.Stratification X) (i : Fin S.n)
      (I : Type (u + 1)) (W : I → (S.domain i).ProEt)
      (f : ∀ j : I, W j ⟶ Scheme.ProEt.mk (𝟙 (S.domain i)))
      (P : I → ModuleCat.{u + 1} (ULift.{u + 1} A)),
    Presieve.ofArrows W f ∈ (Scheme.ProEt.precoverage (S.domain i)).coverings _ →
    (∀ j : I,
      Nonempty ((Scheme.proEtaleConstantModulePullback (S.immersion i) A
        (e.ordinary.functor.obj M)).over (W j) ≅
          Scheme.proEtaleConstantModuleSheafOver (S.domain i) A (W j) (P j))) →
    ordinaryFiniteStalks A (S.domain i)
      (Scheme.proEtaleConstantModulePullback (S.immersion i) A (e.ordinary.functor.obj M)) →
    (Presieve.ofArrows (fun j : {j : I // Nonempty (W j).left} ↦ W j.val)
      (fun j ↦ f j.val) ∈ (Scheme.ProEt.precoverage (S.domain i)).coverings _) ∧
    ∀ j : I, Nonempty (W j).left → Finite (P j) ∧
      ∃ Q : Mod Ab.{u + 1} (scalarRingObj (coefficient A)),
        Mod.IsFinitelyPresented (scalarRingObj (coefficient A)) Q ∧
        Nonempty ((CondensedRing.upperStar (coefficient A) (W j).hom).obj
          ((CondensedRing.upperStar (coefficient A) (S.immersion i)).obj M) ≅
            (finiteConstantScalarExtension (coefficient A) (W j).left).obj Q)
  -- STATEMENT-DISPUTED: the former unparenthesized equivalence was false for b < a.
  /-- The actual termwise derived equivalence preserves and reflects each vanishing interval. -/
  intervals : ∀ (K : DerivedCategory (Internal A X)) (a b : ℤ), a ≤ b →
    ((∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Internal A X) q).obj K)) ↔
    (∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Ordinary A X) q).obj
        (e.ordinaryDerived.functor.obj K))))
  /-- Both bounded-constructible membership tests agree, without a finite-Tor condition. -/
  boundedConstructible : ∀ K : DerivedCategory (Internal A X),
    constantModelBoundedConstructible (coefficient A) X K ↔
      ordinaryIntrinsicBoundedConstructible A X (e.ordinaryDerived.functor.obj K)
  /-- The equivalence on the full subcategories is induced by the specified ambient functor. -/
  boundedEquivalence : ∃ d : ConstantModelBoundedConstructible (coefficient A) X ≌
      (ordinaryIntrinsicBoundedConstructible A X).FullSubcategory,
    Nonempty (d.functor ⋙ (ordinaryIntrinsicBoundedConstructible A X).ι ≅
      (constantModelBoundedConstructible (coefficient A) X).ι ⋙ e.ordinaryDerived.functor)

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem fixedRestriction_iso (T : Scheme.{u}) (F : Ordinary A T) :
    Nonempty ((fixedRestriction A T).obj F ≅ (Scheme.proEtaleModuleRestriction T A).obj F) := by
  let J := Scheme.ProEt.topology T
  let B := ULift.{u + 1} A
  let c := (constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
    (CommRingCat.of B)
  have hc : Scheme.proEtaleModuleScalarUnit T A ≫ c.hom.hom =
      toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of B)) := by
    change _ ≫ ((constantCommuteCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app
        (CommRingCat.of B)).hom = _
    erw [constantCommuteCompose_hom_app_hom]
    unfold Scheme.proEtaleModuleScalarUnit
    rw [← Category.assoc, sheafComposeIso_inv_fac]
    exact (toSheafify_naturality J
      (Functor.constComp T.ProEtᵒᵖ (CommRingCat.of B)
        (forget₂ CommRingCat RingCat)).hom).symm.trans (by rfl)
  have hci : toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of B)) ≫ c.inv.hom =
      Scheme.proEtaleModuleScalarUnit T A := by
    rw [← hc, Category.assoc]
    change _ ≫ (c.hom ≫ c.inv).hom = _
    rw [Iso.hom_inv_id]
    exact Category.comp_id _
  refine ⟨ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦ ?_) ?_)⟩
  · refine (show (((fixedRestriction A T).obj F).obj.obj U : Type (u + 1)) ≃ₗ[B]
        (((Scheme.proEtaleModuleRestriction T A).obj F).obj.obj U) from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun b m ↦ ?_ }).toModuleIso
    change (c.inv.hom.app U
      ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of B))).app U b)) •
        (show F.val.obj U from m) =
      (Scheme.proEtaleModuleScalarUnit T A).app U b • (show F.val.obj U from m)
    exact congrArg (fun r ↦ r • (show F.val.obj U from m))
      (ConcreteCategory.congr_hom (congr_app hci U) b)
  · intro U V f
    ext m
    rfl

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem discardEmpty_cover (T : Scheme.{u})
    (I : Type (u + 1)) (W : I → T.ProEt)
    (f : ∀ j : I, W j ⟶ Scheme.ProEt.mk (𝟙 T))
    (hf : Presieve.ofArrows W f ∈ (Scheme.ProEt.precoverage T).coverings _) :
    Presieve.ofArrows (fun j : {j : I // Nonempty (W j).left} ↦ W j.val)
      (fun j ↦ f j.val) ∈ (Scheme.ProEt.precoverage T).coverings _ := by
  classical
  have hw (j : I) : (f j).left = (W j).hom := by
    have h := MorphismProperty.Over.w (f j)
    exact (Category.comp_id _).symm.trans h
  rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hf ⊢
  change Presieve.ofArrows (fun j ↦ (W j).left) (fun j ↦ (f j).left) ∈
    Scheme.proetalePrecoverage T at hf
  change Presieve.ofArrows (fun j : {j : I // Nonempty (W j).left} ↦
    (W j.1).left) (fun j ↦ (f j.1).left) ∈ Scheme.proetalePrecoverage T
  simp only [hw] at hf ⊢
  let E : PreZeroHypercover T := ⟨I, fun j ↦ (W j).left, fun j ↦ (W j).hom⟩
  have : QuasiCompactCover E := Scheme.presieve₀_mem_qcPrecoverage_iff.mp hf.1
  let E' : PreZeroHypercover T :=
    ⟨{j : I // Nonempty (W j).left}, fun j ↦ (W j.1).left, fun j ↦ (W j.1).hom⟩
  have : QuasiCompactCover E' := by
    constructor
    intro V hV
    obtain ⟨n, a, U, hU, hcov⟩ :=
      QuasiCompactCover.exists_isAffineOpen_of_isCompact E hV.isCompact
    refine IsCompactOpenCovered.of_finite
      (fun j : {j : Fin n // Nonempty (W (a j)).left} ↦ ⟨a j.1, j.2⟩)
      (fun j ↦ U j.1) (fun j ↦ (hU j.1).isCompact) ?_
    rw [← hcov]
    ext x
    simp only [Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨j, y, hy, rfl⟩
      exact ⟨j.1, y, hy, rfl⟩
    · rintro ⟨j, y, hy, rfl⟩
      exact ⟨⟨j, ⟨y⟩⟩, y, hy, rfl⟩
  refine ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr ‹QuasiCompactCover E'›, ?_⟩
  rw [Scheme.ofArrows_mem_precoverage_iff]
  have hweak := hf.2
  rw [Scheme.ofArrows_mem_precoverage_iff] at hweak
  exact ⟨fun x ↦ by
    obtain ⟨j, y, hy⟩ := hweak.1 x
    exact ⟨⟨j, ⟨y⟩⟩, y, hy⟩, fun j ↦ (W j.1).prop⟩

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem finite_value_of_nonempty (T : Scheme.{u}) (F : Ordinary A T)
    (W : T.ProEt) (P : ModuleCat.{u + 1} (ULift.{u + 1} A))
    (e : F.over W ≅ Scheme.proEtaleConstantModuleSheafOver T A W P)
    (hs : ordinaryFiniteStalks A T F) (hw : Nonempty W.left) : Finite P := by
  classical
  let w : W.left := Classical.choice hw
  let Ω := AlgebraicClosure (W.left.residueField w)
  let y : Spec (.of Ω) ⟶ W.left := (Scheme.SpecToEquivOfField Ω _).2
    ⟨w, CommRingCat.ofHom (algebraMap (W.left.residueField w) Ω)⟩
  let x := y ≫ W.hom
  let Φ := AlgebraicGeometry.ProEtale.geometricPoint x
  let z : Φ.fiber.obj W := ⟨Over.homMk y rfl⟩
  let R := (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing T A)
  let a := Functor.whiskerLeft (Over.forget W).op (Scheme.proEtaleModuleScalarUnit T A)
  have hb := Scheme.proEtaleConstantRingUnit_over_locallyBijective T A W
  have : Presheaf.IsLocallyInjective ((Scheme.ProEt.topology T).over W) a := hb.1
  have : Presheaf.IsLocallySurjective ((Scheme.ProEt.topology T).over W) a := hb.2
  let E := Scheme.ConstantScalarComparison.restriction
    ((Scheme.ProEt.topology T).over W) (ULift.{u + 1} A) (R.over W) a
  have hc := Scheme.ConstantScalarComparison.constantComparisonHom_isIso
    ((Scheme.ProEt.topology T).over W) (ULift.{u + 1} A) (R.over W) a P
  let em : ((Scheme.proEtaleModuleRestriction T A).obj F).over W ≅
      (constantSheaf ((Scheme.ProEt.topology T).over W)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P :=
    E.mapIso e ≪≫
      (asIso (Scheme.ConstantScalarComparison.constantComparisonHom
        ((Scheme.ProEt.topology T).over W) (ULift.{u + 1} A) (R.over W) a P)).symm
  let estalk : Scheme.proEtaleGeometricFixedModuleStalk x (ULift.{u + 1} A)
      ((Scheme.proEtaleModuleRestriction T A).obj F) ≅ P :=
    AlgebraicGeometry.ProEtale.geometricStalkIsoFiber x _ _ ≪≫
      (AlgebraicGeometry.ProEtale.sheafFiberOverIso Φ z _ _).symm ≪≫
      (Φ.over z).sheafFiber.mapIso em ≪≫ (Φ.over z).sheafFiberConstantSheafIso P
  have : Finite (Scheme.proEtaleGeometricFixedModuleStalk x (ULift.{u + 1} A)
      ((Scheme.proEtaleModuleRestriction T A).obj F)) :=
    (Scheme.finite_stalk_iff T A F Ω x).mp (hs Ω x)
  exact Finite.of_equiv _ estalk.toLinearEquiv.toEquiv

private def fixedIso (T : Scheme.{u}) (e : Encoding A T) (F : Ordinary A T) :
    e.fixed.functor.obj F ≅ (Scheme.proEtaleModuleRestriction T A).obj F :=
  (eqToIso (congrArg (fun G ↦ G.obj F) e.fixed_functor)) ≪≫
    (fixedRestriction_iso A T F).some

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem intrinsicConstant_iff_fixed (T : Scheme.{u}) (F : Ordinary A T) :
    (∃ P : ModuleCat.{u + 1} (ULift.{u + 1} A), Finite P ∧
      Nonempty (F ≅ Scheme.proEtaleConstantModuleSheaf T A P)) ↔
    ∃ P : ModuleCat.{u + 1} (ULift.{u + 1} A), Finite P ∧
      Nonempty ((Scheme.proEtaleModuleRestriction T A).obj F ≅
        (constantSheaf (Scheme.ProEt.topology T)
          (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P) := by
  let J := Scheme.ProEt.topology T
  let B := ULift.{u + 1} A
  let R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (Scheme.proEtaleConstantRing T A)
  let a := Scheme.proEtaleModuleScalarUnit T A
  have : Presheaf.IsLocallyInjective J a := (Scheme.proEtaleConstantRingUnit_locallyBijective T A).1
  have : Presheaf.IsLocallySurjective J a :=
    (Scheme.proEtaleConstantRingUnit_locallyBijective T A).2
  let E := Scheme.ConstantScalarComparison.restriction J B R a
  have h (P : ModuleCat.{u + 1} B) :
      IsIso (Scheme.ConstantScalarComparison.constantComparisonHom J B R a P) :=
    Scheme.ConstantScalarComparison.constantComparisonHom_isIso J B R a P
  constructor
  · rintro ⟨P, hP, ⟨e⟩⟩
    exact ⟨P, hP, ⟨E.mapIso e ≪≫
      (asIso (Scheme.ConstantScalarComparison.constantComparisonHom J B R a P)).symm⟩⟩
  · rintro ⟨P, hP, ⟨e⟩⟩
    exact ⟨P, hP, ⟨(Scheme.ConstantScalarComparison.restrictionFullyFaithful J B R a).preimageIso
      (e ≪≫ asIso (Scheme.ConstantScalarComparison.constantComparisonHom J B R a P))⟩⟩

private def encodedPullbackIso [Finite A] [DiscreteTopology A]
    {T U : Scheme.{u}} (f : U ⟶ T) (eT : Encoding A T) (eU : Encoding A U)
    (M : Internal A T) :
    (eU.ordinary.functor ⋙ eU.fixed.functor).obj
      ((CondensedRing.upperStar (coefficient A) f).obj M) ≅
      (Scheme.proEtaleModuleRestriction U A).obj
        (Scheme.proEtaleConstantModulePullback f A (eT.ordinary.functor.obj M)) :=
  (encoding_pullback_fixed A f eT eU M).some ≪≫
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).mapIso
      (fixedIso A T eT (eT.ordinary.functor.obj M)) ≪≫
    (Scheme.proEtaleModuleRestriction_pullback f A (eT.ordinary.functor.obj M)).some.symm

private theorem coverModels_iff [Finite A] [DiscreteTopology A]
    (E : ∀ T : Scheme.{u}, Encoding A T) (T : Scheme.{u}) (M : Internal A T)
    (F : Ordinary A T)
    (e : (E T).fixed.functor.obj ((E T).ordinary.functor.obj M) ≅
      (Scheme.proEtaleModuleRestriction T A).obj F)
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage T) :
    HasFiniteConstantLocalModelOnCover (coefficient A) M C ↔
      ordinaryFiniteCoverModels A T F C := by
  refine forall_congr' fun j ↦ ?_
  let V := C.X j
  let h : ((E V).ordinary.functor ⋙ (E V).fixed.functor).obj
      ((CondensedRing.upperStar (coefficient A) (C.f j)).obj M) ≅
      (Scheme.proEtaleModuleRestriction V A).obj
        (Scheme.proEtaleConstantModulePullback (C.f j) A F) :=
    (encoding_pullback_fixed A (C.f j) (E T) (E V) M).some ≪≫
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (C.f j)).mapIso e ≪≫
      (Scheme.proEtaleModuleRestriction_pullback (C.f j) A F).some.symm
  refine (finite_scalar_model_iff_constant A V (E V) _).trans ?_
  refine Iff.trans ?_ (intrinsicConstant_iff_fixed A V _).symm
  constructor
  · rintro ⟨P, hP, ⟨hM⟩⟩
    exact ⟨P, hP, ⟨h.symm ≪≫ hM⟩⟩
  · rintro ⟨P, hP, ⟨hF⟩⟩
    exact ⟨P, hP, ⟨h ≪≫ hF⟩⟩

private theorem internalModel_on_object [Finite A] [DiscreteTopology A]
    (E : ∀ T : Scheme.{u}, Encoding A T) (T : Scheme.{u})
    (N : Internal A T) (F : Ordinary A T)
    (hNF : ((E T).ordinary.functor ⋙ (E T).fixed.functor).obj N ≅
      (Scheme.proEtaleModuleRestriction T A).obj F)
    (W : T.ProEt) (P : ModuleCat.{u + 1} (ULift.{u + 1} A)) [Finite P]
    (e : F.over W ≅ Scheme.proEtaleConstantModuleSheafOver T A W P) :
    ∃ Q : Mod Ab.{u + 1} (scalarRingObj (coefficient A)),
      Mod.IsFinitelyPresented (scalarRingObj (coefficient A)) Q ∧
      Nonempty ((CondensedRing.upperStar (coefficient A) W.hom).obj N ≅
        (finiteConstantScalarExtension (coefficient A) W.left).obj Q) := by
  let R := (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing T A)
  let a := Functor.whiskerLeft (Over.forget W).op (Scheme.proEtaleModuleScalarUnit T A)
  have hb := Scheme.proEtaleConstantRingUnit_over_locallyBijective T A W
  have : Presheaf.IsLocallyInjective ((Scheme.ProEt.topology T).over W) a := hb.1
  have : Presheaf.IsLocallySurjective ((Scheme.ProEt.topology T).over W) a := hb.2
  let H := Scheme.ConstantScalarComparison.restriction
    ((Scheme.ProEt.topology T).over W) (ULift.{u + 1} A) (R.over W) a
  have hc := Scheme.ConstantScalarComparison.constantComparisonHom_isIso
    ((Scheme.ProEt.topology T).over W) (ULift.{u + 1} A) (R.over W) a P
  let em : ((Scheme.proEtaleModuleRestriction T A).obj F).over W ≅
      (constantSheaf ((Scheme.ProEt.topology T).over W)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj P :=
    H.mapIso e ≪≫
      (asIso (Scheme.ConstantScalarComparison.constantComparisonHom
        ((Scheme.ProEt.topology T).over W) (ULift.{u + 1} A) (R.over W) a P)).symm
  have : (Scheme.ProEt.sliceEquiv T W).inverse.IsDenseSubsite
      (Scheme.ProEt.topology W.left) ((Scheme.ProEt.topology T).over W) :=
    Scheme.ProEt.sliceDense T W
  let S := (Scheme.ProEt.sliceEquiv T W).sheafCongr
    ((Scheme.ProEt.topology T).over W) (Scheme.ProEt.topology W.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))
  let r : S.functor.obj (((Scheme.proEtaleModuleRestriction T A).obj F).over W) ≅
      (localizationRestriction (ModuleCat.{u + 1} (ULift.{u + 1} A)) W.hom W.prop).obj
        ((Scheme.proEtaleModuleRestriction T A).obj F) :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  let c := ((Scheme.ProEt.sliceEquiv T W).constantSheafSheafCongrIso
    ((Scheme.ProEt.topology T).over W) (Scheme.ProEt.topology W.left)
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) (Over.mkIdTerminal (X := W))).app P
  apply (finite_scalar_model_iff_constant A W.left (E W.left) _).mpr
  refine ⟨P, inferInstance, ⟨?_⟩⟩
  exact (encoding_pullback_fixed A W.hom (E T) (E W.left) N).some ≪≫
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) W.hom).mapIso hNF ≪≫
    (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} (ULift.{u + 1} A))
      W.hom W.prop).app _ ≪≫ r.symm ≪≫ S.functor.mapIso em ≪≫ c

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem localModel_iff_finiteLocal [Finite A] (T : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    ordinaryLocalModel A T F ↔ IsFiniteLocallyConstant (ULift.{u + 1} A) F := by
  constructor
  · rintro ⟨C, hC⟩
    let D : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage T :=
      C.reindex Equiv.ulift.{u + 1, u}
    refine ⟨D.I₀, D.X, D.f, D.mem₀, fun i ↦ ?_⟩
    obtain ⟨P, _, e⟩ := hC i.down
    exact ⟨P, Module.Finite.of_finite, e⟩
  · rintro ⟨I, W, f, hf, h⟩
    let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage T := ⟨⟨I, W, f⟩, hf⟩
    have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
    refine ⟨C.restrictIndexOfSmall.{u}, fun i ↦ ?_⟩
    obtain ⟨P, _, e⟩ := h (Precoverage.ZeroHypercover.Small.restrictFun C i)
    exact ⟨P, Module.finite_of_finite (ULift.{u + 1} A), e⟩

private theorem localCondition_iff [Finite A] [DiscreteTopology A]
    (T : Scheme.{u}) (e : Encoding A T) (M : Internal A T) :
    HasFiniteConstantLocalModel (coefficient A) T M ↔
      ordinaryFiniteLocalCondition A T (e.ordinary.functor.obj M) := by
  have hl : HasFiniteConstantLocalModel (coefficient A) T M ↔
      ordinaryLocalModel A T ((e.ordinary.functor ⋙ e.fixed.functor).obj M) := by
    refine (finiteConstantLocalModel_iff_exists_cover (coefficient A) M).trans ?_
    apply exists_congr
    intro C
    refine forall_congr' fun i ↦ ?_
    let eU := (encoding_exists A (C.X i)).some
    let h := (encoding_pullback_fixed A (C.f i) e eU M).some
    refine (finite_scalar_model_iff_constant A (C.X i) eU _).trans ?_
    constructor
    · rintro ⟨P, hP, ⟨j⟩⟩
      exact ⟨P, hP, ⟨h.symm ≪≫ j⟩⟩
    · rintro ⟨P, hP, ⟨j⟩⟩
      exact ⟨P, hP, ⟨h ≪≫ j⟩⟩
  refine hl.trans ?_
  refine (localModel_iff_finiteLocal A T _).trans ?_
  let h := fixedIso A T e (e.ordinary.functor.obj M)
  refine Iff.trans ?_ (Scheme.finiteLocal_iff T A _)
  exact ⟨isFiniteLocallyConstant_of_iso h, isFiniteLocallyConstant_of_iso h.symm⟩

private theorem strataComparison [Finite A] [DiscreteTopology A]
    (E : ∀ T : Scheme.{u}, Encoding A T) (X : Scheme.{u}) (M : Internal A X)
    (S : Scheme.Stratification X) :
    (∀ i : Fin S.n, HasFiniteConstantLocalModel (coefficient A) (S.domain i)
      ((CondensedRing.upperStar (coefficient A) (S.immersion i)).obj M)) ↔
    ∀ i : Fin S.n, ordinaryFiniteLocalCondition A (S.domain i)
      (Scheme.proEtaleConstantModulePullback (S.immersion i) A
        ((E X).ordinary.functor.obj M)) := by
  refine forall_congr' fun i ↦ ?_
  let N := (CondensedRing.upperStar (coefficient A) (S.immersion i)).obj M
  let F := Scheme.proEtaleConstantModulePullback (S.immersion i) A
    ((E X).ordinary.functor.obj M)
  let h := (fixedIso A (S.domain i) (E (S.domain i))
    ((E (S.domain i)).ordinary.functor.obj N)).symm ≪≫
      encodedPullbackIso A (S.immersion i) (E X) (E (S.domain i)) M
  refine (localCondition_iff A (S.domain i) (E (S.domain i)) N).trans ?_
  refine (Scheme.finiteLocal_iff (S.domain i) A _).symm.trans ?_
  exact (Iff.intro (isFiniteLocallyConstant_of_iso h)
    (isFiniteLocallyConstant_of_iso h.symm)).trans (Scheme.finiteLocal_iff _ A F)

private theorem sheafConstructibility [Finite A] [DiscreteTopology A]
    (E : ∀ T : Scheme.{u}, Encoding A T) (X : Scheme.{u}) [IsNoetherian X]
    (M : Internal A X) :
    IsConstantModelConstructible (coefficient A) X M ↔
      Scheme.IsConstructibleProEtaleModuleSheaf X A ((E X).ordinary.functor.obj M) := by
  have hqc : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, ite_eq_left hqc]
  constructor
  · rintro ⟨S, hS⟩
    have h := (strataComparison A E X M S).mp hS
    let F := ((E X).ordinary.functor ⋙ (E X).fixed.functor).obj M
    have hc : IsConstructible (ULift.{u + 1} A) F := by
      refine ⟨S, fun i ↦ ?_⟩
      have hi := (Scheme.finiteLocal_iff (S.domain i) A _).mpr (h i)
      let e := (Scheme.proEtaleModuleRestriction_pullback (S.immersion i) A
        ((E X).ordinary.functor.obj M)).some ≪≫
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (S.immersion i)).mapIso
          (fixedIso A X (E X) ((E X).ordinary.functor.obj M)).symm
      exact isFiniteLocallyConstant_of_iso e hi
    exact (Scheme.proEtaleModuleRestriction_constructible_iff X A _).mpr
      (isConstructible_of_iso (fixedIso A X (E X) _) hc)
  · rintro ⟨S, hn, hS⟩
    exact ⟨S, (strataComparison A E X M S).mpr hS⟩

omit [TopologicalSpace A] [IsTopologicalRing A] in
private theorem constructible_of_iso [Finite A] (T : Scheme.{u})
    {F G : Ordinary A T} (e : F ≅ G)
    (hF : Scheme.IsConstructibleProEtaleModuleSheaf T A F) :
    Scheme.IsConstructibleProEtaleModuleSheaf T A G := by
  obtain ⟨S, hn, hS⟩ := hF
  refine ⟨S, hn, fun i ↦ ?_⟩
  let e' := (Scheme.proEtaleConstantRingPullback A (S.immersion i)).mapIso e
  obtain ⟨I, U, f, hc, ht⟩ := (hS i).1
  refine ⟨⟨I, U, f, hc, fun j ↦ ?_⟩, ?_⟩
  · obtain ⟨P, ⟨hP⟩⟩ := ht j
    exact ⟨P, ⟨(SheafOfModules.overFunctor _ (U j)).mapIso e'.symm ≪≫ hP⟩⟩
  · intro Ω _ _ y
    let E := Scheme.geometricRingModuleStalkFunctor y
      (Scheme.proEtaleConstantRing (S.domain i) A)
    have : Finite (E.obj ((Scheme.proEtaleConstantRingPullback A
        (S.immersion i)).obj F)) := (hS i).2 Ω y
    exact Finite.of_injective (E.mapIso e'.symm).toLinearEquiv
      (E.mapIso e'.symm).toLinearEquiv.injective

private theorem derived_intervals (X : Scheme.{u}) (e : Encoding A X)
    (K : DerivedCategory (Internal A X)) (a b : ℤ) :
    (∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Internal A X) q).obj K)) ↔
    (∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor (Ordinary A X) q).obj
        (e.ordinaryDerived.functor.obj K))) := by
  constructor
  · intro h q hq
    exact e.ordinary.functor.isZero_homologyFunctor_mapDerivedCategory_obj (h q hq)
  · intro h q hq
    exact e.ordinary.functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      (h q hq)

private theorem derived_boundedConstructible [Finite A] (X : Scheme.{u}) (e : Encoding A X)
    (hc : ∀ M : Internal A X, IsConstantModelConstructible (coefficient A) X M ↔
      Scheme.IsConstructibleProEtaleModuleSheaf X A (e.ordinary.functor.obj M))
    (K : DerivedCategory (Internal A X)) :
    constantModelBoundedConstructible (coefficient A) X K ↔
      ordinaryIntrinsicBoundedConstructible A X (e.ordinaryDerived.functor.obj K) := by
  have hb : DerivedCategory.TStructure.t.bounded K ↔
      DerivedCategory.TStructure.t.bounded (e.ordinaryDerived.functor.obj K) :=
    ⟨e.ordinary.functor.bounded_mapDerivedCategory_obj,
      e.ordinary.functor.bounded_of_bounded_mapDerivedCategory_obj⟩
  refine and_congr hb (forall_congr' fun q ↦ ?_)
  let h := (e.ordinary.functor.mapDerivedCategoryHomologyFunctorIso q).app K
  exact (hc _).trans ⟨constructible_of_iso A X h, constructible_of_iso A X h.symm⟩

private theorem derived_boundedEquivalence [Finite A] (X : Scheme.{u}) (e : Encoding A X)
    (hc : ∀ K : DerivedCategory (Internal A X),
      constantModelBoundedConstructible (coefficient A) X K ↔
        ordinaryIntrinsicBoundedConstructible A X (e.ordinaryDerived.functor.obj K)) :
    ∃ d : ConstantModelBoundedConstructible (coefficient A) X ≌
      (ordinaryIntrinsicBoundedConstructible A X).FullSubcategory,
      Nonempty (d.functor ⋙ (ordinaryIntrinsicBoundedConstructible A X).ι ≅
        (constantModelBoundedConstructible (coefficient A) X).ι ⋙
          e.ordinaryDerived.functor) := by
  let Q := ordinaryIntrinsicBoundedConstructible A X
  let : Q.IsClosedUnderIsomorphisms := ⟨by
    intro K L h hK
    exact ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso h hK.1,
      fun q ↦ constructible_of_iso A X ((DerivedCategory.homologyFunctor _ q).mapIso h)
        (hK.2 q)⟩⟩
  have hp : Q.inverseImage e.ordinaryDerived.functor =
      constantModelBoundedConstructible (coefficient A) X := by
    funext K
    exact propext (hc K).symm
  exact ⟨e.ordinaryDerived.congrFullSubcategory hp, ⟨Iso.refl _⟩⟩

/-- Finite discrete coefficients identify finite constant local models with locally constant
finite-stalk constructibility, retaining strata, covers after deletion of empty objects, and
all cohomological vanishing intervals under the induced bounded-constructible equivalence.

Source: blueprint main-20261015, chap-The-pro-etale-site,
sk-prop-integral-criterion-reductions.proof.md, second paragraph
(blueprint: lem-pe-finite-coefficient-model-comparison).

Proof following the seven DAG steps:
1. Use lem-sf-module-object-ordinary-coefficient-equivalence for the normalized Encoding.
Its ringIso is the canonical constant-coefficient identification. The section-action
construction retains the abelian sheaf. By lem-sfb-internal-module-operations-transport,
restriction along each stratum immersion and covering arrow agrees under this encoding.
2. Over a finite ring A, a finitely presented module is a quotient of finite A^n and hence
finite. Conversely the finite free module A^P surjects onto a finite module P. Its kernel R
is finite, so A^R maps onto that kernel, giving a finite presentation. Finite generation
likewise agrees with finiteness of the underlying set. This includes zero rings.
3. With discrete finite coefficients, the scalar local model is A_U tensor_{A_U} P_U,
isomorphic to P_U by a tensor m mapping to am and inverse m mapping to 1 tensor m. These
restriction-compatible maps respect the balancing relations, retaining the same cover.
4. Finite constant values on a cover give local constancy and finite geometric stalks by
lem-weil-pbc-proetale-finite-model-stalks, on each original stratum.
5. Conversely discard the empty objects of any ordinary trivializing cover. They contribute
no points or affine opens to its covering condition, so the remaining family still covers.
Choose a geometric point on each remaining object. By
lem-sfb-proetale-object-inverse-image-restriction the localized restriction is inverse image.
Then lem-pur-proetale-inverse-image-stalk and lem-weil-proetale-constant-sheaf-stalk identify
the constant value with a finite stalk. Step 2 makes this value finitely presented, and
step 3 supplies the internal finite scalar model on precisely that cover member.
6. Apply steps 4 and 5 on each stratum of any finite constructible locally closed
stratification. On a Noetherian scheme the global and affine-local conventions agree.
The empty scheme is allowed: an empty stratum imposes no condition, and a single empty
stratum also meets the ordinary definition's positive-number convention. Zero sheaves and
empty covering families on the empty scheme are included.
7. The termwise extension of the exact equivalence commutes with cohomology: it preserves
kernels, images and cokernels, and the inverse gives reflection of zero cohomology. Thus
every vanishing interval is unchanged. Step 6 identifies every cohomology sheaf's
constructibility. Restrict the equivalence and its inverse to the full bounded
constructible subcategories; their unit and counit give the asserted equivalence and its
commuting comparison with the ambient functor. No completeness or Tor bound is used.
-/
theorem finiteCoefficientModelComparison [Finite A] [DiscreteTopology A]
    (X : Scheme.{u}) [IsNoetherian X] :
    ∃ e : Encoding A X, FiniteCoefficientModelComparison A X e := by
  classical
  let E : ∀ T : Scheme.{u}, Encoding A T := fun T ↦ (encoding_exists A T).some
  refine ⟨E X, ?_⟩
  have hc := sheafConstructibility A E X
  have hb := derived_boundedConstructible A X (E X) hc
  refine
    { constructible := hc
      strata := strataComparison A E X
      covers := ?_
      discardEmpty := ?_
      intervals := fun K a b _ ↦ derived_intervals A X (E X) K a b
      boundedConstructible := hb
      boundedEquivalence := derived_boundedEquivalence A X (E X) hb }
  · intro M S i C
    exact coverModels_iff A E (S.domain i) _ _
      (encodedPullbackIso A (S.immersion i) (E X) (E (S.domain i)) M) C
  · intro M S i I W f P hf he hs
    refine ⟨discardEmpty_cover (S.domain i) I W f hf, fun j hj ↦ ?_⟩
    obtain ⟨ej⟩ := he j
    have hP : Finite (P j) := finite_value_of_nonempty A (S.domain i) _ _ _ ej hs hj
    have := hP
    exact ⟨hP, internalModel_on_object A E (S.domain i) _ _
      (encodedPullbackIso A (S.immersion i) (E X) (E (S.domain i)) M) (W j) (P j) ej⟩

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
