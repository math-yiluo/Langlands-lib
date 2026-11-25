/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients
public import WeilConjectures.CategoryTheory.PowerTransition.PowerTransitionFunctor

import all WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import all WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import all WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all WeilConjectures.SixFunctors.Etale.Derived.Hom
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplex
import all WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.Algebra.Category.Grp.Abelian
import all WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import all WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import all WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import all WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplexProjections
import all WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import all Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import all WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import all WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import all Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import all Mathlib.Algebra.Category.Grp.EpiMono
import all WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import all Mathlib.CategoryTheory.Sites.Abelian
import all Mathlib.Algebra.Homology.Functor
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Limits.Final
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.Algebra.Module.ZMod

/-! # The ordinary quotient of a tower by its variable positive powers -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local irreducible] HasDerivedCategory.standard

private abbrev sequenceRing (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  SemilinearSections.ring.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (fun n ↦ (Rrings l T).obj (op n))
      (fun n ↦ (Rrings l T).map (homOfLE (Nat.le_succ n)).op))

private def rawRings (l : ℕ) : ℕᵒᵖ ⥤ CommRingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n ↦ CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))
    (fun n ↦ CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1))) _).comp
        ULift.ringEquiv.toRingHom)))

private abbrev rawRing (l : ℕ) (T : Scheme.{u}) : (ℕ × T.ProEt)ᵒᵖ ⥤ RingCat.{u + 1} :=
  (prodOpEquiv (C := ℕ) (D := T.ProEt)).functor ⋙
    Functor.uncurry.obj (rawRings.{u} l ⋙ (Functor.const T.ProEtᵒᵖ)) ⋙
      forget₂ CommRingCat RingCat

private theorem uliftZMod_hom_ext {n : ℕ} {A : RingCat.{u + 1}}
    (f g : RingCat.of (ULift.{u + 1} (ZMod n)) ⟶ A) : f = g := by
  apply RingCat.hom_ext
  apply (RingHom.cancel_right
    (f := (ULift.ringEquiv (R := ZMod n)).symm.toRingHom)
    (fun x ↦ ⟨x.down, rfl⟩)).mp
  exact Subsingleton.elim _ _

private def ringUnit (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    rawRing l T ⟶ (sequenceRing l T).obj where
  app X := (forget₂ CommRingCat RingCat).map
    ((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (X.unop.1 + 1))))))).app (op X.unop.2))
  naturality _ _ _ := uliftZMod_hom_ext _ _

private instance ringUnit_surjective (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    Presheaf.IsLocallySurjective (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (ringUnit l T) := by
  constructor
  intro X x
  change (Presheaf.imageSieve (ringUnit l T) x).functorPullback
    (Prod.sectR X.1 T.ProEt) ∈ Scheme.ProEt.topology T X.2
  let η := toSheafify (Scheme.ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (X.1 + 1))))))
  apply (Scheme.ProEt.topology T).superset_covering _ (Presheaf.imageSieve_mem _ η x)
  intro V f hf
  obtain ⟨a, ha⟩ := hf
  refine ⟨a, ?_⟩
  change η.app (op V) a =
    ((sequenceRing l T).obj.map ((Prod.sectR X.1 T.ProEt).map f).op) x
  change η.app (op V) a =
    (((SemilinearSections.rings.{u + 1, u, u + 1} _ _ _).map (𝟙 (op X.1))).hom.app
      (op X.2) ≫ ((Rlevel l T X.1).obj.map f.op)) x
  rw [CategoryTheory.Functor.map_id]
  exact ha

private instance ringUnit_injective (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    Presheaf.IsLocallyInjective (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (ringUnit l T) := by
  constructor
  intro X x y h
  obtain ⟨X⟩ := X
  change (Presheaf.equalizerSieve x y).functorPullback
    (Prod.sectR X.1 T.ProEt) ∈ Scheme.ProEt.topology T X.2
  let η := toSheafify (Scheme.ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (X.1 + 1))))))
  apply (Scheme.ProEt.topology T).superset_covering _
    (Presheaf.equalizerSieve_mem _ η x y h)
  intro V f hf
  change (rawRing l T).map ((Prod.sectR X.1 T.ProEt).map f).op x =
    (rawRing l T).map ((Prod.sectR X.1 T.ProEt).map f).op y
  change ((forget₂ CommRingCat RingCat).map ((rawRings.{u} l).map (𝟙 (op X.1)))) x =
    ((forget₂ CommRingCat RingCat).map ((rawRings.{u} l).map (𝟙 (op X.1)))) y
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  exact hf

private theorem residue_annihilates (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (M : Systems T (Rrings l T)) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) : l ^ (n + 1) • x = 0 := by
  let α := ringUnit l T
  have h : ((l ^ (n + 1) : ℕ) : (rawRing l T).obj (op (n, U.unop))) = 0 :=
    ULift.ext (by
      change ((l ^ (n + 1) : ℕ) : ZMod (l ^ (n + 1))) = 0
      exact ZMod.natCast_self _)
  have h' := map_natCast (α.app (op (n, U.unop))).hom (l ^ (n + 1))
  rw [← Nat.cast_smul_eq_nsmul (R := (sequenceRing l T).obj.obj (op (n, U.unop))),
    ← h', h, map_zero, zero_smul]

private theorem nsmul_transport {A B : AddCommGrpCat.{u + 1}} (e : A = B) (k : ℕ)
    (h : ∀ x : B, k • x = 0) (x : A) : k • x = 0 := by
  subst B
  exact h x

private theorem unit_zero (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Reduction T (Rrings l T)) (X : Ab T) :
    (PowerTransition.multiplication l).app X ≫ r.model.adjunction.unit.app X = 0 := by
  ext n U x
  change ((r.model.adjunction.unit.app X).app n).hom.app U
    ((((PowerTransition.multiplication l).app X).app n).hom.app U x) = 0
  change ((r.model.adjunction.unit.app X).app n).hom.app U (l ^ (n.unop + 1) • x) = 0
  erw [map_nsmul]
  exact nsmul_transport (r.forget.sections (r.ordinary.obj X) n.unop U) _
    (residue_annihilates l T (r.ordinary.obj X) n.unop U) _

private abbrev moduleLevel {l : ℕ} [Fact l.Prime] {T : Scheme.{u}}
    (M : Systems T (Rrings l T)) (n : ℕ) : DiagonalAb T :=
  ((Prod.sectR n T.ProEt).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Scheme.ProEt.topology T) (coefficientSequenceTopology (Scheme.ProEt.topology T))).obj
      ((SheafOfModules.toSheaf _).obj M)

private def moduleTower {l : ℕ} [Fact l.Prime] {T : Scheme.{u}}
    (M : Systems T (Rrings l T)) : Ab T where
  obj n := moduleLevel M n.unop
  map {n m} f := ⟨
    { app U := M.val.presheaf.map (Prod.mkHom f.unop (𝟙 U.unop)).op
      naturality U V g := by
        change M.val.presheaf.map (Prod.mkHom (𝟙 n.unop) g.unop).op ≫
            M.val.presheaf.map (Prod.mkHom f.unop (𝟙 V.unop)).op =
          M.val.presheaf.map (Prod.mkHom f.unop (𝟙 U.unop)).op ≫
            M.val.presheaf.map (Prod.mkHom (𝟙 m.unop) g.unop).op
        rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
        congr 1 }⟩
  map_id n := by
    ext U x
    exact ConcreteCategory.congr_hom (M.val.presheaf.map_id (op (n.unop, U.unop))) x
  map_comp f g := by
    ext U x
    apply ConcreteCategory.congr_hom (f :=
      M.val.presheaf.map (Prod.mkHom (f ≫ g).unop (𝟙 U.unop)).op) _ x
    change M.val.presheaf.map (Prod.mkHom (f ≫ g).unop (𝟙 U.unop)).op =
      M.val.presheaf.map (Prod.mkHom f.unop (𝟙 U.unop)).op ≫
        M.val.presheaf.map (Prod.mkHom g.unop (𝟙 U.unop)).op
    rw [← Functor.map_comp, ← op_comp]
    congr 1

private def moduleTowerMap {l : ℕ} [Fact l.Prime] {T : Scheme.{u}}
    {M N : Systems T (Rrings l T)} (f : M ⟶ N) : moduleTower M ⟶ moduleTower N where
  app n := ⟨Functor.whiskerLeft (Prod.sectR n.unop T.ProEt).op
    ((PresheafOfModules.toPresheaf _).map f.val)⟩
  naturality n m g := by
    ext U x
    exact ConcreteCategory.congr_hom
      (((PresheafOfModules.toPresheaf _).map f.val).naturality
        (Prod.mkHom g.unop (𝟙 U.unop)).op) x

private theorem transport_map {A B M N : AddCommGrpCat.{u + 1}}
    (hA : A = M) (hB : B = N) (f : A ⟶ B) (g : M ⟶ N)
    (h : HEq f.hom g.hom) : f ≫ eqToHom hB = eqToHom hA ≫ g := by
  subst A
  subst B
  simpa using AddCommGrpCat.hom_ext (eq_of_heq h)

private def forgetIso {l : ℕ} [Fact l.Prime] {T : Scheme.{u}}
    (F : Forget T (Rrings l T)) (M : Systems T (Rrings l T)) :
    F.F.obj M ≅ moduleTower M :=
  NatIso.ofComponents (fun n ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ eqToIso (F.sections M n.unop U)) (by
      intro U V f
      exact transport_map (F.sections M n.unop U) (F.sections M n.unop V) _ _
        (F.restrictions M n.unop f)))) (by
    intro n m f
    ext U x
    apply ConcreteCategory.congr_hom _ x
    exact transport_map (F.sections M n.unop U) (F.sections M m.unop U) _ _
      (F.transitions M (leOfHom f.unop) U))

private theorem forgetIso_map {l : ℕ} [Fact l.Prime] {T : Scheme.{u}}
    (F : Forget T (Rrings l T)) {M N : Systems T (Rrings l T)} (f : M ⟶ N) :
    F.F.map f ≫ (forgetIso F N).hom = (forgetIso F M).hom ≫ moduleTowerMap f := by
  ext n U x
  apply ConcreteCategory.congr_hom _ x
  exact transport_map (F.sections M n.unop U) (F.sections N n.unop U) _ _
    (F.morphisms f n.unop U)

private abbrev towerPresheaf {T : Scheme.{u}} (X : Ab T) :
    (ℕ × T.ProEt)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (prodOpEquiv (C := ℕ) (D := T.ProEt)).functor ⋙
    Functor.uncurry.obj (X ⋙ sheafToPresheaf _ _)

private theorem uncurry_slice {T : Scheme.{u}}
    (F : ℕᵒᵖ ⥤ T.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n : ℕ) :
    (Prod.sectR n T.ProEt).op ⋙ (prodOpEquiv (C := ℕ) (D := T.ProEt)).functor ⋙
      Functor.uncurry.obj F = F.obj (op n) := by
  apply CategoryTheory.Functor.ext
    (F := (Prod.sectR n T.ProEt).op ⋙ (prodOpEquiv (C := ℕ) (D := T.ProEt)).functor ⋙
      Functor.uncurry.obj F) (G := F.obj (op n)) (fun _ ↦ rfl) ?_
  intro U V f
  change (F.map (𝟙 (op n))).app U ≫ (F.obj (op n)).map f =
    𝟙 _ ≫ (F.obj (op n)).map f ≫ 𝟙 _
  rw [CategoryTheory.Functor.map_id]
  simp

private theorem additive_natCast_smul {R S A B : Type (u + 1)} [Ring R] [Ring S]
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module S B]
    (f : A →+ B) (k : ℕ) (x : A) : f ((k : R) • x) = (k : S) • f x := by
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  exact map_nsmul f _ _

private def towerSheaf {T : Scheme.{u}} (X : Ab T) :
    Sheaf (coefficientSequenceTopology (Scheme.ProEt.topology T)) AddCommGrpCat.{u + 1} :=
  ⟨towerPresheaf X, by
    intro A
    apply SemilinearSections.sequence_isSheaf_of_slices
    intro n
    dsimp only [towerPresheaf]
    rw [← Functor.assoc]
    change Presieve.IsSheaf (Scheme.ProEt.topology T)
      (((Prod.sectR n T.ProEt).op ⋙ (prodOpEquiv (C := ℕ) (D := T.ProEt)).functor ⋙
        Functor.uncurry.obj (X ⋙ sheafToPresheaf _ _)) ⋙ coyoneda.obj (op A))
    rw [uncurry_slice]
    exact (X.obj (op n)).property A⟩

private theorem rawRing_natCast (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (U : (ℕ × T.ProEt)ᵒᵖ) (a : (rawRing l T).obj U) :
    ∃ k : ℕ, a = (k : (rawRing l T).obj U) := by
  have hn : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  refine ⟨a.down.val, ULift.ext ?_⟩
  change a.down = (a.down.val : ZMod (l ^ (U.unop.1 + 1)))
  exact (ZMod.natCast_zmod_val _).symm

private def rawModule (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (X : Ab T)
    (hX : ∀ (n : ℕ) (U : T.ProEtᵒᵖ) (x : (X.obj (op n)).obj.obj U),
      l ^ (n + 1) • x = 0) : PresheafOfModules.{u + 1} (rawRing l T) := by
  letI : ∀ V : (ℕ × T.ProEt)ᵒᵖ,
      Module (ZMod (l ^ (V.unop.1 + 1))) ((towerPresheaf X).obj V) :=
    fun V ↦ AddCommGroup.zmodModule (hX V.unop.1 (op V.unop.2))
  letI : ∀ V : (ℕ × T.ProEt)ᵒᵖ,
      Module ((rawRing l T).obj V) ((towerPresheaf X).obj V) := fun V ↦
    inferInstanceAs (Module (ULift.{u + 1} (ZMod (l ^ (V.unop.1 + 1)))) _)
  apply PresheafOfModules.ofPresheaf (towerPresheaf X)
  intro U V f a x
  obtain ⟨k, rfl⟩ := rawRing_natCast l T U a
  change ((towerPresheaf X).map f).hom ((k : (rawRing l T).obj U) • x) =
    ((rawRing l T).map f).hom (k : (rawRing l T).obj U) •
      ((towerPresheaf X).map f).hom x
  simp only [map_natCast]
  exact additive_natCast_smul ((towerPresheaf X).map f).hom k x

private def liftTower (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (X : Ab T)
    (hX : ∀ (n : ℕ) (U : T.ProEtᵒᵖ) (x : (X.obj (op n)).obj.obj U),
      l ^ (n + 1) • x = 0) : Systems T (Rrings l T) :=
  PresheafOfModules.sheafify (ringUnit l T) (M₀ := rawModule l X hX)
    (A := towerSheaf X) (eqToHom (by rfl))

private def liftTowerIso (l : ℕ) [Fact l.Prime] {T : Scheme.{u}} (X : Ab T)
    (hX : ∀ (n : ℕ) (U : T.ProEtᵒᵖ) (x : (X.obj (op n)).obj.obj U),
      l ^ (n + 1) • x = 0) : moduleTower (liftTower l X hX) ≅ X :=
  NatIso.ofComponents (fun n ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ Iso.refl _) (by
      intro U V f
      change ((X.map (𝟙 n)).hom.app U ≫ (X.obj n).obj.map f) ≫ 𝟙 _ =
        𝟙 _ ≫ (X.obj n).obj.map f
      rw [CategoryTheory.Functor.map_id]
      simp)))
    (by
      intro n m f
      ext U x
      change ((X.obj m).obj.map (𝟙 U)) (((X.map f).hom.app U) x) =
        ((X.map f).hom.app U) x
      simp only [CategoryTheory.Functor.map_id, CategoryTheory.id_apply])

private def uncurryModuleIso {l : ℕ} [Fact l.Prime] {T : Scheme.{u}}
    (M : Systems T (Rrings l T)) :
    towerPresheaf (moduleTower M) ≅ M.val.presheaf :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro U V f
    change (M.val.presheaf.map (Prod.mkHom f.unop.1 (𝟙 U.unop.2)).op ≫
      M.val.presheaf.map (Prod.mkHom (𝟙 V.unop.1) f.unop.2).op) ≫ 𝟙 _ =
        𝟙 _ ≫ M.val.presheaf.map f
    rw [Category.comp_id, Category.id_comp, ← Functor.map_comp, ← op_comp]
    congr 1)

private theorem moduleTower_full {l : ℕ} [Fact l.Prime] {T : Scheme.{u}}
    {M N : Systems T (Rrings l T)} (f : moduleTower M ⟶ moduleTower N) :
    ∃ g : M ⟶ N, moduleTowerMap g = f := by
  let φ : M.val.presheaf ⟶ N.val.presheaf := (uncurryModuleIso M).inv ≫
    Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := T.ProEt)).functor
      (Functor.uncurry.map (Functor.whiskerRight f (sheafToPresheaf _ _))) ≫
        (uncurryModuleIso N).hom
  let α := ringUnit l T
  let g : (PresheafOfModules.restrictScalars α).obj M.val ⟶
      (PresheafOfModules.restrictScalars α).obj N.val :=
    PresheafOfModules.homMk φ (by
      intro U a x
      obtain ⟨k, rfl⟩ := rawRing_natCast l T U a
      change φ.app U ((α.app U).hom (k : (rawRing l T).obj U) •
        (show M.val.obj U from x)) =
          (α.app U).hom (k : (rawRing l T).obj U) •
            (show N.val.obj U from φ.app U x)
      simp only [map_natCast]
      exact additive_natCast_smul (φ.app U).hom k x)
  let g' := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    α N.isSheaf).symm g
  refine ⟨⟨g'⟩, ?_⟩
  have hg := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    α N.isSheaf).apply_symm_apply g
  ext n U x
  exact congrArg (fun k ↦ k.app (op (n.unop, U.unop)) x) hg

private theorem forget_full (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (F : Forget T (Rrings l T)) : F.F.Full where
  map_surjective {M N} f := by
    let φ := (forgetIso F M).inv ≫ f ≫ (forgetIso F N).hom
    obtain ⟨g, hg⟩ := moduleTower_full φ
    refine ⟨g, ?_⟩
    apply (cancel_mono (forgetIso F N).hom).mp
    rw [forgetIso_map, hg]
    simp only [φ, Iso.hom_inv_id_assoc]

private theorem forget_faithful (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (F : Forget T (Rrings l T)) : F.F.Faithful where
  map_injective {M N} f g h := by
    have hh : moduleTowerMap f = moduleTowerMap g := by
      apply (cancel_epi (forgetIso F M).hom).mp
      rw [← forgetIso_map, ← forgetIso_map, h]
    ext U x
    exact congrArg (fun k ↦ ((k.app (op U.unop.1)).hom.app (op U.unop.2)) x) hh

private theorem cokernel_torsion (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) (X : Ab T)
    (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : ((cokernel ((PowerTransition.multiplication l).app X)).obj (op n)).obj.obj U) :
    l ^ (n + 1) • x = 0 := by
  let μ := (PowerTransition.multiplication l).app X
  let π := (cokernel.π μ).app (op n)
  have hepi : Epi π := inferInstance
  have hz : (l ^ (n + 1) • 𝟙 _) ≫ π = 0 := by
    have h := congrArg (fun f ↦ f.app (op n)) (cokernel.condition μ)
    change ((l ^ (n + 1) • 𝟙 (X.obj (op n))) ≫ π) = 0
    change ((PowerTransition.multiplication l).app X ≫ cokernel.π μ).app (op n) = 0 at h
    exact h
  have hq : l ^ (n + 1) • 𝟙 ((cokernel μ).obj (op n)) = 0 := by
    apply (cancel_epi π).mp
    simpa only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
      Category.comp_id, comp_zero] using hz
  have hh := congrArg (fun f ↦ (f.hom.app U) x) hq
  exact hh

private def unitCokernel (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Reduction T (Rrings l T)) (X : Ab T) :
    IsColimit (CokernelCofork.ofπ (r.model.adjunction.unit.app X) (unit_zero l T r X)) := by
  let μ := (PowerTransition.multiplication l).app X
  let a := r.model.adjunction
  let F := r.forget.F
  letI := forget_full l T r.forget
  letI := forget_faithful l T r.forget
  let Q := liftTower l (cokernel μ) (cokernel_torsion l T X)
  let eQ : cokernel μ ≅ F.obj Q :=
    (liftTowerIso l (cokernel μ) (cokernel_torsion l T X)).symm ≪≫
      (forgetIso r.forget Q).symm
  let b := (a.homEquiv X Q).symm (cokernel.π μ ≫ eQ.hom)
  have hb : a.unit.app X ≫ F.map b = cokernel.π μ ≫ eQ.hom :=
    (Adjunction.homEquiv_unit a _ _ b).symm.trans (Equiv.apply_symm_apply _ _)
  let k := cokernel.desc μ (a.unit.app X) (unit_zero l T r X)
  let c := F.preimage (eQ.inv ≫ k)
  have hc : F.map c = eQ.inv ≫ k := Functor.map_preimage _ _
  have hbc : b ≫ c = 𝟙 _ := by
    apply (a.homEquiv X (r.ordinary.obj X)).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    simp only [Functor.map_comp, CategoryTheory.Functor.map_id]
    rw [← Category.assoc, hb, hc]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    erw [Category.comp_id]
    exact cokernel.π_desc μ (a.unit.app X) (unit_zero l T r X)
  have hcb : c ≫ b = 𝟙 _ := by
    apply F.map_injective
    apply (cancel_epi (cokernel.π μ ≫ eQ.hom)).mp
    simp only [Functor.map_comp, Category.assoc, CategoryTheory.Functor.map_id, Category.comp_id]
    rw [hc]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, cokernel.π_desc]
    exact hb
  let eb : r.ordinary.obj X ≅ Q := ⟨b, c, hbc, hcb⟩
  let e := eQ ≪≫ (F.mapIso eb).symm
  have he : cokernel.π μ ≫ e.hom = a.unit.app X := by
    change cokernel.π μ ≫ eQ.hom ≫ F.map c = _
    rw [← Category.assoc, ← hb, Category.assoc, ← Functor.map_comp, hbc,
      CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  exact IsColimit.ofIsoColimit (cokernelIsCokernel μ) (Cofork.ext e he)

/-- The ordinary coefficient unit is the cokernel of the variable-power map.

Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
coefficient-resolution calculation; Stacks 03D7, ordinary extension of scalars.
(blueprint: lem-sfb-power-system-ordinary-cokernel).

Proof: at level n the coefficient ring is the constant sheaf Z/l^(n+1).
Its sections kill l^(n+1), so the ordinary unit kills the indicated power map.
The sheaf cokernel of that map has a unique Z/l^(n+1)-module structure: an
integer acts by its multiple, and this factors through the residue ring because
l^(n+1) acts by zero. Extend this action from constant sections to the constant
ring sheaf by its sheafification universal property. Restrictions are linear,
and the original transitions are semilinear for the quotient transitions of the
rings, since they commute with all integer multiples. Thus this cokernel is an
object of the ringed sequence-site module category. Additive maps out of it are
exactly module-system maps, as can be checked locally on constant integer
sections of the coefficient ring. Its quotient universal property therefore
identifies it with the ordinary left adjoint applied to X; the comparison takes
the quotient projection to the actual ordinary adjunction unit. Consequently
that unit, with its specified source X, is a cokernel of the power map. -/
theorem powerSystem_ordinary_cokernel (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Reduction T (Rrings l T)) (X : Ab T) :
    ∃ hz : (PowerTransition.multiplication l).app X ≫
        r.model.adjunction.unit.app X = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (r.model.adjunction.unit.app X) hz)) := by
  exact ⟨unit_zero l T r X, ⟨unitCokernel l T r X⟩⟩

end AlgebraicGeometry.ProEtale.SpTowerClasses
