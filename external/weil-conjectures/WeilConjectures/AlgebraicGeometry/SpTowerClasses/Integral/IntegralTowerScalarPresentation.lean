/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSystems
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.AlgebraicGeometry.ResidueQuotientDerivedUnit
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Data.ZMod.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
import all WeilConjectures.Algebra.Homology.DivisibleReduction.DivisibleExtensionDerivedReductionSupplement
import all WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import all WeilConjectures.SixFunctors.BaseChange.DerivedForget
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import all Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.Constant.ConstantSequenceModuleEquivalenceOfUniverses
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence

/-! # The ordinary integral presentation of a ringed tower topos -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

private abbrev integralBaseRing (T : Scheme.{u}) :=
  (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1} ℤ))

private abbrev integralTowerRing (T : Scheme.{u}) :=
  SheafOfModules.systemSequenceRing.{u + 1, u, u + 1} ((Functor.const ℕᵒᵖ).obj (integralBaseRing T))

private abbrev integralTowerForget (T : Scheme.{u}) :=
  (ConstantCompletion.independentConstantSequenceEquivalence.{u + 1, u, u + 1}
    (integralBaseRing T)).functor ⋙
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj
        (SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (integralBaseRing T)))

private theorem integralTowerForget_equivalence (T : Scheme.{u}) :
    (integralTowerForget T).IsEquivalence := by
  have : (SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (integralBaseRing T))).IsEquivalence :=
    CategoryTheory.Sheaf.ConstantResidue.integerForget_isEquivalence
      (Scheme.ProEt.topology T)
  unfold integralTowerForget
  infer_instance

private theorem integralTowerForget_additive (T : Scheme.{u}) :
    (integralTowerForget T).Additive := by
  have := (ConstantCompletion.independentConstantSequenceEquivalence_additive.{u + 1, u, u + 1}
    (integralBaseRing T)).1
  unfold integralTowerForget
  infer_instance

private def integralBaseScalar (T : Scheme.{u})
    (A : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) : integralBaseRing T ⟶ A :=
  ((sheafificationAdjunction (Scheme.ProEt.topology T) CommRingCat.{u + 1}).homEquiv _ _).symm
    { app U := CommRingCat.ofHom
        ((Int.castRingHom _).comp (ULift.ringEquiv (R := ℤ)).toRingHom)
      naturality U V f := by
        ext k
        exact (map_intCast (A.obj.map f).hom k.down).symm }

private theorem integralBaseScalar_unique (T : Scheme.{u})
    (A : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (f : integralBaseRing T ⟶ A) : f = integralBaseScalar T A := by
  let h := (sheafificationAdjunction (Scheme.ProEt.topology T)
    CommRingCat.{u + 1}).homEquiv
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} ℤ))) A
  apply h.injective
  ext U k
  exact (map_intCast ((h f).app U).hom k.down).trans
    (map_intCast ((h (integralBaseScalar T A)).app U).hom k.down).symm

private def integralScalarTower (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :
    (Functor.const ℕᵒᵖ).obj (integralBaseRing T) ⟶
      SemilinearSections.rings.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ B.obj (op n)) (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op) where
  app n := integralBaseScalar T _
  naturality n m f := by
    change 𝟙 (integralBaseRing T) ≫ integralBaseScalar T _ = _
    rw [Category.id_comp]
    exact (integralBaseScalar_unique T _ (integralBaseScalar T _ ≫
        (SemilinearSections.rings.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
          (fun n ↦ B.obj (op n))
          (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op)).map f)).symm

private def integralTowerScalar (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :
    integralTowerRing T ⟶
      SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        (fun n ↦ B.obj (op n)) (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op) :=
  ObjectProperty.homMk
    (Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := T.ProEt)).functor
      (Functor.uncurry.map (Functor.whiskerRight (integralScalarTower T B)
        (sheafToPresheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}))))

private theorem integralForgetGroups_preservesSheafification (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).PreservesSheafification
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) := by
  constructor
  intro P Q f hf
  change (Scheme.ProEt.topology T).W (Functor.whiskerRight f _)
  rw [(Scheme.ProEt.topology T).W_iff_isLocallyBijective] at hf ⊢
  let := hf.1
  let := hf.2
  exact ⟨⟨fun x y h ↦ Presheaf.equalizerSieve_mem (Scheme.ProEt.topology T) f x y h⟩,
    ⟨fun x ↦ Presheaf.imageSieve_mem (Scheme.ProEt.topology T) f x⟩⟩

private def integralTowerUnitIso (T : Scheme.{u}) :
    (integralTowerForget T).obj
      (SheafOfModules.unit ((sheafCompose
        (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (integralTowerRing T))) ≅ integers T := by
  let := integralForgetGroups_preservesSheafification T
  let c := (constantCommuteCompose (Scheme.ProEt.topology T)
    ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}))).app
        (CommRingCat.of (ULift.{u + 1} ℤ))
  exact NatIso.ofComponents (fun _ ↦ c) (by
    intro n m f
    ext U x
    change c.hom.hom.app U ((integralBaseRing T).obj.map (𝟙 U) x) = c.hom.hom.app U x
    have h (y : (integralBaseRing T).obj.obj U) :
        c.hom.hom.app U ((integralBaseRing T).obj.map (𝟙 U) y) =
          c.hom.hom.app U y := by
      exact congrArg (fun (g : (integralBaseRing T).obj.obj U ⟶
        (integralBaseRing T).obj.obj U) ↦ c.hom.hom.app U (g y))
          ((integralBaseRing T).obj.map_id U)
    exact h x)

private theorem integralBaseScalar_generator (T : Scheme.{u})
    (A : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (U : T.ProEtᵒᵖ) (k : ULift.{u + 1} ℤ) :
    (integralBaseScalar T A).hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} ℤ)))).app U k) =
      (k.down : A.obj.obj U) := by
  change (((sheafificationAdjunction (Scheme.ProEt.topology T)
    CommRingCat.{u + 1}).homEquiv _ _) (integralBaseScalar T A)).app U k = _
  dsimp only [integralBaseScalar]
  rw [Equiv.apply_symm_apply]
  rfl

private theorem integralTowerUnitIso_generator (T : Scheme.{u}) (n : ℕ)
    (U : T.ProEtᵒᵖ) (k : ULift.{u + 1} ℤ) :
    (((integralTowerUnitIso T).inv.app (op n)).hom.app U)
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U k) =
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} ℤ)))).app U k) := by
  let := integralForgetGroups_preservesSheafification T
  let J := Scheme.ProEt.topology T
  let P := (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} ℤ))
  let V := (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  let c := (constantCommuteCompose J V).app (CommRingCat.of (ULift.{u + 1} ℤ))
  have hn : Functor.whiskerRight (toSheafify J P) V ≫ c.hom.hom =
      (Functor.constComp T.ProEtᵒᵖ (CommRingCat.of (ULift.{u + 1} ℤ)) V).hom ≫
        toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := by
    change Functor.whiskerRight (toSheafify J P) V ≫
      ((constantCommuteCompose J V).hom.app (CommRingCat.of (ULift.{u + 1} ℤ))).hom = _
    rw [constantCommuteCompose_hom_app_hom, ← Category.assoc,
      sheafComposeIso_inv_fac]
    exact (toSheafify_naturality J
      (Functor.constComp T.ProEtᵒᵖ (CommRingCat.of (ULift.{u + 1} ℤ)) V).hom).symm
  have hx : c.hom.hom.app U ((toSheafify J P).app U k) =
      (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U k :=
    congrArg (fun (f : P ⋙ V ⟶ sheafify J
      ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ↦
        (f.app U).hom k) hn
  change c.inv.hom.app U _ = _
  rw [← hx]
  change ((c.hom ≫ c.inv).hom.app U) ((toSheafify J P).app U k) = _
  rw [c.hom_inv_id]
  rfl

private theorem equiv_tensor_unit_transpose
    {A C D : Type*} [Category A] [Category C] [Category D]
    (e : A ≌ C) {E : C ⥤ D} {V : D ⥤ C} (a : E ⊣ V)
    {X : A} {U : C} {Y : D} (c : e.inverse.obj U ≅ X) (v : E.obj U ≅ Y) :
    let z := e.functor.mapIso c.symm ≪≫ e.counitIso.app U
    (e.toAdjunction.comp a).homEquiv _ _ (E.map z.hom ≫ v.hom) =
      c.inv ≫ e.inverse.map (a.homEquiv _ _ v.hom) := by
  intro z
  rw [Adjunction.comp_homEquiv]
  change e.toAdjunction.homEquiv X _
    (a.homEquiv _ _ (E.map z.hom ≫ v.hom)) = _
  rw [a.homEquiv_naturality_left, Adjunction.homEquiv_unit]
  change e.unit.app X ≫ e.inverse.map (z.hom ≫ _) = _
  dsimp only [z, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [e.unit_naturality_assoc c.inv, e.unit_inverse_comp_assoc]
  rfl

/-- The ordinary tensor/restriction adjunction for abelian towers, including its free unit.

Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
and IntegralUnitReduction proof steps 1 and 3.
(blueprint: lem-sfb-integral-tower-scalar-presentation).

Proof: let O be the constant lifted-integer ring sheaf on the base site, and take R
to be its constant sequence ring on the vertical sequence site.
Flattening a tower of abelian sheaves identifies it with an abelian sheaf on this site:
the sheaf condition is precisely the sheaf condition at each fixed index. Give every
section its unique integer action and extend it to R by the universal property of
constant sheafification. This gives the additive equivalence e; its inverse forgets
that action and takes the levels. The flattened constant integer tower is the free
rank-one R-module, giving the displayed source isomorphism. The unique unital integer
map into each B-section sheafifies to phi. Restriction along phi, followed by levels,
is the functor F: its section groups, vertical maps, horizontal maps and morphisms
are the four formulas in Forget, and it is exact since underlying abelian sheaves
compute kernels and sheafified cokernels. Sheafified balanced tensor with B is left
adjoint to this restriction. For any functor E with the stated objects and maps,
transport this adjunction by the component equality isomorphisms. Multiplication
B tensor_R R to B identifies E(e(Z)) with the coefficient module. Its adjoint sends
a constant integer k to k times one on every section, so uniqueness in
integerGenerator_existsUnique gives the last equality. No nonzero-ring, nonempty-site,
prime, or coefficient-flatness assumption is used. This statement concerns ordinary
categories only; it supplies no derived functor or derived adjunction. -/
theorem exists_integralTowerScalarPresentation (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) :
    let J := coefficientSequenceTopology (Scheme.ProEt.topology T)
    let S := SemilinearSections.systemRing.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (fun n ↦ B.obj (op n))
      (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op)
    ∃ (R : Sheaf J CommRingCat.{u + 1}) (φ : R ⟶ S)
      (e : Ab T ≌ ringedSiteModules.{u + 1}
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)),
      e.functor.Additive ∧
      Nonempty (e.functor.obj (integers T) ≅
        SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ∧
      ∃ F : Forget T B,
        ∀ (E : ringedSiteModules.{u + 1}
            ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⥤ Systems T B)
          [E.Additive]
          (hobj : ∀ M, E.obj M = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M)
          (_hmap : ∀ {M N} (f : M ⟶ N), E.map f =
            eqToHom (hobj M) ≫ SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} φ M f ≫
              eqToHom (hobj N).symm),
          ∃ adj : e.functor ⋙ E ⊣ F.F,
            ∃ b : E.obj (e.functor.obj (integers T)) ≅ coefficient T B,
              adj.homEquiv _ _ b.hom = integerGenerator T B F := by
  classical
  let J := coefficientSequenceTopology (Scheme.ProEt.topology T)
  let S := SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (fun n ↦ B.obj (op n)) (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op)
  let R := integralTowerRing T
  let φ : R ⟶ S := integralTowerScalar T B
  let G := integralTowerForget T
  let : G.IsEquivalence := integralTowerForget_equivalence T
  let : G.Additive := integralTowerForget_additive T
  let : G.asEquivalence.functor.Additive := by
    change G.Additive
    infer_instance
  let e := G.asEquivalence.symm
  let : e.functor.Additive := G.asEquivalence.inverse_additive
  let V := SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ)
  obtain ⟨hlim, hcol, hadj⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction φ
  let := hlim
  let := hcol
  let F : Forget T B :=
    { F := V ⋙ G
      sections := by intros; rfl
      restrictions := by intros; rfl
      transitions := by intros; rfl
      morphisms := by intros; rfl
      additive := by infer_instance
      limits := by infer_instance
      colimits := by infer_instance }
  let U := SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let c : G.obj U ≅ integers T := integralTowerUnitIso T
  let z : e.functor.obj (integers T) ≅ U :=
    e.functor.mapIso c.symm ≪≫ e.counitIso.app U
  refine ⟨R, φ, e, inferInstance, ⟨z⟩, F, ?_⟩
  intro E hadd hobj hmap
  obtain ⟨a, ha⟩ := hadj E hobj hmap
  let adj : e.functor ⋙ E ⊣ F.F := e.toAdjunction.comp a
  obtain ⟨d⟩ := SheafOfModules.scalarExtension_constraint_coherence R S φ
  let v : E.obj U ≅ coefficient T B := eqToIso (hobj U) ≪≫ d.unitIso
  let b : E.obj (e.functor.obj (integers T)) ≅ coefficient T B := E.mapIso z ≪≫ v
  refine ⟨adj, b, ?_⟩
  have ht : adj.homEquiv _ _ b.hom =
      c.inv ≫ G.map (a.homEquiv _ _ v.hom) :=
    equiv_tensor_unit_transpose e a c v
  rw [ht]
  apply (integerGenerator_existsUnique T B F).unique ?_
    (integerGenerator_existsUnique T B F).exists.choose_spec
  intro n W k
  change HEq
    ((a.homEquiv U (coefficient T B) v.hom).val.app (op (n, W.unop))
      ((((integralTowerUnitIso T).inv.app (op n)).hom.app W)
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app W k)))
    (k.down : (B.obj (op n)).obj.obj W)
  rw [integralTowerUnitIso_generator]
  change HEq
    ((a.homEquiv U (coefficient T B) (eqToHom (hobj U) ≫ d.unitIso.hom)).val.app
      (op (n, W.unop))
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1} ℤ)))).app W k)) _
  rw [ha]
  apply heq_of_eq
  have hu := d.unit_hom (op (n, W.unop)) (1 : S.obj.obj (op (n, W.unop)))
    ((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} ℤ)))).app W k)
  change d.unitIso.hom.val.app (op (n, W.unop))
      (SheafOfModules.scalarExtensionConstraintTmul φ U (op (n, W.unop)) _ 1) = _
  exact hu.trans (by
    rw [one_mul]
    exact integralBaseScalar_generator T _ W k)

end AlgebraicGeometry.ProEtale.SpTowerClasses
