/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.AlgebraicGeometry.Affine.AffineRootsRepresentability
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Limits.AffineOverLimitProperties
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Sites.PreservesLimits
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransport

/-! # Preservation of the cyclotomic inverse limit

## References

* Stacks Project, Tags 09A5 and 03CF
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local instance] IsCofiltered.isConnected

/-- Inverse image preserves the particular root tower defining Z_ell(1).
It need not preserve arbitrary inverse limits. -/
private theorem globalPrimeUnit (Y : Scheme.{u}) (l : ℕ)
    [∀ y : Y, Invertible (l : Y.residueField y)] : IsUnit (l : Γ(Y, ⊤)) := by
  apply Y.toRingedSpace.isUnit_of_isUnit_germ
  intro y hy
  rw [map_natCast]
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  change (Y.residue y).hom (l : Y.presheaf.stalk y) ≠ 0
  simpa only [map_natCast] using (isUnit_of_invertible (l : Y.residueField y)).ne_zero

private theorem roots_representation (Y : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hunit : IsUnit (N : Γ(Y, ⊤))) :
    ∃ V : Y.ProEt, IsFinite V.hom ∧ Etale V.hom ∧
      Nonempty ((Scheme.ProEt.topology Y).uliftYoneda.{u + 1}.obj V ≅
        (sheafCompose (Scheme.ProEt.topology Y) (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          (proEtaleRootsOfUnitySheaf Y N)) := by
  classical
  let R := Γ(Y, ⊤)
  let P := affineRootsOver R N
  have hmonic : ((Polynomial.X : Polynomial R) ^ N - 1).Monic := by
    simpa using Polynomial.monic_X_pow_sub_C (1 : R) hN.ne'
  have : IsFinite P.hom := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R _)))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr hmonic.finite_adjoinRoot
  have : Etale P.hom := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap R _)))
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    apply RingHom.etale_algebraMap.mpr
    simpa only [Polynomial.C_1] using
      AdjoinRoot.etale_X_pow_sub_C hN.ne' hunit (isUnit_one : IsUnit (1 : R))
  let W := (Over.pullback Y.toSpecΓ).obj P
  let : IsFinite W.hom := inferInstanceAs (IsFinite (pullback.snd P.hom Y.toSpecΓ))
  let : Etale W.hom := inferInstanceAs (Etale (pullback.snd P.hom Y.toSpecΓ))
  let V : Y.ProEt := Scheme.ProEt.mk W.hom
  obtain ⟨_, _, _, _, _, _, _, hbase⟩ := affineRoots_representability R N hN
  obtain ⟨e, _, hnat, _⟩ := hbase Y Y.toSpecΓ
  let a (U : Y.ProEtᵒᵖ) :
      (U.unop ⟶ V) ≃ ((Scheme.ProEt.forget Y).obj U.unop ⟶ W) :=
    { toFun := fun f ↦ Over.homMk f.left f.w
      invFun := fun f ↦ MorphismProperty.Over.homMk f.left f.w
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let b (U : Y.ProEtᵒᵖ) :
      {z : Γ(U.unop.left, ⊤)ˣ // z ^ N = 1} ≃
        Additive (rootsOfUnity N Γ(U.unop.left, ⊤)) :=
    { toFun := fun z ↦ Additive.ofMul ⟨z.val, (mem_rootsOfUnity N _).mpr z.property⟩
      invFun := fun z ↦ ⟨z.toMul.val, (mem_rootsOfUnity N _).mp z.toMul.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let k (U : Y.ProEtᵒᵖ) :
      ULift.{u + 1} (U.unop ⟶ V) ≃
        (proEtaleRootsOfUnitySheaf Y N).obj.obj U :=
    Equiv.ulift.trans ((a U).trans ((e _).trans
      ((b U).trans (proEtaleRootsOfUnitySections Y N U).toEquiv.symm)))
  let j : ((Scheme.ProEt.topology Y).uliftYoneda.{u + 1}.obj V).obj ≅
      ((sheafCompose (Scheme.ProEt.topology Y) (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
        (proEtaleRootsOfUnitySheaf Y N)).obj :=
    NatIso.ofComponents (fun U ↦ (k U).toIso) (by
      intro U U' f
      ext x
      apply (proEtaleRootsOfUnitySections Y N U').injective
      apply Additive.toMul.injective
      apply Subtype.ext
      have hi := NatTrans.naturality_apply
        (proEtaleRootsOfUnityInclusion Y N).hom f (k U x)
      have hu := (existsUnique_proEtaleRootsOfUnitySections Y N U).exists.choose_spec
        (k U x)
      have hv := (existsUnique_proEtaleRootsOfUnitySections Y N U').exists.choose_spec
        ((proEtaleRootsOfUnitySheaf Y N).obj.map f (k U x))
      have hk (T : Y.ProEtᵒᵖ) (z : ULift.{u + 1} (T.unop ⟶ V)) :
          (proEtaleRootsOfUnitySections Y N T (k T z)).toMul.val =
            (e _ (a T z.down)).val := by
        dsimp [k, b]
        exact congrArg (fun z ↦ z.toMul.val)
          ((proEtaleRootsOfUnitySections Y N T).apply_symm_apply _)
      have hr : (proEtaleRootsOfUnitySections Y N U'
          ((proEtaleRootsOfUnitySheaf Y N).obj.map f (k U x))).toMul.val =
          Units.map f.unop.left.appTop.hom.toMonoidHom
            (proEtaleRootsOfUnitySections Y N U (k U x)).toMul.val := by
        rw [← hu, ← hv] at hi
        exact congrArg (fun z ↦ z.down.toMul) hi
      change (proEtaleRootsOfUnitySections Y N U'
          (k U' ⟨f.unop ≫ x.down⟩)).toMul.val =
        (proEtaleRootsOfUnitySections Y N U'
          ((proEtaleRootsOfUnitySheaf Y N).obj.map f (k U x))).toMul.val
      exact (hk U' _).trans ((hnat _ _ ((Scheme.ProEt.forget Y).map f.unop)
        (a U x.down)).trans ((congrArg
          (Units.map f.unop.left.appTop.hom.toMonoidHom) (hk U x).symm).trans hr.symm)))
  exact ⟨V, ‹IsFinite W.hom›, ‹Etale W.hom›,
    ⟨(sheafToPresheaf _ _).preimageIso j⟩⟩

private theorem lift_representable_diagram
    {C B I : Type*} [Category C] [Category B] [Category I]
    (F : C ⥤ B) [F.Full] [F.Faithful] (A : I ⥤ B)
    (V : I → C) (e : ∀ i, F.obj (V i) ≅ A.obj i) :
    ∃ D : I ⥤ C, (∀ i, D.obj i = V i) ∧ Nonempty (D ⋙ F ≅ A) := by
  let D : I ⥤ C :=
    { obj := V
      map {i j} g := F.preimage ((e i).hom ≫ A.map g ≫ (e j).inv)
      map_id i := by
        apply F.map_injective
        simp
      map_comp g h := by
        apply F.map_injective
        simp [Category.assoc] }
  refine ⟨D, fun _ ↦ rfl, ⟨NatIso.ofComponents e ?_⟩⟩
  intro i j g
  change F.map (F.preimage _) ≫ (e j).hom = _
  simp [Category.assoc]

private theorem finiteEtale_geometric_limit
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Y.ProEt)
    (hfin : ∀ i, IsFinite (D.obj i).hom) (het : ∀ i, Etale (D.obj i).hom) :
    HasLimit D ∧ PreservesLimit D (Scheme.proEtaleBaseChange f) := by
  let A := D ⋙ Scheme.ProEt.forget Y ⋙ Over.forget Y
  let p (i : I) : A.obj i ⟶ Y := (D.obj i).hom
  have hp {i j : I} (g : i ⟶ j) : A.map g ≫ p j = p i := (D.map g).w
  let (i : I) : IsFinite (p i) := hfin i
  let (i : I) : Etale (p i) := het i
  let (i : I) : IsAffineHom (p i) := inferInstance
  let cA := Scheme.AffineOverLimit.limitCone A p hp
  let hcA := Scheme.AffineOverLimit.isLimitLimitCone A p hp
  let q := Scheme.AffineOverLimit.limitHom A p hp
  have hq (i : I) : cA.π.app i ≫ p i = q := Scheme.AffineOverLimit.π_p A p hp i
  let : WeaklyEtale q := Scheme.weaklyEtale_of_isLimit A hcA p hp q hq
  let c : Cone D :=
    { pt := Scheme.ProEt.mk q
      π :=
        { app i := MorphismProperty.Over.homMk (cA.π.app i) (hq i)
          naturality i j g := by
            apply MorphismProperty.Over.Hom.ext
            change 𝟙 _ ≫ cA.π.app j = cA.π.app i ≫ A.map g
            exact (Category.id_comp _).trans (cA.w g).symm } }
  have hcOver : IsLimit ((Scheme.ProEt.forget Y).mapCone c) := by
    apply isLimitOfReflects (Over.forget Y)
    exact hcA
  have hc : IsLimit c := isLimitOfReflects (Scheme.ProEt.forget Y) hcOver
  have hfc : IsLimit ((Scheme.proEtaleBaseChange f).mapCone c) := by
    apply isLimitOfReflects (Scheme.ProEt.forget X)
    exact isLimitOfPreserves (Over.pullback f) hcOver
  exact ⟨⟨⟨⟨c, hc⟩⟩⟩, preservesLimit_of_preserves_limit_cone hc hfc⟩

private noncomputable def representableInverseImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleBaseChange f ⋙ (ProEt.topology X).uliftYoneda.{u + 1} ≅
      (ProEt.topology Y).uliftYoneda.{u + 1} ⋙
        proEtaleSheafInverseImage f (Type (u + 1)) := by
  let e := Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{u + 1}
    (proEtaleBaseChange f)
  exact Functor.isoWhiskerLeft
    (proEtaleBaseChange f ⋙ (ProEt.topology X).uliftYoneda.{u + 1})
    (sheafificationNatIso (ProEt.topology X) (Type (u + 1))) ≪≫
    Functor.isoWhiskerRight e (presheafToSheaf (ProEt.topology X) (Type (u + 1)))

private noncomputable def abelianForgetInverseImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    AlgebraicGeometry.ProEtale.upperStar AddCommGrpCat.{u + 1} f ⋙
      sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1}) ≅
    sheafCompose (ProEt.topology Y) (CategoryTheory.forget AddCommGrpCat.{u + 1}) ⋙
      proEtaleSheafInverseImage f (Type (u + 1)) := by
  let : RepresentablyFlat (proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  let : (CategoryTheory.forget AddCommGrpCat.{u + 1}).PreservesLeftKanExtensions
      (proEtaleBaseChange f).op := by
    intro P
    let : PreservesFilteredColimitsOfSize.{u, u + 1}
        (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
      preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    let : ∀ V, Functor.PreservesPointwiseLeftKanExtensionAt
        (CategoryTheory.forget AddCommGrpCat.{u + 1}) P (proEtaleBaseChange f).op V := by
      intro V
      infer_instance
    infer_instance
  exact sheafPullbackForgetIso (ProEt.topology Y) (ProEt.topology X)
    (proEtaleBaseChange f) (CategoryTheory.forget AddCommGrpCat.{u + 1})

theorem pur_root_tower_preservation
    {X Y : Scheme.{u}} (h : X ⟶ Y) (l : ℕ) [Fact l.Prime]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    PreservesLimit (proEtaleRootsOfUnityTower Y l (Fact.out : l.Prime))
      (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}) := by
  let T := proEtaleRootsOfUnityTower Y l (Fact.out : l.Prime)
  let Ry := sheafCompose (ProEt.topology Y) (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let Rx := sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let L := proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}
  let P := proEtaleSheafInverseImage h (Type (u + 1))
  classical
  choose W hfin het e using fun n : ℕᵒᵖ ↦
    roots_representation Y (l ^ (n.unop + 1)) (pow_pos (Fact.out : l.Prime).pos _)
      (by simpa only [Nat.cast_pow] using (globalPrimeUnit Y l).pow (n.unop + 1))
  obtain ⟨D, hD, ⟨eD⟩⟩ := lift_representable_diagram
    (ProEt.topology Y).uliftYoneda.{u + 1} (T ⋙ Ry)
    (fun n ↦ W n) (fun n ↦ (e n).some)
  have hfinD (n : ℕᵒᵖ) : IsFinite (D.obj n).hom := by rw [hD]; exact hfin n
  have hetD (n : ℕᵒᵖ) : Etale (D.obj n).hom := by rw [hD]; exact het n
  let liftIndex : ℕᵒᵖ ≌ AsSmall.{u} ℕᵒᵖ := AsSmall.equiv
  let : IsCofiltered (AsSmall.{u} ℕᵒᵖ) := IsCofiltered.of_equivalence liftIndex
  obtain ⟨hlim, hpres⟩ := finiteEtale_geometric_limit h
    (liftIndex.inverse ⋙ D) (fun i ↦ hfinD (ULift.down i))
      (fun i ↦ hetD (ULift.down i))
  let := hlim
  let := hpres
  let : HasLimit D := Functor.Initial.hasLimit_of_comp liftIndex.inverse
  let : PreservesLimit D (proEtaleBaseChange h) :=
    Functor.Initial.preservesLimit_of_comp liftIndex.inverse
  let Ly := (ProEt.topology Y).uliftYoneda.{u + 1}
  let Lx := (ProEt.topology X).uliftYoneda.{u + 1}
  let : PreservesLimit D (proEtaleBaseChange h ⋙ Lx) := inferInstance
  let : PreservesLimit D (Ly ⋙ P) :=
    preservesLimit_of_natIso D (representableInverseImageIso h)
  let : PreservesLimit (D ⋙ Ly) P := by
    exact preservesLimit_of_preserves_limit_cone
      (isLimitOfPreserves Ly (limit.isLimit D))
      (isLimitOfPreserves (Ly ⋙ P) (limit.isLimit D))
  let : PreservesLimit (T ⋙ Ry) P :=
    preservesLimit_of_iso_diagram P eD
  let : PreservesLimitsOfShape ℕᵒᵖ (Ry ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (ProEt.topology Y) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{u + 1})))
  let : PreservesLimitsOfShape ℕᵒᵖ Ry :=
    preservesLimitsOfShape_of_reflects_of_preserves Ry (sheafToPresheaf _ _)
  let : PreservesLimitsOfShape ℕᵒᵖ (Rx ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{u + 1})))
  let : PreservesLimitsOfShape ℕᵒᵖ Rx :=
    preservesLimitsOfShape_of_reflects_of_preserves Rx (sheafToPresheaf _ _)
  let : ReflectsLimitsOfShape ℕᵒᵖ Rx := reflectsLimitsOfShape_of_reflectsIsomorphisms
  let : PreservesLimit T (L ⋙ Rx) :=
    preservesLimit_of_natIso T (abelianForgetInverseImageIso h).symm
  let : PreservesLimit T L := preservesLimit_of_reflects_of_preserves L Rx
  exact preservesLimit_of_reflects_of_preserves L Rx

end AlgebraicGeometry.Scheme
