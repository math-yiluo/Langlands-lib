/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedComparisonData
import WeilConjectures.Algebra.Homology.KFlatResolution
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedAdjointLift
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedTensorLift
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedIdentityComparison
import WeilConjectures.Algebra.Homology.RingedTensorSquare.RingedExchangeTensorCoherence
import WeilConjectures.Algebra.Homology.Ringed.RingedSquareTensorCompatibility
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent

/-! # Normalized composition comparisons before the counit consequence

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0D6E, 07A6 and 0FPI.
(blueprint: lem-sfb-ringed-derived-composition-comparison).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits WeilConjectures SheafOfModules
namespace CategoryTheory.RingedDerivedComparisons

attribute [local irreducible] SheafOfModules.monoidalCategory

open CategoryTheory.MonoidalCategory in
private abbrev Site.ringSets (X : Site.{u, w}) :=
  (sheafCompose X.J (CategoryTheory.forget CommRingCat.{u})).obj X.A

open CategoryTheory.MonoidalCategory in
private abbrev transpose {X Y : Site.{u, w}} (f : Morphism X Y)
    (M : X.modules) {T : Sheaf Y.J (Type u)} (x : T ⟶ Y.sets.obj (f.modules.obj M)) :=
  (f.adj.homEquiv T (X.sets.obj M)).symm (x ≫ f.underlying.hom.app M)

open CategoryTheory.MonoidalCategory in
private theorem transpose_injective {X Y : Site.{u, w}} (f : Morphism X Y)
    (M : X.modules) (T : Sheaf Y.J (Type u)) :
    Function.Injective (transpose f M (T := T)) := by
  intro x y h
  apply (cancel_mono (f.underlying.hom.app M)).mp
  exact (f.adj.homEquiv T (X.sets.obj M)).symm.injective h

open CategoryTheory.MonoidalCategory in
private theorem homEquiv_conjugate
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R')
    (c : L ≅ L') (U : C) (E : D) (b : L.obj U ⟶ E) :
    a.homEquiv U E b ≫ (conjugateIsoEquiv a a' c.symm).hom.app E =
      a'.homEquiv U E (c.inv.app U ≫ b) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  let κ := conjugateIsoEquiv a a' c.symm
  change (a.unit.app U ≫ R.map b) ≫ κ.hom.app E = _
  rw [Category.assoc, κ.hom.naturality, ← Category.assoc]
  change (a.unit.app U ≫ (conjugateEquiv a a' c.inv).app (L.obj U)) ≫ _ = _
  rw [unit_conjugateEquiv, Category.assoc, ← R'.map_comp]

open CategoryTheory.MonoidalCategory in
private def liftLinear {X : Site.{u, w}} {M N : X.modules}
    (q : X.sets.obj M ⟶ X.sets.obj N)
    (ha : ∀ U (x y : M.val.obj U), q.hom.app U (x + y) =
      @Add.add (N.val.obj U) inferInstance (q.hom.app U x) (q.hom.app U y))
    (hs : ∀ U (r : X.A.obj.obj U) (x : M.val.obj U),
      q.hom.app U (r • x) = r • (show N.val.obj U from q.hom.app U x)) : M ⟶ N where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := q.hom.app U
          map_add' := ha U
          map_smul' := hs U }
      naturality := by
        intro U V i
        ext x
        exact CategoryTheory.congr_fun (q.hom.naturality i) x }

open CategoryTheory.MonoidalCategory in
private def normalizedAdj {X Y : Site.{u, w}} {f : Morphism X Y} (l : Lift f) :
    l.edge.pullback ⊣ f.modules :=
  l.edge.moduleAdjunction.ofNatIsoRight (eqToIso l.pushforward_eq)

open CategoryTheory.MonoidalCategory in
private theorem normalized_transpose {X Y : Site.{u, w}} {f : Morphism X Y}
    (l : Lift f) (M : Y.modules) (N : X.modules) (b : l.edge.pullback.obj M ⟶ N) :
    transpose f N (Y.sets.map ((normalizedAdj l).homEquiv M N b)) =
      l.insertion M ≫ X.sets.map b := by
  apply (f.adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  simpa only [normalizedAdj, Adjunction.homEquiv_ofNatIsoRight_apply,
    Functor.map_comp, eqToIso.hom, Functor.whiskerRight_app, Lift.insertion,
    Category.assoc] using l.ordinary_adjunction M N b

open CategoryTheory.MonoidalCategory in
private theorem transpose_precomp {X Y : Site.{u, w}} (f : Morphism X Y)
    (M : X.modules) {T T' : Sheaf Y.J (Type u)} (a : T' ⟶ T)
    (x : T ⟶ Y.sets.obj (f.modules.obj M)) :
    transpose f M (a ≫ x) = f.inverse.map a ≫ transpose f M x := by
  dsimp only [transpose]
  rw [Category.assoc, f.adj.homEquiv_naturality_left_symm]

open CategoryTheory.MonoidalCategory in
private theorem composite_transpose {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} (lf : Lift f) (lg : Lift g)
    (M : Z.modules) (N : X.modules) (b : lf.edge.pullback.obj (lg.edge.pullback.obj M) ⟶ N) :
    transpose f N (transpose g (f.modules.obj N)
      (Z.sets.map (((normalizedAdj lg).comp (normalizedAdj lf)).homEquiv M N b))) =
      f.inverse.map (lg.insertion M) ≫ lf.insertion (lg.edge.pullback.obj M) ≫ X.sets.map b := by
  rw [Adjunction.comp_homEquiv]
  change transpose f N (transpose g (f.modules.obj N)
    (Z.sets.map ((normalizedAdj lg).homEquiv M (f.modules.obj N)
      ((normalizedAdj lf).homEquiv (lg.edge.pullback.obj M) N b)))) = _
  rw [normalized_transpose, transpose_precomp, normalized_transpose]

open CategoryTheory.MonoidalCategory in
private theorem preserves_flat {X Y : Site.{u, w}} {f : Morphism X Y} (l : Lift f)
    (P : CochainComplex Y.modules ℤ) (hp : Y.corner.mateFlat P) :
    X.corner.mateFlat ((l.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P) := by
  have hf (n : ℤ) : IsFlatOnSite (J := Y.J) (R := Y.A) (P.X n) := by
    let := monoidalCategory Y.A
    exact ObjectProperty.prop_of_iso (exactFunctor _ _)
      (siteSheafTensorRightIso Y.A (P.X n)).symm (hp.2 n)
  obtain ⟨hk, ht⟩ := isKFlat_ringedToposPullback l.edge.inverse l.edge.direct l.edge.adjunction
    l.edge.algebraic l.edge.ringMap l.edge.pullback l.edge.object_eq l.edge.map_eq P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp.1) hf
  refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk, ?_⟩
  intro n
  let := monoidalCategory X.A
  exact ObjectProperty.prop_of_iso (exactFunctor _ _)
    (siteSheafTensorRightIso X.A _) (ht n)

open CategoryTheory.MonoidalCategory in
private theorem tensor_model (X : Site.{u, w}) :
    ∃ r : RingedTensorModel X.corner, ∀ P Q hP hQ,
      r.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
        (X.model.iso X.J X.A X.closed P Q hP.1 hQ.1).hom := by
  let ι : ObjectProperty.FullSubcategory X.corner.mateFlat ⥤
      ObjectProperty.FullSubcategory (CochainComplex.IsKFlatIndependentCoefficients.{u, u, u}
        (J := X.J) (R := X.A)) := {
    obj := fun P ↦ ⟨P.obj,
      (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).2 P.property.1⟩
    map := fun a ↦ ObjectProperty.homMk a.hom }
  let r : RingedTensorModel X.corner := {
    representative := Functor.isoWhiskerLeft (ι.prod ι) X.model.comparison }
  exact ⟨r, fun _ _ _ _ ↦ rfl⟩

open CategoryTheory.MonoidalCategory in
private theorem conjugate_transpose
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R')
    (c : L ≅ L') (U : C) (E : D) (b : U ⟶ R.obj E) :
    (a'.homEquiv U E).symm
        (b ≫ (conjugateIsoEquiv a a' c.symm).hom.app E) =
      c.inv.app U ≫ (a.homEquiv U E).symm b := by
  apply (a'.homEquiv U E).injective
  rw [Equiv.apply_symm_apply, ← homEquiv_conjugate, Equiv.apply_symm_apply]

open CategoryTheory.MonoidalCategory in
private theorem complex_conjugate {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    (lf : Lift f) (lg : Lift g) (lk : Lift k)
    (e : lk.edge.pullback ≅ lg.edge.pullback ⋙ lf.edge.pullback)
    (P : CochainComplex Z.modules ℤ) (I : CochainComplex X.modules ℤ)
    (b : P ⟶ (lk.edge.pushforward.mapHomologicalComplex (.up ℤ)).obj I) :
    ((lf.edge.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv
      ((lg.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P) I).symm
      (((lg.edge.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P
        ((lf.edge.pushforward.mapHomologicalComplex (.up ℤ)).obj I)).symm
        (b ≫ (NatTrans.mapHomologicalComplex
          (conjugateIsoEquiv lk.edge.moduleAdjunction
            (lg.edge.moduleAdjunction.comp lf.edge.moduleAdjunction) e.symm).hom
          (.up ℤ)).app I)) =
      (NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app P ≫
        ((lk.edge.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I).symm b := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [Adjunction.homEquiv_counit, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f]
  change _ = e.inv.app (P.X n) ≫ _
  have hh := conjugate_transpose lk.edge.moduleAdjunction
    (lg.edge.moduleAdjunction.comp lf.edge.moduleAdjunction) e (P.X n) (I.X n) (b.f n)
  rw [Adjunction.comp_homEquiv] at hh
  change (lf.edge.moduleAdjunction.homEquiv (lg.edge.pullback.obj (P.X n)) (I.X n)).symm
    ((lg.edge.moduleAdjunction.homEquiv (P.X n)
      (lf.edge.pushforward.obj (I.X n))).symm
      (b.f n ≫ (conjugateIsoEquiv lk.edge.moduleAdjunction
        (lg.edge.moduleAdjunction.comp lf.edge.moduleAdjunction) e.symm).hom.app (I.X n))) =
    _ at hh
  simp only [Adjunction.homEquiv_counit] at hh
  exact hh

open CategoryTheory.MonoidalCategory in
private theorem square_tensor {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    {i : Morphism X X} (lf : Lift f) (lg : Lift g) (lk : Lift k) (li : Lift i)
    (s : RingedTensorSquare Z.corner Y.corner X.corner X.corner
      lg.edge lk.edge lf.edge li.edge) :
    ∀ U V : Z.D,
      s.derivedComparison.hom.app (Z.closed.tensor.obj (U, V)) ≫
        lf.edge.left.map (lg.tensor U V).hom ≫
        (lf.tensor (lg.edge.left.obj U) (lg.edge.left.obj V)).hom =
      li.edge.left.map (lk.tensor U V).hom ≫
        (li.tensor (lk.edge.left.obj U) (lk.edge.left.obj V)).hom ≫
        X.closed.tensor.map
          (X := (li.edge.left.obj (lk.edge.left.obj U), li.edge.left.obj (lk.edge.left.obj V)))
          (Y := (lf.edge.left.obj (lg.edge.left.obj U), lf.edge.left.obj (lg.edge.left.obj V)))
          (s.derivedComparison.hom.app U, s.derivedComparison.hom.app V) := by
  have model_unique {A : Site.{u, w}} {r r' : RingedTensorModel A.corner}
      (h : ∀ P Q hP hQ, r.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
        r'.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)) : r = r' := by
    cases r with | mk r =>
    cases r' with | mk r' =>
    congr 1
    apply Iso.ext
    apply NatTrans.ext
    funext B
    exact h B.1.obj B.2.obj B.1.property B.2.property
  have hZY : lg.tensorModelY = lk.tensorModelY := model_unique
    (fun P Q hP hQ ↦ (lg.tensorModelY_eq P Q hP hQ).trans
      (lk.tensorModelY_eq P Q hP hQ).symm)
  have hYY : lg.tensorModelX = lf.tensorModelY := model_unique
    (fun P Q hP hQ ↦ (lg.tensorModelX_eq P Q hP hQ).trans
      (lf.tensorModelY_eq P Q hP hQ).symm)
  have hXX : lk.tensorModelX = li.tensorModelY := model_unique
    (fun P Q hP hQ ↦ (lk.tensorModelX_eq P Q hP hQ).trans
      (li.tensorModelY_eq P Q hP hQ).symm)
  have hXI : lf.tensorModelX = li.tensorModelX := model_unique
    (fun P Q hP hQ ↦ (lf.tensorModelX_eq P Q hP hQ).trans
      (li.tensorModelX_eq P Q hP hQ).symm)
  let l : Z.closed.tensor ⋙ lk.edge.left ⋙ li.edge.left ⟶
      ((lg.edge.left ⋙ lf.edge.left).prod (lg.edge.left ⋙ lf.edge.left)) ⋙ X.closed.tensor :=
    Functor.whiskerLeft Z.closed.tensor s.derivedComparison.hom ≫
      Functor.whiskerRight (lg.edge.tensorComparison lg.tensorModelY lg.tensorModelX).hom
        lf.edge.left ≫
      Functor.whiskerLeft (lg.edge.left.prod lg.edge.left)
        (lf.edge.tensorComparison lg.tensorModelX lf.tensorModelX).hom
  let r : Z.closed.tensor ⋙ lk.edge.left ⋙ li.edge.left ⟶
      ((lg.edge.left ⋙ lf.edge.left).prod (lg.edge.left ⋙ lf.edge.left)) ⋙ X.closed.tensor :=
    Functor.whiskerRight (lk.edge.tensorComparison lg.tensorModelY lk.tensorModelX).hom
      li.edge.left ≫
      Functor.whiskerLeft (lk.edge.left.prod lk.edge.left)
        (li.edge.tensorComparison lk.tensorModelX lf.tensorModelX).hom ≫
      Functor.whiskerRight
        (NatTrans.prod s.derivedComparison.hom s.derivedComparison.hom) X.closed.tensor
  have heq : l = r := by
    obtain ⟨P, hP, _, _, hd⟩ := site_derived_tensor_descent.{u, w, u + 1, w} Z.J Z.A
    apply (hd _ inferInstance _ _).injective
    ext A
    obtain ⟨hp, hpf⟩ := (hP A.1.obj).1 A.1.property
    obtain ⟨hq, hqf⟩ := (hP A.2.obj).1 A.2.property
    have hh : l.app (DerivedCategory.Q.obj A.1.obj.as, DerivedCategory.Q.obj A.2.obj.as) =
        r.app (DerivedCategory.Q.obj A.1.obj.as, DerivedCategory.Q.obj A.2.obj.as) :=
      ringedSquareTensorCompatibility s lg.tensorModelY lg.tensorModelX
        lk.tensorModelX lf.tensorModelX s.derivedComparison
        (Classical.choose_spec s.derivedComparison_existsUnique.exists)
        A.1.obj.as A.2.obj.as hp hpf hq hqf
    let e := (DerivedCategory.quotientCompQhIso Z.modules).app A.1.obj.as |>.symm.prod
      ((DerivedCategory.quotientCompQhIso Z.modules).app A.2.obj.as).symm
    change l.app (DerivedCategory.Qh.obj A.1.obj, DerivedCategory.Qh.obj A.2.obj) =
      r.app (DerivedCategory.Qh.obj A.1.obj, DerivedCategory.Qh.obj A.2.obj)
    apply (cancel_epi ((Z.closed.tensor ⋙ lk.edge.left ⋙ li.edge.left).map e.hom)).mp
    exact (l.naturality e.hom).trans
      ((congrArg (fun z ↦ z ≫
        (((lg.edge.left ⋙ lf.edge.left).prod (lg.edge.left ⋙ lf.edge.left)) ⋙
          X.closed.tensor).map e.hom) hh).trans (r.naturality e.hom).symm)
  have hLf : lf.edge.tensorComparison lg.tensorModelX lf.tensorModelX =
      lf.edge.tensorComparison lf.tensorModelY lf.tensorModelX := by rw [hYY]
  have hLk : lk.edge.tensorComparison lg.tensorModelY lk.tensorModelX =
      lk.edge.tensorComparison lk.tensorModelY lk.tensorModelX := by rw [hZY]
  have hLi : li.edge.tensorComparison lk.tensorModelX lf.tensorModelX =
      li.edge.tensorComparison li.tensorModelY li.tensorModelX := by rw [hXX, hXI]
  intro U V
  have hh := congr_app heq (U, V)
  simp only [l, r, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.prod, hLf, hLk, hLi,
    ← lf.tensor_canonical, ← lg.tensor_canonical, ← lk.tensor_canonical,
    ← li.tensor_canonical] at hh
  exact hh

-- Comparing the four recorded site presentations requires additional definitional equality work.
open CategoryTheory.MonoidalCategory in
private theorem unit_of_tensor
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
    {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (c : F ≅ G)
    (h : ∀ U V, c.hom.app (U ⊗ V) ≫ Functor.OplaxMonoidal.δ G U V =
      Functor.OplaxMonoidal.δ F U V ≫ (c.hom.app U ⊗ₘ c.hom.app V)) :
    c.hom.app (𝟙_ C) ≫ Functor.OplaxMonoidal.η G = Functor.OplaxMonoidal.η F := by
  have hh := c.hom.naturality (λ_ (𝟙_ C)).hom
  rw [← Functor.OplaxMonoidal.left_unitality_hom F,
    ← Functor.OplaxMonoidal.left_unitality_hom G] at hh
  simp only [Category.assoc] at hh
  rw [← Category.assoc (c.hom.app _), h, Category.assoc] at hh
  rw [← leftUnitor_naturality] at hh
  simp only [← tensorHom_id, ← id_tensorHom] at hh
  have hh' := (cancel_epi (Functor.OplaxMonoidal.δ F (𝟙_ C) (𝟙_ C))).mp hh
  simp only [← Category.assoc] at hh'
  have hh'' := (cancel_mono (λ_ (G.obj (𝟙_ C))).hom).mp hh'
  have hright := congrArg (fun z ↦ z ≫ (𝟙 (𝟙_ D) ⊗ₘ c.inv.app (𝟙_ C))) hh''
  simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
    Iso.hom_inv_id_app] at hright
  let : (tensorRight (𝟙_ D)).Faithful :=
    Functor.Faithful.of_iso (rightUnitorNatIso D).symm
  let : (tensorRight (F.obj (𝟙_ C))).Faithful :=
    Functor.Faithful.of_iso ((curriedTensor D).flip.mapIso
      (Functor.Monoidal.εIso F))
  apply (tensorRight (F.obj (𝟙_ C))).map_injective
  change (c.hom.app (𝟙_ C) ≫ Functor.OplaxMonoidal.η G) ▷ F.obj (𝟙_ C) =
    Functor.OplaxMonoidal.η F ▷ F.obj (𝟙_ C)
  simpa only [← tensorHom_id] using hright.symm

-- The two complex adjunctions and their derived counterparts have different presentation wrappers.
-- Resolve the source and compare both composite adjunctions without unfolding their constructions.
end CategoryTheory.RingedDerivedComparisons
