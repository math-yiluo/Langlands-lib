/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceEvaluationModels
import all WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
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
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Slice evaluation on resolved representatives

Source: Stacks Project, Tags 07A4, 08J9 and 08JB
(blueprint: lem-weil-pbc-ringed-slice-representative-evaluation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe c v u w w' a b x y

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures MonoidalCategory

namespace CategoryTheory

attribute [local instance 20000] siteAbelianHasSheafify siteAbelianWEqualsLocallyBijective

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
  CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

section Generic
variable {D : Type a} [Category.{x} D] {H : Dᵒᵖ × D ⥤ D}

private theorem evaluation_iso_naturality
    (S : CoefficientClosedStructure H) {P Q L M : D} (e : P ≅ L) (g : Q ⟶ M) :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom e.inv.op g)) e.hom) ≫
        S.evaluation L M = S.evaluation P Q ≫ g := by
  let := S.monoidal
  have hn : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op L)) g)) (𝟙 L)) ≫
      S.evaluation L M = S.evaluation L Q ≫ g := by
    simpa only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
      MonoidalCategory.tensor_map, MonoidalCategory.tensorRight,
      Functor.flip, MonoidalCategory.curriedTensor, MonoidalCategory.tensorHom_id,
      Functor.comp_map, Prod.sectR, Functor.id_map] using
      (S.adjunction L).counit.naturality g
  have he : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom e.inv.op (𝟙 Q))) (𝟙 L)) ≫
      S.evaluation L Q = S.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, Q))) e.inv) ≫
        S.evaluation P Q := by
    simpa only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
      MonoidalCategory.tensor_map, MonoidalCategory.tensorRight, MonoidalCategory.tensorLeft,
      Functor.flip, MonoidalCategory.curriedTensor, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom] using S.evaluation_naturality P L Q e.inv
  have hh : H.map (Prod.mkHom e.inv.op g) =
      H.map (Prod.mkHom e.inv.op (𝟙 Q)) ≫
        H.map (Prod.mkHom (𝟙 (op L)) g) := by
    rw [← H.map_comp]
    simp
  rw [hh]
  have ht : S.tensor.map
      (Prod.mkHom (H.map (Prod.mkHom e.inv.op (𝟙 Q)) ≫
        H.map (Prod.mkHom (𝟙 (op L)) g)) e.hom) =
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, Q))) e.hom) ≫
        S.tensor.map (Prod.mkHom (H.map (Prod.mkHom e.inv.op (𝟙 Q))) (𝟙 L)) ≫
          S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op L)) g)) (𝟙 L)) := by
    simp only [← S.tensor.map_comp]
    congr 1
    ext <;> simp
  rw [ht]
  simp only [Category.assoc]
  rw [hn, ← Category.assoc _ (S.evaluation L Q) g, he]
  simp only [Category.assoc]
  simp only [← Category.assoc, ← S.tensor.map_comp]
  simp

private theorem evaluation_of_models
    {E : Type b} [Category.{y} E] {HU : Eᵒᵖ × E ⥤ E}
    (S : CoefficientClosedStructure H) (SU : CoefficientClosedStructure HU)
    {r : D ⥤ E} {K : Prop} (d : RingedSliceEvaluationComparisons H HU r S SU K)
    {X P I Z : D} {XU PU IU ZU : E}
    (i : Z ≅ S.tensor.obj (X, P)) (j : ZU ≅ SU.tensor.obj (XU, PU))
    (aX : r.obj X ≅ XU) (aP : r.obj P ≅ PU) (aI : r.obj I ≅ IU)
    (c : r.obj Z ≅ ZU) (t : X ≅ H.obj (op P, I))
    (u : XU ⟶ HU.obj (op PU, IU)) (f : Z ⟶ I) (fU : ZU ⟶ IU)
    (hi : i.hom ≫ S.tensor.map (t.hom, 𝟙 P) ≫ S.evaluation P I = f)
    (hj : j.hom ≫ SU.tensor.map (u, 𝟙 PU) ≫ SU.evaluation PU IU = fU)
    (ht : r.map i.hom ≫ (d.rho X P).hom ≫
      SU.tensor.map (aX.hom, aP.hom) = c.hom ≫ j.hom)
    (hh : r.map t.hom ≫ (d.eta P I).hom ≫ HU.map (aP.inv.op, aI.hom) =
      aX.hom ≫ u)
    (hc : r.map f ≫ aI.hom = c.hom ≫ fU) :
    (d.rho (H.obj (op P, I)) P).inv ≫ r.map (S.evaluation P I) =
      SU.tensor.map ((d.eta P I).hom, 𝟙 (r.obj P)) ≫
        SU.evaluation (r.obj P) (r.obj I) := by
  apply (cancel_epi (d.rho (H.obj (op P, I)) P).hom).1
  rw [Iso.hom_inv_id_assoc]
  have htiso : IsIso (Prod.mkHom t.hom (𝟙 P)) :=
    (isIso_prod_iff (f := Prod.mkHom t.hom (𝟙 P))).2 ⟨inferInstance, inferInstance⟩
  have : IsIso (S.tensor.map (Prod.mkHom t.hom (𝟙 P))) := inferInstance
  apply (cancel_epi (r.map (S.tensor.map
    (X := (X, P)) (Y := (H.obj (op P, I), P)) (Prod.mkHom t.hom (𝟙 P))))).1
  apply (cancel_epi (r.map i.hom)).1
  apply (cancel_mono aI.hom).1
  have hn := evaluation_iso_naturality SU aP aI.hom
  have hn' : SU.tensor.map ((d.eta P I).hom, 𝟙 (r.obj P)) ≫
      SU.evaluation (r.obj P) (r.obj I) ≫ aI.hom =
      SU.tensor.map (X := (r.obj (H.obj (op P, I)), r.obj P))
        (Y := (HU.obj (op PU, IU), PU))
        ((d.eta P I).hom ≫ HU.map (aP.inv.op, aI.hom), aP.hom) ≫
        SU.evaluation PU IU := by
    rw [← hn]
    simp only [← Category.assoc, ← SU.tensor.map_comp]
    congr 2
    simp only [prod_comp, Category.id_comp]
  have hcomp :
      SU.tensor.map (r.map t.hom, 𝟙 (r.obj P)) ≫
        SU.tensor.map (X := (r.obj (H.obj (op P, I)), r.obj P))
        (Y := (HU.obj (op PU, IU), PU))
        ((d.eta P I).hom ≫ HU.map (aP.inv.op, aI.hom), aP.hom) =
      SU.tensor.map (X := (r.obj X, r.obj P)) (Y := (XU, PU)) (aX.hom, aP.hom) ≫
        SU.tensor.map (X := (XU, PU)) (Y := (HU.obj (op PU, IU), PU)) (u, 𝟙 PU) := by
    simp only [← SU.tensor.map_comp, prod_comp, Category.id_comp, Category.comp_id]
    congr 1
    exact Prod.ext hh rfl
  have hnat := d.rho_naturality X P (H.obj (op P, I)) P t.hom (𝟙 P)
  simp only [Functor.map_id] at hnat
  calc
    (r.map i.hom ≫ r.map (S.tensor.map (t.hom, 𝟙 P)) ≫
        r.map (S.evaluation P I)) ≫ aI.hom = r.map f ≫ aI.hom := by
      rw [← r.map_comp, ← r.map_comp, hi]
    _ = c.hom ≫ fU := hc
    _ = (r.map i.hom ≫ (d.rho X P).hom ≫
        SU.tensor.map (X := (r.obj X, r.obj P)) (Y := (XU, PU)) (aX.hom, aP.hom)) ≫
        SU.tensor.map (X := (XU, PU)) (Y := (HU.obj (op PU, IU), PU))
          (u, 𝟙 PU) ≫ SU.evaluation PU IU := by
      rw [ht, Category.assoc, hj]
    _ = r.map i.hom ≫ (d.rho X P).hom ≫
        SU.tensor.map (r.map t.hom, 𝟙 (r.obj P)) ≫
        SU.tensor.map (X := (r.obj (H.obj (op P, I)), r.obj P))
        (Y := (HU.obj (op PU, IU), PU))
        ((d.eta P I).hom ≫ HU.map (aP.inv.op, aI.hom), aP.hom) ≫
        SU.evaluation PU IU := by
      simp only [Category.assoc]
      rw [reassoc_of% hcomp]
    _ = (r.map i.hom ≫ r.map (S.tensor.map (t.hom, 𝟙 P)) ≫
        (d.rho (H.obj (op P, I)) P).hom ≫
        SU.tensor.map ((d.eta P I).hom, 𝟙 (r.obj P)) ≫
        SU.evaluation (r.obj P) (r.obj I)) ≫ aI.hom := by
      simp only [Category.assoc]
      rw [hn', ← reassoc_of% hnat]

private theorem untranspose_formula (S : CoefficientClosedStructure H)
    (X P I : D) (q : X ⟶ H.obj (op P, I)) :
    (S.transpose X P I).symm q = S.tensor.map (q, 𝟙 P) ≫ S.evaluation P I := by
  let := S.monoidal
  dsimp only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    CoefficientClosedStructure.evaluation, MonoidalCategory.tensor_obj,
    MonoidalCategory.tensor_map]
  rw [MonoidalCategory.tensorHom_id]
  change ((S.adjunction P).homEquiv X I).symm q =
    (@MonoidalCategory.tensorRight D _ S.monoidal P).map q ≫
      (S.adjunction P).counit.app I
  exact (S.adjunction P).homEquiv_symm_apply X I q

private theorem inverse_of_model {X Y Z : D} (κ : X ≅ Y) (e : X ≅ Z)
    (a : Y ⟶ Z) (h : κ.hom ≫ a = e.hom) : a ≫ e.inv = κ.inv := by
  apply (cancel_epi κ.hom).1
  rw [← Category.assoc, h, Iso.hom_inv_id, Iso.hom_inv_id]

private theorem map_hom_square_inverse
    {E : Type b} [Category.{y} E] (r : D ⥤ E) {X P Q : D}
    {XU YU PU QU R : E} (q : X ⟶ Q) (κ : P ≅ Q) (κU : PU ≅ QU)
    (a : r.obj P ⟶ R) (b : R ⟶ PU) (αX : r.obj X ⟶ XU) (αQ : r.obj Q ⟶ YU)
    (qU : XU ⟶ YU) (γ : YU ⟶ QU)
    (h : r.map κ.hom ≫ αQ ≫ γ = a ≫ b ≫ κU.hom)
    (hq : r.map q ≫ αQ = αX ≫ qU) :
    r.map (q ≫ κ.inv) ≫ a ≫ b = αX ≫ (qU ≫ γ) ≫ κU.inv := by
  have hκ : r.map κ.inv ≫ a ≫ b ≫ κU.hom = αQ ≫ γ := by
    rw [← h, ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id,
      Category.id_comp]
  have hκ' := congrArg (fun z ↦ z ≫ κU.inv) hκ
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hκ'
  simp only [Functor.map_comp, Category.assoc]
  rw [hκ', ← Category.assoc _ _ (γ ≫ κU.inv), hq, Category.assoc]

end Generic

set_option hygiene false in
local notation "Mod" => SheafOfModules.{max c v u} ((sheafCompose J
  (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)

attribute [local irreducible] homComplexFunctor coefficientTotalTensor coefficientTensorGenerator
  coefficientHomResolution coefficientHomResolutionIso coefficientHomResolutionInverse

private theorem model_evaluation
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (Q P I : CochainComplex Mod ℤ)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (κ : (derivedInternalHomOfUniverses.{c, v, u, w} J A).obj
      (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (homComplex (R := A) P I))
    (hκ : RingedKInjectiveHomModel.{c, v, u, w} J A P I κ)
    (q : Q ⟶ homComplex (R := A) P I) :
    (T.iso J A S Q P hQ hP).hom ≫
      S.tensor.map (DerivedCategory.Q.map q ≫ κ.inv, 𝟙 (DerivedCategory.Q.obj P)) ≫
      S.evaluation (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I) =
    DerivedCategory.Q.map ((RingedDerivedNative.chainEquiv.{c, v, u} J A Q P I).symm q) := by
  have hc : IsCoefficientTensorCurry.{u, c, v} J A Q P I
      ((RingedDerivedNative.chainEquiv.{c, v, u} J A Q P I).symm q) q := by
    intro a b V x y
    exact RingedDerivedNative.chainEquiv_symm_pure.{c, v, u, w}
      J A Q P I q a b (a + b) rfl (add_comm b a) V x y
  have hn := coefficientTensorCurry_normalize.{u, c, v, w} J A S T Q P I hQ hP
    _ q hc
  have hk : DerivedCategory.Q.map
      (((homComplexFunctor (R := A)).obj (op P)).map
        ((WeilConjectures.coefficientHomAugmentation.{u, c, v} J A).app I)) ≫
      (coefficientHomResolutionIso.{u, c, v, w} J A P I).inv = κ.inv := by
    exact inverse_of_model κ (coefficientHomResolutionIso.{u, c, v, w} J A P I)
      _ hκ
  have harg : DerivedCategory.Q.map
      (q ≫ ((homComplexFunctor (R := A)).obj (op P)).map
        ((WeilConjectures.coefficientHomAugmentation.{u, c, v} J A).app I)) ≫
      (coefficientHomResolutionIso.{u, c, v, w} J A P I).inv =
      DerivedCategory.Q.map q ≫ κ.inv := by
    calc
      _ = (DerivedCategory.Q.map q ≫ DerivedCategory.Q.map
          (((homComplexFunctor (R := A)).obj (op P)).map
            ((WeilConjectures.coefficientHomAugmentation.{u, c, v} J A).app I))) ≫
          (coefficientHomResolutionIso.{u, c, v, w} J A P I).inv :=
        congrArg (fun f ↦ f ≫ (coefficientHomResolutionIso.{u, c, v, w} J A P I).inv)
          (DerivedCategory.Q.map_comp q _)
      _ = DerivedCategory.Q.map q ≫ κ.inv :=
        (Category.assoc _ _ _).trans (congrArg (DerivedCategory.Q.map q ≫ ·) hk)
  rw [harg] at hn
  have ht : (S.transpose (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj I)).symm (DerivedCategory.Q.map q ≫ κ.inv) =
      S.tensor.map (DerivedCategory.Q.map q ≫ κ.inv, 𝟙 (DerivedCategory.Q.obj P)) ≫
        S.evaluation (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I) :=
    untranspose_formula S _ _ _ (DerivedCategory.Q.map q ≫ κ.inv)
  rw [ht] at hn
  exact (Iso.eq_inv_comp _).1 hn

section SliceChains
variable (U : C)
  [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U)
    (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]

set_option hygiene false in
local notation "rC" => ringedSliceComplexRestriction.{c, v, u} J A U
set_option hygiene false in
local notation "tot" => coefficientTotalTensor.{u, c, v} J A
set_option hygiene false in
local notation "totU" => coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U)

-- The local-family formula has dependent slice-section and complex-degree endpoints.
private theorem slice_uncurry
    (Q P I : CochainComplex Mod ℤ) (q : Q ⟶ homComplex (R := A) P I)
    (γt : (rC).obj ((tot).obj (Q, P)) ≅ (totU).obj ((rC).obj Q, (rC).obj P))
    (γh : (rC).obj (homComplex (R := A) P I) ≅
      homComplex (R := A.over U) ((rC).obj P) ((rC).obj I))
    (ht : ∀ (p a k : ℤ) (h : p + a = k) (V : Over U)
      (x : (Q.X p).val.obj (op V.left)) (y : (P.X a).val.obj (op V.left)),
      (γt.hom.f k).val.app (op V)
        (coefficientTensorGenerator.{u, c, v} J A Q P p a k h (op V.left) x y) =
      coefficientTensorGenerator.{u, max c v, v} (J.over U) (A.over U)
        ((rC).obj Q) ((rC).obj P) p a k h (op V) x y)
    (hh : ∀ (n p k : ℤ) (h : p + n = k) (V : Over U) (W : Over V)
      (x : (P.X p).val.obj (op W.left.left))
      (z : ((homComplex (R := A) P I).X n).val.obj (op V.left)),
      (((coefficientHomComponent.{u, max c v, v} (J.over U) (A.over U)
        ((rC).obj P) ((rC).obj I) n p k h).val.app (op V)
        ((γh.hom.f n).val.app (op V) z)).app (op W)).hom x =
      (((coefficientHomComponent.{u, c, v} J A P I n p k h).val.app (op V.left) z).app
        (op (Over.mk W.hom.left))).hom x) :
    (rC).map ((RingedDerivedNative.chainEquiv.{c, v, u} J A Q P I).symm q) =
      γt.hom ≫ ((RingedDerivedNative.chainEquiv.{max c v, v, u}
        (J.over U) (A.over U) ((rC).obj Q) ((rC).obj P) ((rC).obj I)).symm
          ((rC).map q ≫ γh.hom)) := by
  apply (cancel_epi γt.inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply coefficient_total_ext.{u, max c v, v} (J.over U) (A.over U)
  intro p a V x y
  let k := p + a
  have h : p + a = k := rfl
  obtain ⟨V⟩ := V
  have hγ := ht p a k h V x y
  have hinv : (γt.inv.f k).val.app (op V)
      (coefficientTensorGenerator.{u, max c v, v} (J.over U) (A.over U)
        ((rC).obj Q) ((rC).obj P) p a k h (op V) x y) =
      coefficientTensorGenerator.{u, c, v} J A Q P p a k h (op V.left) x y := by
    have he := congrArg (fun f ↦ (f.f k).val.app (op V)
      (coefficientTensorGenerator.{u, c, v} J A Q P p a k h (op V.left) x y))
        γt.hom_inv_id
    exact (congrArg ((γt.inv.f k).val.app (op V)) hγ).symm.trans he
  change (((RingedDerivedNative.chainEquiv.{c, v, u} J A Q P I).symm q).f k).val.app
      (op V.left) ((γt.inv.f k).val.app (op V)
        (coefficientTensorGenerator.{u, max c v, v} (J.over U) (A.over U)
          ((rC).obj Q) ((rC).obj P) p a k h (op V) x y)) = _
  refine (congrArg (fun z ↦
    (((RingedDerivedNative.chainEquiv.{c, v, u} J A Q P I).symm q).f k).val.app
      (op V.left) z) hinv).trans ?_
  refine (RingedDerivedNative.chainEquiv_symm_pure.{c, v, u, w}
    J A Q P I q p a k h (add_comm a p) (op V.left) x y).trans ?_
  exact (hh p a k (add_comm a p) V (Over.mk (𝟙 V)) y
    ((q.f p).val.app (op V.left) x)).symm.trans
      (RingedDerivedNative.chainEquiv_symm_pure.{max c v, v, u, w'}
        (J.over U) (A.over U) ((rC).obj Q) ((rC).obj P) ((rC).obj I)
        ((rC).map q ≫ γh.hom) p a k h (add_comm a p) (op V) x y).symm

end SliceChains

-- Assemble the dependent tensor and Hom normalization squares without unfolding their data.
/-- Normalized slice evaluation on a flat-term K-flat source and K-injective target.
Source: Stacks Project, Tags 08J9 and 08JB
(blueprint: lem-weil-pbc-ringed-slice-representative-evaluation).

Proof: resolve Hom(P,I) by a flat-term K-flat Q. Use the ordinary chain-level
uncurrying equivalence on q:Q to Hom(P,I), and on its restriction followed by the
local-family Hom comparison. The tensor comparison sends every pure-tensor summand
to the same summand, and the Hom comparison evaluates the same local family on every
further slice. Thus the two uncurried maps agree after restriction, by sheafification
and total-summand extensionality. The already proved coefficientTensorCurry_normalize
identifies each localized uncurried map with the derived counit, using precisely the
fixed augmentation equations of kappa and kappa_U. Naturality of the localization
comparison then gives the chain-level equality in the derived category. Substitute
the given tensor and Hom normalization squares. Naturality of evaluation under the
localization isomorphisms identifies their endpoints. Finally cancel the localized
resolution, kappa, and tensor comparison isomorphisms. No evaluation map is inverted,
and the Hom complex is not assumed K-flat. -/
theorem ringedSlice_representativeEvaluation
    (U : C) [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU)
    (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U))
      (ht : RingedSliceTensorModel.{c, v, u, w, w'} J A U S T SU TU d)
      (hh : RingedSliceHomModel.{c, v, u, w, w'} J A U S T SU TU d)
    (P I : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (fP : ∀ n, SheafOfModules.IsFlatOnSite (J := J) (R := A) (P.X n))
    [I.IsKInjective] :
    (d.rho ((derivedInternalHomOfUniverses.{c, v, u, w} J A).obj (op (DerivedCategory.Q.obj P),
      (DerivedCategory.Q.obj I))) (DerivedCategory.Q.obj P)).inv ≫
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).map
            (S.evaluation (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)) =
      SU.tensor.map (X := ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj
        ((derivedInternalHomOfUniverses.{c, v, u, w} J A).obj (op (DerivedCategory.Q.obj P),
      (DerivedCategory.Q.obj I))),
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj (DerivedCategory.Q.obj P))) (Y :=
        ((derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)).obj (op
        ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj (DerivedCategory.Q.obj P)),
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj (DerivedCategory.Q.obj I)),
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj (DerivedCategory.Q.obj P)))
      ((d.eta (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)).hom, 𝟙 _) ≫
        SU.evaluation
          ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj (DerivedCategory.Q.obj P))
          ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj (DerivedCategory.Q.obj I))
      := by
  let r := ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U
  let rC := ringedSliceComplexRestriction.{c, v, u} J A U
  let α := ringedSliceLocalizationIso.{c, v, u, w, w'} J A U
  obtain ⟨κ, κU, γh, hκ, hκU, hγh, hhom⟩ := hh P I
  obtain ⟨Q, q, hQ, fQ, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := A) (homComplex (R := A) P I)
  have fQ' (n : ℤ) : SheafOfModules.IsFlatOnSite (J := J) (R := A) (Q.X n) :=
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso A (Q.X n)).symm (fQ n)
  obtain ⟨γt, hγt, htensor⟩ := ht Q P hQ hP fQ' fP
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  let qU := rC.map q ≫ γh.hom
  let f := (RingedDerivedNative.chainEquiv.{c, v, u} J A Q P I).symm q
  let fU := (RingedDerivedNative.chainEquiv.{max c v, v, u} (J.over U) (A.over U)
    (rC.obj Q) (rC.obj P) (rC.obj I)).symm qU
  apply evaluation_of_models S SU d
    (T.iso J A S Q P hQ hP)
    (TU.iso (J.over U) (A.over U) SU (rC.obj Q) (rC.obj P)
      (d.kflat Q hQ fQ').1 (d.kflat P hP fP).1)
    (α.app Q) (α.app P) (α.app I)
    (α.app ((coefficientTotalTensor.{u, c, v} J A).obj (Q, P)) ≪≫
      DerivedCategory.Q.mapIso γt)
    (asIso (DerivedCategory.Q.map q) ≪≫ κ.symm)
    (DerivedCategory.Q.map qU ≫ κU.inv)
    (DerivedCategory.Q.map f) (DerivedCategory.Q.map fU)
  · exact model_evaluation.{c, v, u, w} J A S T Q P I hQ hP κ hκ q
  · exact model_evaluation.{max c v, v, u, w'} (J.over U) (A.over U) SU TU
      (rC.obj Q) (rC.obj P) (rC.obj I)
      (d.kflat Q hQ fQ').1 (d.kflat P hP fP).1 κU hκU qU
  · simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc,
      α, rC] using htensor
  · change r.map (DerivedCategory.Q.map q ≫ κ.inv) ≫ _ = _
    simpa only [qU, Functor.map_comp, Iso.app_hom, Iso.app_inv, Category.assoc] using
      map_hom_square_inverse r (DerivedCategory.Q.map q) κ κU _ _
        (α.hom.app Q) (α.hom.app (homComplex (R := A) P I))
        (DerivedCategory.Q.map (rC.map q)) (DerivedCategory.Q.map γh.hom)
        hhom (α.hom.naturality q)
  · have hc := slice_uncurry.{c, v, u, w, w'} J A U Q P I q γt γh hγt hγh
    have hn := α.hom.naturality f
    dsimp only [Functor.comp_map] at hn
    change r.map (DerivedCategory.Q.map f) ≫ α.hom.app I = _
    refine hn.trans ((congrArg (fun z ↦ α.hom.app _ ≫ DerivedCategory.Q.map z) hc).trans ?_)
    simp only [Functor.map_comp, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom, Category.assoc, fU, qU, rC]

end CategoryTheory
