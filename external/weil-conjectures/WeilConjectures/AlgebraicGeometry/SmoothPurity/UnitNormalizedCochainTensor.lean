/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryTensorPullbackData
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import all WeilConjectures.CategoryTheory.ScalarHomTensor.ScalarHomTensorComparison
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # The unit-normalized cochain tensor comparison

Source: Stacks Project, Cohomology on Sites, Tag 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe c v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures.SemilinearSections

private theorem normalizedTensor_inverse_square
    {A : Type*} [Category* A] {W X Y Z : A} (a : W ≅ X) (b : Y ≅ Z)
    {i : X ⟶ Y} {j : W ⟶ Z} (h : i ≫ b.hom = a.inv ≫ j) :
    j ≫ b.inv = a.hom ≫ i := by
  apply b.comp_inv_eq.mpr
  exact (a.inv_comp_eq.mp h.symm).trans (Category.assoc _ _ _).symm

variable {C D : Type c} [Category.{v} C] [Category.{v} D]
  [EssentiallySmall.{max c v r} C] [EssentiallySmall.{max c v r} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [HasSheafify K AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (U : C ⥤ D) [U.IsContinuous J K]
  (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf K CommRingCat.{max c v r})
  (phi : R ⟶ (U.sheafPushforwardContinuous CommRingCat.{max c v r} J K).obj S)
  (F : Mod.{c, v, max c v r} J R ⥤ Mod.{c, v, max c v r} K S) [F.Additive]
  (adj : F ⊣ SheafOfModules.pushforward.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map phi))

/-- The normalized ordinary tensor comparisons determine a unique normalized comparison
on arbitrary unbounded cochain complexes.
Source: Stacks Project, Cohomology on Sites, Tag 07A4
(blueprint: lem-pur-unit-normalized-cochain-tensor).
Proof: totalize the inverse ordinary comparisons to obtain a map from the tensor
of the two pulled back complexes to the pullback of their tensor. The left adjoint
preserves the coproducts, so this map is an isomorphism. Two-variable naturality
makes it a natural isomorphism. On each total summand, its inverse satisfies the
ordinary comparison equation. Naturality of the adjunction unit and the ordinary
pure-tensor normalization therefore give the stated generator equation. To prove
uniqueness, transpose a competing map through the ordinary adjunction in each
degree. Equality on all pure tensors in all summands determines those transposes,
and injectivity of the adjunction bijection gives equality of the chain maps. -/
theorem unitNormalizedCochainTensor
    (data : OrdinaryTensorPullbackData J K U R S phi F adj) :
    ∃! e : coefficientTotalTensor.{r, c, v} J R ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      ((F.mapHomologicalComplex (.up ℤ)).prod
        (F.mapHomologicalComplex (.up ℤ))) ⋙ coefficientTotalTensor.{r, c, v} K S,
      ∀ (P Q : CochainComplex (Mod.{c, v, max c v r} J R) ℤ)
        (p q k : ℤ) (h : p + q = k) (V : C)
        (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)),
        ((e.hom.app (P,Q)).f k).val.app (op (U.obj V))
          ((adj.unit.app (((coefficientTotalTensor.{r, c, v} J R).obj (P,Q)).X k)).val.app
            (op V) (coefficientTensorGenerator.{r, c, v} J R P Q p q k h (op V) x y)) =
        coefficientTensorGenerator.{r, c, v} K S
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q k h (op (U.obj V))
          ((adj.unit.app (P.X p)).val.app (op V) x)
          ((adj.unit.app (Q.X q)).val.app (op V) y) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.isMonoidal_W_independentCoefficients S
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let := SheafOfModules.cochainModulesPreadditive R
  let := SheafOfModules.cochainModulesPreadditive S
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients S
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients S
  let mu := data.ordinary
  have hmu : ∀ {M M' N N'} (a : M ⟶ M') (b : N ⟶ N'),
      F.map (a ⊗ₘ b) ≫ (mu M' N').hom =
        (mu M N).hom ≫ (F.map a ⊗ₘ F.map b) := by
    intro M M' N N' a b
    exact data.normalized.2 M M' N N' a b
  let tY := coefficientTotalTensor.{r, c, v} J R
  let tX := coefficientTotalTensor.{r, c, v} K S
  let FC := F.mapHomologicalComplex (.up ℤ)
  have hiso (P Q : CochainComplex (Mod.{c, v, max c v r} J R) ℤ) :
      IsIso (tensorPullbackTotal F mu hmu P Q) :=
    tensorPullbackTotal_isIso F mu hmu _ adj P Q
  let b0 : (FC.prod FC) ⋙ tX ≅ tY ⋙ FC := NatIso.ofComponents
    (fun C ↦ @asIso _ _ _ _ (tensorPullbackTotal F mu hmu C.1 C.2) (hiso C.1 C.2)) (by
      intro C D a
      dsimp only [FC, tY, tX, Functor.comp_map, Functor.prod_map]
      simp only [coefficientTotalTensor, Functor.uncurry_obj_map,
        Functor.map₂HomologicalComplex, asIso_hom,
        CategoryTheory.ScalarHomTensor.tensorMap_factor]
      exact CategoryTheory.ScalarHomTensor.tensorPullbackTotal_naturality F mu hmu a.1 a.2)
  let beta := b0.symm
  have hbeta (P Q : CochainComplex (Mod.{c, v, max c v r} J R) ℤ)
      (p q k : ℤ) (h : p + q = k) (W : C)
      (x : (P.X p).val.obj (op W)) (y : (Q.X q).val.obj (op W)) :
      ((beta.hom.app (P,Q)).f k).val.app (op (U.obj W))
        ((adj.unit.app ((tY.obj (P,Q)).X k)).val.app (op W)
          (coefficientTensorGenerator.{r, c, v} J R P Q p q k h (op W) x y)) =
      coefficientTensorGenerator.{r, c, v} K S (FC.obj P) (FC.obj Q)
        p q k h (op (U.obj W))
        ((adj.unit.app (P.X p)).val.app (op W) x)
        ((adj.unit.app (Q.X q)).val.app (op W) y) := by
    let i := CochainComplex.ιMapBifunctor P Q
      (CategoryTheory.MonoidalCategory.curriedTensor _) p q k h
    let i' := CochainComplex.ιMapBifunctor (FC.obj P) (FC.obj Q)
      (CategoryTheory.MonoidalCategory.curriedTensor _) p q k h
    let z := (HomologicalComplex.eval _ (.up ℤ) k).mapIso (b0.app (P,Q))
    have hz : i' ≫ z.hom = (mu (P.X p) (Q.X q)).inv ≫ F.map i := by
      change i' ≫ tensorPullbackTotalComponent F mu P Q k = _
      exact HomologicalComplex.ι_mapBifunctorDesc _ p q h
    have hi : F.map i ≫ z.inv = (mu (P.X p) (Q.X q)).hom ≫ i' :=
      normalizedTensor_inverse_square (mu (P.X p) (Q.X q)) z hz
    have hu := congrArg (fun a ↦ a.val.app (op W)
      (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) (op W) x y))
      (adj.unit.naturality i)
    have hh := congrArg (fun a ↦ a.val.app (op (U.obj W))
      ((adj.unit.app (P.X p ⊗ Q.X q)).val.app (op W)
        (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) (op W) x y))) hi
    change z.inv.val.app (op (U.obj W))
      ((adj.unit.app ((tY.obj (P,Q)).X k)).val.app (op W)
        (i.val.app (op W)
          (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) (op W) x y))) = _
    change (adj.unit.app _).val.app (op W)
      (i.val.app (op W)
        (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) (op W) x y)) =
      (F.map i).val.app (op (U.obj W))
        ((adj.unit.app (P.X p ⊗ Q.X q)).val.app (op W)
          (SheafOfModules.ScalarHomOrdinary.pure R (P.X p) (Q.X q) (op W) x y)) at hu
    erw [hu]
    have hgen := data.normalized.1 (P.X p) (Q.X q) W (U.obj W) (𝟙 _) x y 1
    simp only [op_id, PresheafOfModules.map_id, one_smul] at hgen
    exact hh.trans (congrArg (i'.val.app (op (U.obj W))) hgen)
  refine ⟨beta, hbeta, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext C
  obtain ⟨P,Q⟩ := C
  apply HomologicalComplex.hom_ext
  intro k
  apply (adj.homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{c, v, r}
    (J := J) (R := R) P Q k _
  intro p q h W x y
  change ((e.hom.app (P,Q)).f k).val.app (op (U.obj W.unop))
      ((adj.unit.app _).val.app W
        (coefficientTensorGenerator.{r, c, v} J R P Q p q k h W x y)) =
    ((beta.hom.app (P,Q)).f k).val.app (op (U.obj W.unop))
      ((adj.unit.app _).val.app W
        (coefficientTensorGenerator.{r, c, v} J R P Q p q k h W x y))
  exact (he P Q p q k h W.unop x y).trans (hbeta P Q p q k h W.unop x y).symm

end WeilConjectures.SemilinearSections
