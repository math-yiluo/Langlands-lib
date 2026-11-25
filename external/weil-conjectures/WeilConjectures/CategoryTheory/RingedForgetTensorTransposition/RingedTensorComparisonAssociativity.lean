/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedTensorAssociatorDetection
import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorModelAssociativity

/-! # Associativity of summand-normalized ringed tensor comparisons
Source: Stacks 03EL, 06YU and 0FPT.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.MonoidalCategory
open WeilConjectures
namespace CategoryTheory.RingedForgetTensorTransposition
attribute [local irreducible] SheafOfModules.monoidalCategory
  PresheafOfModules.sheafificationAdjunction SheafOfModules.tensorObjIsoSheafification
universe c v r d vd s
open CategoryTheory.RingedForgetTensorTransposition
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
/-- The canonical summand inclusion for the signed total tensor of module sheaves.
Source: Stacks 06YN (blueprint: lem-pur-ringed-tensor-comparison-associativity).
This is the actual cochain bifunctor summand, with the canonical sheaf tensor instances. -/
def coefficientTensorSummand (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    (SheafOfModules.monoidalCategory R).tensorObj (P.X p) (Q.X q) ⟶
      ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X n :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  CochainComplex.ιMapBifunctor P Q (MonoidalCategory.curriedTensor _) p q n hpq

variable {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive]

/-- Coherence on pure-triple model associators, with the total comparison kept abstract.
Source: Stacks 03EL, 06YU and 0FPT
(blueprint: lem-pur-ringed-tensor-comparison-associativity). -/
structure RingedTensorComparisonCoherence
    (chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{s, d, vd} J' R') : Prop where
  /-- The comparison respects any model associators with their local generator formulas. -/
  model_associativity :
    ∀ (P Q N : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (aB : (coefficientTotalTensor.{r, c, v} J R).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q), N) ≅
      (coefficientTotalTensor.{r, c, v} J R).obj
        (P, (coefficientTotalTensor.{r, c, v} J R).obj (Q, N)))
    (aA : (coefficientTotalTensor.{s, d, vd} J' R').obj
        ((coefficientTotalTensor.{s, d, vd} J' R').obj
          ((U.mapHomologicalComplex (.up ℤ)).obj P, (U.mapHomologicalComplex (.up ℤ)).obj Q),
          (U.mapHomologicalComplex (.up ℤ)).obj N) ≅
      (coefficientTotalTensor.{s, d, vd} J' R').obj
        ((U.mapHomologicalComplex (.up ℤ)).obj P,
          (coefficientTotalTensor.{s, d, vd} J' R').obj
            ((U.mapHomologicalComplex (.up ℤ)).obj Q, (U.mapHomologicalComplex (.up ℤ)).obj N)))
    (_haB : ∀ (p q t pq qt n : ℤ) (hpq : p + q = pq) (hqt : q + t = qt)
      (hn : pq + t = n) (hn' : p + qt = n) (V : Cᵒᵖ)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) (z : (N.X t).val.obj V),
      (aB.hom.f n).val.app V
        (coefficientTensorGenerator.{r, c, v} J R
          ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) N pq t n hn V
          (coefficientTensorGenerator.{r, c, v} J R P Q p q pq hpq V x y) z) =
      coefficientTensorGenerator.{r, c, v} J R P
        ((coefficientTotalTensor.{r, c, v} J R).obj (Q, N)) p qt n hn' V x
        (coefficientTensorGenerator.{r, c, v} J R Q N q t qt hqt V y z))
    (_haA : ∀ (p q t pq qt n : ℤ) (hpq : p + q = pq) (hqt : q + t = qt)
      (hn : pq + t = n) (hn' : p + qt = n) (V : Dᵒᵖ)
      (x : (((U.mapHomologicalComplex (.up ℤ)).obj P).X p).val.obj V)
      (y : (((U.mapHomologicalComplex (.up ℤ)).obj Q).X q).val.obj V)
      (z : (((U.mapHomologicalComplex (.up ℤ)).obj N).X t).val.obj V),
      (aA.hom.f n).val.app V
        (coefficientTensorGenerator.{s, d, vd} J' R'
          ((coefficientTotalTensor.{s, d, vd} J' R').obj
            (((U.mapHomologicalComplex (.up ℤ)).obj P), ((U.mapHomologicalComplex (.up ℤ)).obj Q)))
          ((U.mapHomologicalComplex (.up ℤ)).obj N) pq t n hn V
          (coefficientTensorGenerator.{s, d, vd} J' R'
            ((U.mapHomologicalComplex (.up ℤ)).obj P) ((U.mapHomologicalComplex (.up ℤ)).obj Q)
            p q pq hpq V x y) z) =
      coefficientTensorGenerator.{s, d, vd} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
        ((coefficientTotalTensor.{s, d, vd} J' R').obj
          (((U.mapHomologicalComplex (.up ℤ)).obj Q), ((U.mapHomologicalComplex (.up ℤ)).obj N)))
        p qt n hn' V x
        (coefficientTensorGenerator.{s, d, vd} J' R'
          ((U.mapHomologicalComplex (.up ℤ)).obj Q) ((U.mapHomologicalComplex (.up ℤ)).obj N)
          q t qt hqt V y z)),
    let V := U.mapHomologicalComplex (.up ℤ)
    let B := coefficientTotalTensor.{r, c, v} J R
    let A := coefficientTotalTensor.{s, d, vd} J' R'
    V.map aB.hom ≫ chain.hom.app (P, B.obj (Q, N)) ≫
        A.map (X := (V.obj P, V.obj (B.obj (Q, N))))
          (Y := (V.obj P, A.obj (V.obj Q, V.obj N)))
          (𝟙 (V.obj P), chain.hom.app (Q, N)) =
      chain.hom.app (B.obj (P, Q), N) ≫
        A.map (X := (V.obj (B.obj (P, Q)), V.obj N))
          (Y := (A.obj (V.obj P, V.obj Q), V.obj N))
          (chain.hom.app (P, Q), 𝟙 (V.obj N)) ≫ aA.hom

/-- A summand-normalized natural tensor comparison respects pure-triple model associators.
Source: Stacks 03EL, 06YU and 0FPT
(blueprint: lem-pur-ringed-tensor-comparison-associativity).
Proof: the local pure-triple formulas identify both supplied model associators
with the native complex associators. Install the canonical sheaf monoidal
structures and unfold only the total-tensor and summand aliases. The abstract
model-chain associativity theorem applies to the ordinary inverse associativity
formula and the total-summand formula. No derived localization, preservation of
internal Hom, or flatness assertion is used. -/
theorem ringed_tensorComparison_associativity
    (ν : @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R) ⋙ U ≅
      (U.prod U) ⋙ @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R'))
    (hν : letI := SheafOfModules.monoidalCategory R
      letI := SheafOfModules.monoidalCategory R'
      ∀ X Y Z, (ν.inv.app (X, Y) ▷ U.obj Z) ≫ ν.inv.app (X ⊗ Y, Z) ≫
        U.map (α_ X Y Z).hom = (α_ (U.obj X) (U.obj Y) (U.obj Z)).hom ≫
          (U.obj X ◁ ν.inv.app (Y, Z)) ≫ ν.inv.app (X, Y ⊗ Z))
    (chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{s, d, vd} J' R')
    (summand : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (p q n : ℤ) (hpq : p + q = n),
      U.map (coefficientTensorSummand.{c, v, r} J R P Q p q n hpq) ≫ (chain.hom.app (P, Q)).f n =
        ν.hom.app (P.X p, Q.X q) ≫
          coefficientTensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
            ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq) :
    RingedTensorComparisonCoherence J R J' R' U chain := by
  constructor
  intro P Q N aB aA haB haA
  have hB := coefficientAssociator_eq_native.{c, v, r} J R P Q N aB haB
  have hA := coefficientAssociator_eq_native.{d, vd, s} J' R'
    ((U.mapHomologicalComplex (.up ℤ)).obj P) ((U.mapHomologicalComplex (.up ℤ)).obj Q)
    ((U.mapHomologicalComplex (.up ℤ)).obj N) aA haA
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{c, v, max c v r} R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{d, vd, max d vd s} R'
  let := SheafOfModules.monoidalCategory R'
  unfold coefficientTensorSummand at summand
  unfold coefficientTotalTensor at chain summand aB aA hB hA
  dsimp only
  delta coefficientTotalTensor
  exact tensorComparison_model_chain_associativity U ν chain summand hν
    P Q N aB aA hB hA

end CategoryTheory.RingedForgetTensorTransposition
