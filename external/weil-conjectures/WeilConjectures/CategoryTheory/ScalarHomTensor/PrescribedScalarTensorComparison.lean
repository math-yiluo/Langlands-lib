/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
import WeilConjectures.CategoryTheory.ScalarHomTensor.ScalarHomTensorComparison
import WeilConjectures.Algebra.Homology.Scalar.ScalarHomExtensionKFlat
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Normalized scalar tensor comparison on unbounded derived categories

Source: Stacks Project, Cohomology on Sites, Tag 07A4.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w u u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Functor
open SheafOfModules WeilConjectures
namespace CategoryTheory.ScalarHomTensor
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max c v r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
  [∀ R : Sheaf J CommRingCat.{max c v r},
    HasDerivedCategory.{w} (scalarModules J R)]
  (s : ScalarDerivedPair a)
  (SR : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
  (SS : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J S))
  (TR : CoefficientTensorModels.{r, c, v, w} J R SR)
  (TS : CoefficientTensorModels.{r, c, v, w} J S SS)

/-- The ordinary adjunction unit on local sections of the prescribed scalar pair.
Source: Stacks 03CZ (blueprint: lem-coef-prescribed-scalar-tensor-comparison). -/
noncomputable def pairUnit (X : scalarModules J R) (V : Cᵒᵖ) (x : X.val.obj V) :
    (s.extension.obj X).val.obj V :=
  (s.ordinaryAdjunction.unit.app X).val.app V x

/-- The prescribed unit equals the sheafified tensor-insertion section.
Source: Stacks 03CZ (blueprint: lem-coef-prescribed-scalar-tensor-comparison).
Proof: apply the inverse object transport to the scalar pair's ordinary-unit
formula. Its composite with the forward transport is the identity. -/
theorem pairUnit_eq_tensorSection (X : scalarModules J R) (V : Cᵒᵖ)
    (x : X.val.obj V) :
    pairUnit.{c, v, r, w} a s X V x =
      (eqToHom (s.extension_obj X).symm).val.app V
        ((toSheafify J (changeOfRingsPresheaf a X).presheaf).app V
          ((ModuleCat.extendRestrictScalarsAdj (a.hom.app V).hom).unit.app
            (X.val.obj V) x)) := by
  have he := congrArg ((eqToHom (s.extension_obj X).symm).val.app V)
    (s.ordinaryUnit X V x)
  have hi := congrArg (fun f ↦ f.val.app V
    ((s.ordinaryAdjunction.unit.app X).val.app V x))
    (eqToIso (s.extension_obj X)).hom_inv_id
  exact hi.symm.trans he

/-- The representative square for a prescribed scalar-derived pair.
Source: Stacks 07A4 (blueprint: lem-coef-prescribed-scalar-tensor-comparison). -/
def pairTensorNormalization
    (hE : ∀ (P : CochainComplex (scalarModules J R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
        CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
          ((scalarComplex s.extension s.extension_additive).obj P))
    (e : ∀ (P Q : CochainComplex (scalarModules J R) ℤ),
      (scalarComplex s.extension s.extension_additive).obj
          ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≅
        (coefficientTotalTensor.{r, c, v} J S).obj
          ((scalarComplex s.extension s.extension_additive).obj P,
           (scalarComplex s.extension s.extension_additive).obj Q))
    (μ : SR.tensor ⋙ s.derived ≅
      (s.derived.prod s.derived) ⋙ SS.tensor) : Prop :=
  ∀ (P Q : CochainComplex (scalarModules J R) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
    s.derived.map
        ((CoefficientTensorModels.iso.{r, c, v, w} J R SR TR
          P Q hp hq).hom) ≫
      μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        SS.tensor.map (Prod.mkHom
          (scalarPairComplexComparison s.extension s.extension_additive
            s.derived s.counit P)
          (scalarPairComplexComparison s.extension s.extension_additive
            s.derived s.counit Q)) =
      scalarPairComplexComparison s.extension s.extension_additive
          s.derived s.counit
            ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
        DerivedCategory.Q.map (e P Q).hom ≫
          (CoefficientTensorModels.iso.{r, c, v, w} J S SS TS
            _ _ (hE P hp) (hE Q hq)).hom

attribute [local irreducible] pairTensorNormalization

set_option backward.isDefEq.respectTransparency.types true in
/-- Strong scalar tensor comparison, retaining its actual pure-tensor normalization
before and after passage to the derived category.
Source: Stacks 07A4 and 0D6D
(blueprint: lem-coef-prescribed-scalar-tensor-comparison). -/
structure PairTensorComparison where
  /-- Scalar extension carries K-flat complexes to K-flat complexes. -/
  preservesKFlat : ∀ (P : CochainComplex (scalarModules J R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P →
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
        ((scalarComplex s.extension s.extension_additive).obj P)
  /-- The actual chain tensor comparison, with the differential signs retained. -/
  complexIso : ∀ (P Q : CochainComplex (scalarModules J R) ℤ),
    (scalarComplex s.extension s.extension_additive).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≅
      (coefficientTotalTensor.{r, c, v} J S).obj
        ((scalarComplex s.extension s.extension_additive).obj P,
         (scalarComplex s.extension s.extension_additive).obj Q)
  /-- It sends 1 tensor (x tensor y) to (1 tensor x) tensor (1 tensor y). -/
  generators : ∀ (P Q : CochainComplex (scalarModules J R) ℤ)
    (p q k : ℤ) (h : p + q = k) (V : Cᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
    ((complexIso P Q).hom.f k).val.app V
        (pairUnit.{c, v, r, w} a s _ V
          (coefficientTensorGenerator.{r, c, v} J R P Q p q k h V x y)) =
      coefficientTensorGenerator.{r, c, v} J S
        ((scalarComplex s.extension s.extension_additive).obj P)
        ((scalarComplex s.extension s.extension_additive).obj Q)
        p q k h V (pairUnit.{c, v, r, w} a s _ V x) (pairUnit.{c, v, r, w} a s _ V y)
  /-- The natural derived strong tensor comparison. -/
  iso : SR.tensor ⋙ s.derived ≅
    (s.derived.prod s.derived) ⋙ SS.tensor
  /-- Its defining square on the actual K-flat representatives. -/
  normalization : pairTensorNormalization.{c, v, r, w} a s SR SS TR TS preservesKFlat complexIso iso

attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local irreducible] monoidalCategory scalarPairComplexComparison
  CoefficientTensorModels.iso

private noncomputable def withScalarPair (M : ScalarHomModels.{c, v, r, w} J)
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) (s : ScalarDerivedPair a) :
    ScalarHomModels.{c, v, r, w} J := by
  classical
  let f : (p : Σ R : Sheaf J CommRingCat.{max c v r},
      Σ S : Sheaf J CommRingCat.{max c v r}, R ⟶ S) → ScalarDerivedPair p.2.2 :=
    fun p ↦ M.scalar p.2.2
  let f' := Function.update f ⟨R, S, a⟩ s
  exact { M with scalar := fun {R' S'} b ↦ f' ⟨R', S', b⟩ }

private theorem withScalarPair_scalar (M : ScalarHomModels.{c, v, r, w} J)
    {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) (s : ScalarDerivedPair a) :
    (withScalarPair (J := J) M a s).scalar a = s := by
  classical
  simp only [withScalarPair, Function.update_self]

/-- A normalized tensor comparison for any prescribed scalar-derived pair, using
simultaneous closed tensor models.
Source: Stacks 07A4, 07A6 and 0D6D
(blueprint: lem-coef-prescribed-scalar-tensor-comparison).
Proof: update the simultaneous scalar family at the given coefficient map, retaining
all closed structures and tensor models. Apply the existing scalar tensor comparison
to this family. At the updated map the scalar pair is the prescribed pair, so all
normalizations specialize literally to its functors, adjunction and universal counit. -/
theorem pairTensorComparison_from_models
    (M : ScalarHomModels.{c, v, r, w} J) :
    Nonempty (PairTensorComparison.{c, v, r, w} a s
      (M.closed R) (M.closed S) (M.model R) (M.model S)) := by
  classical
  let M' := withScalarPair (J := J) M a s
  have hs : M'.scalar a = s := withScalarPair_scalar (J := J) M a s
  rw [← hs]
  let t := (CategoryTheory.ScalarHomTensor.scalarHomTensorComparison_exists M' a).some
  refine ⟨{ preservesKFlat := t.preservesKFlat
            complexIso := t.complexIso
            generators := ?_
            iso := t.iso
            normalization := ?_ }⟩
  · exact t.generators
  · unfold pairTensorNormalization
    exact t.normalization

/-- Unit generators uniquely determine the scalar tensor comparison on complexes.
Source: Stacks 03EK and 07A4
(blueprint: lem-coef-prescribed-scalar-tensor-comparison).
Proof: transpose a component through the ordinary scalar adjunction. The resulting
maps out of the total tensor agree on every summand's pure tensors, hence agree.
The existing normalized comparison supplies existence. -/
theorem pairTensorIso_existsUnique
    (M : ScalarHomModels.{c, v, r, w} J)
    (P Q : CochainComplex (scalarModules J R) ℤ) :
    ∃! e : (scalarComplex s.extension s.extension_additive).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≅
      (coefficientTotalTensor.{r, c, v} J S).obj
        ((scalarComplex s.extension s.extension_additive).obj P,
          (scalarComplex s.extension s.extension_additive).obj Q),
      ∀ (p q k : ℤ) (h : p + q = k) (V : Cᵒᵖ)
        (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
        (e.hom.f k).val.app V
          (pairUnit.{c, v, r, w} a s _ V
            (coefficientTensorGenerator.{r, c, v} J R P Q p q k h V x y)) =
          coefficientTensorGenerator.{r, c, v} J S
            ((scalarComplex s.extension s.extension_additive).obj P)
            ((scalarComplex s.extension s.extension_additive).obj Q) p q k h V
            (pairUnit.{c, v, r, w} a s (P.X p) V x) (pairUnit.{c, v, r, w} a s (Q.X q) V y) := by
  obtain ⟨tc⟩ := pairTensorComparison_from_models.{c, v, r, w} a s M
  refine ⟨tc.complexIso P Q, tc.generators P Q, ?_⟩
  intro e he
  apply Iso.ext
  apply HomologicalComplex.Hom.ext
  funext k
  apply (s.ordinaryAdjunction.homEquiv _ _).injective
  dsimp only [Adjunction.homEquiv, Equiv.coe_fn_mk]
  change s.ordinaryAdjunction.unit.app _ ≫ (scalarRestriction a).map (e.hom.f k) =
    s.ordinaryAdjunction.unit.app _ ≫
      (scalarRestriction a).map ((tc.complexIso P Q).hom.f k)
  apply total_pure_hom_ext.{c, v, r}
  intro p q h V x y
  change (e.hom.f k).val.app V
      (pairUnit.{c, v, r, w} a s _ V (coefficientTensorGenerator.{r, c, v} J R P Q p q k h V x y)) =
    ((tc.complexIso P Q).hom.f k).val.app V
      (pairUnit.{c, v, r, w} a s _ V (coefficientTensorGenerator.{r, c, v} J R P Q p q k h V x y))
  exact (he p q k h V x y).trans ((tc.generators P Q p q k h V x y).symm)

/-- Ordinary tensor evaluation depends on the prescribed ordinary functor and adjunction.
Source: Stacks 03CZ and 07A4 (blueprint: lem-coef-prescribed-scalar-tensor-comparison).
Proof: identify the extension functors and their ordinary adjunctions, then apply
pairTensorIso_existsUnique. The derived presentation does not enter the generator formula. -/
theorem pairTensorIso_existsUnique_with_ordinary
    (M : ScalarHomModels.{c, v, r, w} J)
    (E : scalarModules J R ⥤ scalarModules J S) [E.Additive]
    (am : E ⊣ scalarRestriction a) (he : s.extension = E)
    (ha : HEq s.ordinaryAdjunction am)
    (P Q : CochainComplex (scalarModules J R) ℤ) :
    ∃! e : (E.mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≅
      (coefficientTotalTensor.{r, c, v} J S).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj P,
          (E.mapHomologicalComplex (.up ℤ)).obj Q),
      ∀ (p q k : ℤ) (h : p + q = k) (V : Cᵒᵖ)
        (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
        (e.hom.f k).val.app V
          ((am.unit.app _).val.app V
            (coefficientTensorGenerator.{r, c, v} J R P Q p q k h V x y)) =
          coefficientTensorGenerator.{r, c, v} J S
            ((E.mapHomologicalComplex (.up ℤ)).obj P)
            ((E.mapHomologicalComplex (.up ℤ)).obj Q) p q k h V
            ((am.unit.app (P.X p)).val.app V x)
            ((am.unit.app (Q.X q)).val.app V y) := by
  subst E
  have ha' : s.ordinaryAdjunction = am := eq_of_heq ha
  subst am
  exact pairTensorIso_existsUnique.{c, v, r, w} a s M P Q

/-- K-flat preservation is unchanged when the scalar extension is given explicitly.
Source: Stacks 07A4 (blueprint: lem-coef-prescribed-scalar-tensor-comparison).
Proof: identify the ordinary extension functors and apply scalarExtension_preservesKFlat. -/
theorem pair_preservesKFlat_with_extension
    (E : scalarModules J R ⥤ scalarModules J S) [E.Additive]
    (he : s.extension = E) (P : CochainComplex (scalarModules J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P) :
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
      ((E.mapHomologicalComplex (.up ℤ)).obj P) := by
  subst E
  exact SheafOfModules.scalarExtension_preservesKFlat a s P hP

end CategoryTheory.ScalarHomTensor
