/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
public import WeilConjectures.Compactification.RefinementCategory

/-! # Strict ordinary étale system interfaces

Source: Zheng, Construction 4.1, Constructions 5.14--5.15 and Lemma 5.16
(blueprint: def-per-strict-etale-system-interfaces).

These declarations are relocated, with their original names and data, from the
adjoint theorem module. No existence theorem is needed to import these notions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
open SheafOfModules
/-- Reuse the existing ring-sheafification witness once at the concrete etale-site size.
This instance only caches an existing proof, so the constant sheaf construction is unchanged.
Source: Stacks Tag 00W1; Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
instance (priority := 2000) strictEtaleCommRingSheafify (T : Scheme.{u}) :
    HasWeakSheafify T.smallEtaleTopology CommRingCat.{u + 1} := inferInstance
/-- Reuse the existing additive-sheafification witness at the ordinary etale-site size.
Source: Stacks Tag 00W1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
instance (priority := 2000) strictEtaleAddCommGrpSheafify (T : Scheme.{u}) :
    HasSheafify T.smallEtaleTopology AddCommGrpCat.{u + 1} := inferInstance
/-- Reuse the existing local-bijection characterization for additive sheaves.
Source: Stacks Tag 00W1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
instance (priority := 2000) strictEtaleAddCommGrpLocal (T : Scheme.{u}) :
    T.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} := inferInstance
/-- Reuse the existing forgetful composition witness for constant coefficient rings.
Source: Stacks Tag 03D7
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
instance (priority := 2000) strictEtaleRingCompose (T : Scheme.{u}) :
    T.smallEtaleTopology.HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := inferInstance
/-- Cache the existing set-sheafification witness at the concrete etale-site size.
Source: Stacks Tag 00W1; Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
instance (priority := 2000) strictEtaleTypeSheafify (T : Scheme.{u}) :
    HasWeakSheafify T.smallEtaleTopology (Type (u + 1)) := inferInstance
/-- Cache the existing ring-to-set sheaf composition witness.
Source: Stacks Tag 03D7; Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
instance (priority := 2000) strictEtaleRingSetCompose (T : Scheme.{u}) :
    T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget CommRingCat.{u + 1}) :=
  inferInstance
/-- Cache the existing additive-to-set sheaf composition witness.
Source: Stacks Tag 03D7; Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
instance (priority := 2000) strictEtaleAddCommGrpSetCompose (T : Scheme.{u}) :
    T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  inferInstance
/-- The recorded strict system category on the ordinary étale site.
Source: Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev strictEtaleCoefficientSystem (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O) :=
  CoefficientSystem (J := T.smallEtaleTopology) O ell
/-- The recorded coefficient-level category, with positive exponent `n+1`.
Source: Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev strictEtaleLevel (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O) (n : ℕ) :=
  coefficientLevelModules (J := T.smallEtaleTopology) O ell n
/-- Use Mathlib's standard localization for the strict system category.
Source: Zheng, Construction 4.1; Stacks Tag 05RU
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
@[irreducible]
instance (priority := 100) strictEtaleSystemDerived (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O) :
    HasDerivedCategory.{u + 2} (strictEtaleCoefficientSystem T O ell) :=
  HasDerivedCategory.standard _
/-- Use the same standard localization at every finite coefficient level.
Source: Zheng, Construction 4.1; Stacks Tag 05RU
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
@[irreducible]
instance (priority := 100) strictEtaleLevelDerived (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O) (n : ℕ) :
    HasDerivedCategory.{u + 2} (strictEtaleLevel T O ell n) :=
  HasDerivedCategory.standard _
/-- Specialize the existing levelwise additive witness before elaborating projections
of the evaluation package. No additive structure is changed.
Source: Zheng, Construction 4.1
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
instance (priority := 3000) strictEtaleEvaluationAdditive
    (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O] (ell : O) :
    ∀ n, (coefficientEvaluation.{u + 1, u, u + 1}
      (J := T.smallEtaleTopology) (O := O) (ell := ell) n).Additive :=
  fun n ↦ coefficientEvaluation_additive.{u + 1, u, u + 1} n
/-- The recorded derived evaluation interface at the ordinary etale-site sizes.
Source: Zheng, Construction 4.1 and Lemma 4.10
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleEvaluation (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O] (ell : O) :=
  CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2}
    (J := T.smallEtaleTopology) (O := O) (ell := ell)
/-- The actual set-sheaf adjunction along base change.
Source: Zheng, Constructions 4.1 and 5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev strictEtaleSetAdjunction {T S : Scheme.{u}} (g : T ⟶ S) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
    (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale)
/-- The canonical geometric lift already specified by the system-comparison node.
Source: Zheng, Constructions 4.1 and 5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleOrdinaryImage (O : Type (u + 1)) [CommRing O] (ell : O)
    {T S : Scheme.{u}} (g : T ⟶ S) :=
  CoefficientSystemOrdinaryImage (J := S.smallEtaleTopology) (K := T.smallEtaleTopology)
    O ell (Scheme.etaleSetPullback g)
    ((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
      (Type (u + 1)) (S.smallGrothendieckTopology @Etale) (T.smallGrothendieckTopology @Etale))
    (strictEtaleSetAdjunction g)

/-- Multiplication by a coefficient on strict and derived systems. Its normalization
is the actual constant-ring sheafification unit and its localization on complexes.
Together with additivity, preservation of this action means `O`-linearity on all Homs.
Source: Zheng, the Brown adjoint after Lemma 5.16
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleScalarActionCoherence (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O)
    (ordinary : O → (𝟭 (strictEtaleCoefficientSystem T O ell) ⟶ 𝟭 _))
    (derived : O → (𝟭 (DerivedCategory (strictEtaleCoefficientSystem T O ell)) ⟶ 𝟭 _)) : Prop :=
    -- ordinaryNormalized
    (∀ r M n (U : T.Etaleᵒᵖ) (x : (M.level n).val.obj U),
      (((ordinary r).app M).app n).val.app U x =
        ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (CommRingCat.of (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))))).app U
            (Ideal.Quotient.mk _ r)) • x) ∧
    -- representative
    (∀ r K,
      (derived r).app (DerivedCategory.Q.obj K) =
        DerivedCategory.Q.map
          (((ordinary r).mapHomologicalComplex (.up ℤ)).app K))

/-- The coherence predicate for `StrictEtaleScalarAction`, separated from its data to share
its type during kernel checking. It is exactly the displayed canonical diagram equations.
Source: Zheng, Construction 4.1, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleScalarAction (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O) :=
  { record : (O → (𝟭 (strictEtaleCoefficientSystem T O ell) ⟶ 𝟭 _)) ×
      (O → (𝟭 (DerivedCategory (strictEtaleCoefficientSystem T O ell)) ⟶ 𝟭 _)) //
    StrictEtaleScalarActionCoherence T O ell record.1 record.2 }

section
variable (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (ell : O)
variable {T O ell}

/-- The specified component of `StrictEtaleScalarAction`.
Source: Zheng, Construction 4.1, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleScalarAction.derived (record : StrictEtaleScalarAction T O ell) :
    O → (𝟭 (DerivedCategory (strictEtaleCoefficientSystem T O ell)) ⟶ 𝟭 _) :=
  record.val.2

end

section FixedCoefficients
variable (O : Type (u + 1)) [CommRing O] (ell : O)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
/-- The termwise open extension and proper direct image, with universal derived images.
The open functor is fixed as the left adjoint of the canonical geometric inverse image.
The equations on ordinary evaluations and Hom transposes fix the system functor and all
its transition maps. The proper derived functor uses the universal K-injective interface.
Source: Zheng, Constructions 5.14--5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
structure StrictEtaleCompactSupportData where
  PX : StrictEtaleEvaluation X O ell
  PY : StrictEtaleEvaluation Y O ell
  PZ : StrictEtaleEvaluation c.Z O ell
  openImage : StrictEtaleOrdinaryImage O ell c.i
  properImage : StrictEtaleOrdinaryImage O ell c.g
  properDerived : CoefficientSystemDerivedImage (J := Y.smallEtaleTopology)
    (K := c.Z.smallEtaleTopology) O ell _ _ _ properImage PY PZ
  openExtension : strictEtaleCoefficientSystem X O ell ⥤
    strictEtaleCoefficientSystem c.Z O ell
  [openAdditive : openExtension.Additive]
  openAdjunction : openExtension ⊣ openImage.inverse
  levelOpen : ∀ n, strictEtaleLevel X O ell n ⥤ strictEtaleLevel c.Z O ell n
  [levelOpenAdditive : ∀ n, (levelOpen n).Additive]
  levelOpenAdjunction : ∀ n, levelOpen n ⊣ (openImage.lift n).modules
  openEvaluation : ∀ n, openExtension ⋙ coefficientEvaluation
    (J := c.Z.smallEtaleTopology) (O := O) (ell := ell) n ≅
    coefficientEvaluation (J := X.smallEtaleTopology) (O := O) (ell := ell) n ⋙ levelOpen n
  derivedOpen : DerivedCategory (strictEtaleCoefficientSystem X O ell) ⥤
    DerivedCategory (strictEtaleCoefficientSystem c.Z O ell)
  openDerived : CoefficientSystemDerivedImage (J := c.Z.smallEtaleTopology)
    (K := X.smallEtaleTopology) O ell _ _ _ openImage PZ PX
  derivedOpenAdjunction : derivedOpen ⊣ openDerived.system.inverse
  openFactors : DerivedCategory.Q ⋙ derivedOpen ≅
    openExtension.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  levelDerivedOpen : ∀ n, DerivedCategory (strictEtaleLevel X O ell n) ⥤
    DerivedCategory (strictEtaleLevel c.Z O ell n)
  levelDerivedOpenAdjunction : ∀ n, levelDerivedOpen n ⊣ (openDerived.level n).inverse
  levelOpenFactors : ∀ n, DerivedCategory.Q ⋙ levelDerivedOpen n ≅
    (levelOpen n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  openDerivedEvaluation : ∀ n, derivedOpen ⋙ PZ.evaluation n ≅
    PX.evaluation n ⋙ levelDerivedOpen n

attribute [instance] StrictEtaleCompactSupportData.openAdditive
  StrictEtaleCompactSupportData.levelOpenAdditive

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCompactSupportCoherence
    (record : StrictEtaleCompactSupportData O ell c) : Prop :=
    -- openExact
    (PreservesFiniteLimits record.openExtension ∧ PreservesFiniteColimits record.openExtension) ∧
    -- openTranspose
    (∀ n, (record.openImage.inverseEvaluation n).hom =
      (mateEquiv record.openAdjunction (record.levelOpenAdjunction n)
        (.mk _ _ _ _ (record.openEvaluation n).inv))) ∧
    -- derivedOpenTranspose
    (∀ P K
      (h : (record.openExtension.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      record.derivedOpenAdjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
        (record.openFactors.hom.app P ≫ DerivedCategory.Q.map h) =
      DerivedCategory.Q.map ((record.openAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P K h) ≫
        record.openDerived.system.inverseFactors.inv.app K) ∧
    -- levelDerivedOpenTranspose
    (∀ n P K
      (h : ((record.levelOpen n).mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      (record.levelDerivedOpenAdjunction n).homEquiv
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
        ((record.levelOpenFactors n).hom.app P ≫ DerivedCategory.Q.map h) =
      DerivedCategory.Q.map
        (((record.levelOpenAdjunction n).mapHomologicalComplex (.up ℤ)).homEquiv P K h) ≫
          (record.openDerived.level n).inverseFactors.inv.app K) ∧
    -- openDerivedEvaluation_rep
    (∀ n K,
      (record.openDerivedEvaluation n).hom.app (DerivedCategory.Q.obj K) ≫
        (record.levelDerivedOpen n).map ((record.PX.evaluationFactors n).hom.app K) ≫
        (record.levelOpenFactors n).hom.app
          (((coefficientEvaluation (J := X.smallEtaleTopology)
            (O := O) (ell := ell) n).mapHomologicalComplex (.up ℤ)).obj K) =
      (record.PZ.evaluation n).map (record.openFactors.hom.app K) ≫
        (record.PZ.evaluationFactors n).hom.app
          ((record.openExtension.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (record.openEvaluation n) (.up ℤ)).hom.app K))

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCompactSupport :=
  { record : StrictEtaleCompactSupportData O ell c //
    StrictEtaleCompactSupportCoherence O ell c record }

section
variable {O ell c}

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.PX (record : StrictEtaleCompactSupport O ell c) :=
  record.val.PX

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.PY (record : StrictEtaleCompactSupport O ell c) :=
  record.val.PY

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.PZ (record : StrictEtaleCompactSupport O ell c) :=
  record.val.PZ

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.openImage (record : StrictEtaleCompactSupport O ell c) :=
  record.val.openImage

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.properImage (record : StrictEtaleCompactSupport O ell c) :=
  record.val.properImage

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.properDerived (record : StrictEtaleCompactSupport O ell c) :=
  record.val.properDerived

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.derivedOpen (record : StrictEtaleCompactSupport O ell c) :=
  record.val.derivedOpen

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.openDerived (record : StrictEtaleCompactSupport O ell c) :=
  record.val.openDerived

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.derivedOpenAdjunction
    (record : StrictEtaleCompactSupport O ell c) :=
  record.val.derivedOpenAdjunction

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.levelDerivedOpen (record : StrictEtaleCompactSupport O ell c) :=
  record.val.levelDerivedOpen

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.levelDerivedOpenAdjunction
    (record : StrictEtaleCompactSupport O ell c) :=
  record.val.levelDerivedOpenAdjunction

/-- The specified data and canonical coherence of `StrictEtaleCompactSupport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleCompactSupport.openDerivedEvaluation
    (record : StrictEtaleCompactSupport O ell c) :=
  record.val.openDerivedEvaluation

end

variable {O ell c}
/-- `Rp_* j_!`, as a composite of the specified actual derived functors.
Source: Zheng, Construction 5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCompactSupport.functor (S : StrictEtaleCompactSupport O ell c) :=
  S.derivedOpen ⋙ S.properDerived.system.direct
/-- The ordinary finite-level compact-support functor in the constant-ring encoding.
Source: Zheng, Construction 5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCompactSupport.levelFunctor (S : StrictEtaleCompactSupport O ell c) (n : ℕ) :=
  S.levelDerivedOpen n ⋙ (S.properDerived.level n).direct
/-- The canonical evaluated compact-support comparison, constructed from the open and
proper comparisons, rather than selected as an unspecified isomorphism.
Source: Zheng, Lemma 5.16
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleCompactSupport.evaluation (S : StrictEtaleCompactSupport O ell c) (n : ℕ) :
    S.functor ⋙ S.PY.evaluation n ≅ S.PX.evaluation n ⋙ S.levelFunctor n :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (S.properDerived.directEvaluation n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (S.openDerivedEvaluation n) _ ≪≫ Functor.associator _ _ _

end FixedCoefficients
end AlgebraicGeometry
