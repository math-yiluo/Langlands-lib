/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.NumberTheory.Padics.PadicIntegersIntegralClosure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Basis
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.Etale.EtaleExceptionalConstantTensor
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemBrownConstruction
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemEvaluationBound
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSystemQuotientNormalization
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
public import WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientTransportInterfaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleIsomorphicStageProjection
import WeilConjectures.NumberTheory.Padics.LocalFieldCoefficientStages
import WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreeExtensionLeftExact
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleExactCoefficientTransport
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleFiniteFreeProjectionAssembly
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleFiniteFreeMateAtLevel
/-!
# The strict étale coefficient-system adjoint
Source: Zheng, Six Operations and Lefschetz--Verdier, Constructions 5.14--5.15,
Lemmas 5.16 and 5.22, and Proposition 5.24 (blueprint:
lem-pur-etale-coefficient-system-adjoint).
The structure records the actual compact-support system functor, its right adjoint,
the finite-level adjunctions, and the asserted coefficient-system coherences.
* `StrictEtaleCompactSupport` specifies the ordinary and unbounded derived functors.
* `StrictEtaleExceptionalAdjoint` records the exact linear adjoint and finite-level mates.
* `StrictEtaleExceptionalTransport` specifies the scalar and cofinal comparison maps.
* `etaleCoefficientSystemAdjoint` and its scalar/cofinal companions assert existence.
* The identity/composition theorems state coherence with canonical tensor identifications.
This core module holds the exceptional-adjoint and transport records, the integer-ring
and coefficient-change definitions, the scalar transport projection
`strictEtaleScalarTransportProjection` (blueprint: lem-pur-etale-scalar-transport-projection)
and the identity/composition theorems;
`WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientSystemAdjoint` re-exports
it and proves the existence theorems (split for the per-file compile limit).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async true
set_option linter.all false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
open SheafOfModules
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local irreducible] CategoryTheory.constantSheaf SheafOfModules.siteCoefficientTensor
  SheafOfModules.siteCoefficientTensorAdj
set_option backward.defeqAttrib.useBackward true
/-- Use the recorded proper inverse-image additive witness at the strict site sizes.
Source: Zheng, Construction 4.1 and Construction 5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
theorem strictEtaleProperInverseAdditive
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : StrictEtaleCompactSupport O ell c) (n : ℕ) :
    (S.val.properImage.lift n).modules.Additive := S.val.properImage.inverseAdditive n

/-- Use the recorded proper direct-image additive witness at the strict site sizes.
Source: Zheng, Construction 4.1 and Construction 5.15
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
theorem strictEtaleProperDirectAdditive
    {O : Type (u + 1)} [CommRing O] {ell : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : StrictEtaleCompactSupport O ell c) (n : ℕ) :
    (S.val.properImage.right n).Additive := S.val.properImage.rightAdditive n

attribute [local instance 9000] strictEtaleProperInverseAdditive strictEtaleProperDirectAdditive

section TransportTypes
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] SheafOfModules.coefficientQuotientSheaf
  SheafOfModules.coefficientQuotientMap CategoryTheory.sheafCompose
section FixedCoefficients
variable (O : Type (u + 1)) [CommRing O] (ell : O)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
/-- The right adjoint with actual evaluated units, counits, and transition mates.
The isomorphisms are uniquely characterized by the two adjunction equations. Quotient
coefficient maps use the recorded universal derived tensor, including nonflat quotients.
Source: Zheng, Lemmas 5.16 and 5.22, Proposition 5.24, and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
structure StrictEtaleExceptionalAdjointData (S : StrictEtaleCompactSupport O ell c) where
  right : DerivedCategory (strictEtaleCoefficientSystem Y O ell) ⥤
    DerivedCategory (strictEtaleCoefficientSystem X O ell)
  [rightAdditive : right.Additive]
  [shift : right.CommShift ℤ]
  adjunction : S.functor ⊣ right
  scalarX : StrictEtaleScalarAction X O ell
  scalarY : StrictEtaleScalarAction Y O ell
  levelRight : ∀ n, DerivedCategory (strictEtaleLevel Y O ell n) ⥤
    DerivedCategory (strictEtaleLevel X O ell n)
  levelAdjunction : ∀ n, S.levelFunctor n ⊣ levelRight n
  evaluation : ∀ n, right ⋙ S.PX.evaluation n ≅ S.PY.evaluation n ⋙ levelRight n
  quotientOpen : ∀ {m n : ℕ} (h : n ≤ m),
    (S.PX.scalar h).derived ⋙ S.levelDerivedOpen n ≅
      S.levelDerivedOpen m ⋙ (S.PZ.scalar h).derived
  quotientProper : ∀ {m n : ℕ} (h : n ≤ m),
    (S.PZ.scalar h).derived ⋙ (S.properDerived.level n).direct ≅
      (S.properDerived.level m).direct ⋙ (S.PY.scalar h).derived
  quotientProjection : ∀ {m n : ℕ} (h : n ≤ m),
    (S.PX.scalar h).derived ⋙ S.levelFunctor n ≅
      S.levelFunctor m ⋙ (S.PY.scalar h).derived
  quotientComparison : ∀ {m n : ℕ} (h : n ≤ m),
    levelRight m ⋙ (S.PX.scalar h).derived ≅
      (S.PY.scalar h).derived ⋙ levelRight n

attribute [instance] StrictEtaleExceptionalAdjointData.rightAdditive
  StrictEtaleExceptionalAdjointData.shift

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleExceptionalAdjointCoherence (S : StrictEtaleCompactSupport O ell c)
    (record : StrictEtaleExceptionalAdjointData O ell c S) : Prop :=
    -- exact
    (record.right.IsTriangulated) ∧
    -- linear
    (∀ r M, record.right.map ((record.scalarY.derived r).app M) =
      (record.scalarX.derived r).app (record.right.obj M)) ∧
    -- counit
    (∀ n, (record.evaluation n).hom =
      (mateEquiv record.adjunction (record.levelAdjunction n)
        (.mk _ _ _ _ (S.evaluation n).inv)).natTrans) ∧
    -- quotientOpenMate
    (∀ {m n : ℕ} (h : n ≤ m),
      (mateEquiv (S.levelDerivedOpenAdjunction m) (S.levelDerivedOpenAdjunction n)
        (.mk _ _ _ _ (record.quotientOpen h).hom)).natTrans =
      (S.openDerived.derivedTensor h).inv) ∧
    -- quotientProperMate
    (∀ {m n : ℕ} (h : n ≤ m),
      (record.quotientProper h).inv =
      (mateEquiv (S.properDerived.level m).adjunction (S.properDerived.level n).adjunction
        (.mk _ _ _ _ (S.properDerived.derivedTensor h).hom)).natTrans) ∧
    -- quotientProjection_def
    (∀ {m n : ℕ} (h : n ≤ m), record.quotientProjection h =
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (record.quotientOpen h) _ ≪≫
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (record.quotientProper h) ≪≫
          (Functor.associator _ _ _).symm) ∧
    -- quotientMate
    (∀ {m n : ℕ} (h : n ≤ m),
      (record.quotientComparison h).hom =
      (mateEquiv (record.levelAdjunction m) (record.levelAdjunction n)
        (.mk _ _ _ _ (record.quotientProjection h).hom)).natTrans) ∧
    -- quotientIdentity
    (∀ n M,
      (record.quotientComparison (Nat.le_refl n)).hom.app M ≫
        (record.levelRight n).map ((S.PY.derivedUnit n).hom.app M) =
      (S.PX.derivedUnit n).hom.app ((record.levelRight n).obj M)) ∧
    -- quotientComposition
    (∀ {l m n : ℕ} (h₁ : m ≤ l) (h₂ : n ≤ m) M,
      (S.PX.derivedAssoc h₁ h₂).hom.app ((record.levelRight l).obj M) ≫
        (record.quotientComparison (h₂.trans h₁)).hom.app M =
      (S.PX.scalar h₂).derived.map ((record.quotientComparison h₁).hom.app M) ≫
        (record.quotientComparison h₂).hom.app ((S.PY.scalar h₁).derived.obj M) ≫
        (record.levelRight n).map ((S.PY.derivedAssoc h₁ h₂).hom.app M)) ∧
    -- transition
    (∀ {m n : ℕ} (h : n ≤ m) M,
      (S.PX.scalar h).derived.map ((record.evaluation m).hom.app M) ≫
        (record.quotientComparison h).hom.app ((S.PY.evaluation m).obj M) ≫
        (record.levelRight n).map
          (((S.PY.scalar h).derivedAdj.homEquiv _ _).symm ((S.PY.transition h).app M)) =
      ((S.PX.scalar h).derivedAdj.homEquiv _ _).symm
        ((S.PX.transition h).app (record.right.obj M)) ≫ (record.evaluation n).hom.app M) ∧
    -- bound
    (∃ c_f : ℕ, ∀ (a : ℤ) M, M.IsGE a → (record.right.obj M).IsGE (a - c_f)) ∧
    -- normalized
    (∀ M, (∃ a : ℤ, M.IsGE a) →
      IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
        (J := Y.smallEtaleTopology) O ell S.PY M →
        (∃ a : ℤ, (record.right.obj M).IsGE a) ∧
          IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
            (J := X.smallEtaleTopology) O ell S.PX (record.right.obj M))

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleExceptionalAdjoint (S : StrictEtaleCompactSupport O ell c) :=
  { record : StrictEtaleExceptionalAdjointData O ell c S //
    StrictEtaleExceptionalAdjointCoherence O ell c S record }

section
variable (S : StrictEtaleCompactSupport O ell c)
variable {O ell c S}

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.right (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  record.val.right

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.adjunction
    (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  record.val.adjunction

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.levelRight
    (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  record.val.levelRight

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.levelAdjunction
    (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  record.val.levelAdjunction

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.evaluation
    (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  record.val.evaluation

/-- The specified data and canonical coherence of `StrictEtaleExceptionalAdjoint`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalAdjoint.quotientComparison
    (record : StrictEtaleExceptionalAdjoint O ell c S) :=
  fun {m n : ℕ} (h : n ≤ m) ↦ record.val.quotientComparison h

end

end FixedCoefficients
section Transport
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
  {phi : O →+* O'} {index : ℕ →o ℕ}
  (a : StrictEtaleCoefficientChange O O' ell mu phi index)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  (SA : StrictEtaleCompactSupport O ell c) (SB : StrictEtaleCompactSupport O' mu c)
  (TX : StrictEtaleCoefficientTransport a X SA.PX SB.PX)
  (TY : StrictEtaleCoefficientTransport a Y SA.PY SB.PY)
  (TZ : StrictEtaleCoefficientTransport a c.Z SA.PZ SB.PZ)
variable (GA : StrictEtaleExceptionalAdjoint O ell c SA)
  (GB : StrictEtaleExceptionalAdjoint O' mu c SB)
/-- The actual exceptional coefficient comparison. Its transpose is the inverse
compact-support projection followed by the extended counit. Evaluations identify it
with the identical finite-level transpose, including every quotient transition.
Source: Zheng, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
structure StrictEtaleExceptionalTransportData where
  compact : StrictEtaleCompactSupportTransport a c SA SB TX TY TZ
  right : GA.right ⋙ TX.derived ≅ TY.derived ⋙ GB.right
  levelProjection : ∀ n, SA.levelFunctor (index n) ⋙ (TY.level n).derived ≅
    (TX.level n).derived ⋙ SB.levelFunctor n
  levelRight : ∀ n, GA.levelRight (index n) ⋙ (TX.level n).derived ≅
    (TY.level n).derived ⋙ GB.levelRight n
  quotientX : StrictEtaleTransportQuotient TX
  quotientY : StrictEtaleTransportQuotient TY

/-- The specified data and canonical coherence of `StrictEtaleExceptionalTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleExceptionalTransportCoherence
    (record : StrictEtaleExceptionalTransportData a c SA SB TX TY TZ GA GB) : Prop :=
    -- mate
    (record.right.hom = (mateEquiv GA.adjunction GB.adjunction
      (.mk _ _ _ _ record.compact.projection.inv)).natTrans) ∧
    -- projectionEvaluation
    (∀ n K,
      (TY.derivedEvaluation n).hom.app (SA.functor.obj K) ≫
        (TY.level n).derived.map ((SA.evaluation (index n)).hom.app K) ≫
        (record.levelProjection n).hom.app ((SA.PX.evaluation (index n)).obj K) =
      (SB.PY.evaluation n).map (record.compact.projection.hom.app K) ≫
        (SB.evaluation n).hom.app (TX.derived.obj K) ≫
        (SB.levelFunctor n).map ((TX.derivedEvaluation n).hom.app K)) ∧
    -- levelMate
    (∀ n, (record.levelRight n).hom =
      (mateEquiv (GA.levelAdjunction (index n)) (GB.levelAdjunction n)
        (.mk _ _ _ _ (record.levelProjection n).inv)).natTrans) ∧
    -- quotient
    (∀ {m n : ℕ} (h : n ≤ m) M,
      (SB.PX.scalar h).derived.map ((record.levelRight m).hom.app M) ≫
        (GB.quotientComparison h).hom.app ((TY.level m).derived.obj M) ≫
        (GB.levelRight n).map ((record.quotientY.derived h).inv.app M) =
      (record.quotientX.derived h).inv.app ((GA.levelRight (index m)).obj M) ≫
        (TX.level n).derived.map ((GA.quotientComparison (index.monotone h)).hom.app M) ≫
        (record.levelRight n).hom.app ((SA.PY.scalar (index.monotone h)).derived.obj M)) ∧
    -- rightEvaluation
    (∀ n M,
      (TX.derivedEvaluation n).hom.app (GA.right.obj M) ≫
        (TX.level n).derived.map ((GA.evaluation (index n)).hom.app M) ≫
        (record.levelRight n).hom.app ((SA.PY.evaluation (index n)).obj M) =
      (SB.PX.evaluation n).map (record.right.hom.app M) ≫
        (GB.evaluation n).hom.app (TY.derived.obj M) ≫
        (GB.levelRight n).map ((TY.derivedEvaluation n).hom.app M))

/-- The specified data and canonical coherence of `StrictEtaleExceptionalTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def StrictEtaleExceptionalTransport :=
  { record : StrictEtaleExceptionalTransportData a c SA SB TX TY TZ GA GB //
    StrictEtaleExceptionalTransportCoherence a c SA SB TX TY TZ GA GB record }

section
variable {a c SA SB TX TY TZ GA GB}

/-- The specified data and canonical coherence of `StrictEtaleExceptionalTransport`.
Source: Zheng, Construction 4.1, Construction 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
abbrev StrictEtaleExceptionalTransport.right
    (record : StrictEtaleExceptionalTransport a c SA SB TX TY TZ GA GB) :=
  record.val.right

end

end Transport
end TransportTypes
section EfficientRealization
set_option backward.isDefEq.respectTransparency.types true
section IntegerMaps
variable (l : ℕ) [Fact l.Prime]
  {E F : Type (u + 1)} [Field E] [Field F]
  [Algebra (Padic l) E] [Algebra (Padic l) F]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
/-- A finite p-adic field embedding preserves the recorded integer rings.
Source: Zheng, coefficient change in Proposition 2.29(2); Serre, Local Fields II.2
(blueprint: lem-pur-etale-coefficient-system-adjoint).
Proof: uniqueness of the extending absolute value identifies the two absolute values
on E. The integer rings are their unit balls, so the embedding preserves membership. -/
theorem strictEtaleIntegerMap_mem (i : E →ₐ[Padic l] F)
    (x : Padic.coefficientExtensionIntegers l E) :
    i (x : E) ∈ Padic.coefficientExtensionIntegers l F := by
  have hE := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hF := (Padic.coefficientExtensionIntegers_dvr l F).choose_spec
  apply (hF.1 _).mpr
  change spectralNorm (Padic l) F (i (x : E)) ≤ 1
  have hmap : spectralNorm (Padic l) F (i (x : E)) =
      spectralNorm (Padic l) E (x : E) := by
    unfold spectralNorm
    rw [minpoly.algHom_eq i i.injective]
  rw [hmap]
  exact (hE.1 _).mp x.property
/-- Restrict the actual field embedding to the integer rings.
Source: Zheng, Proposition 2.29(2); Serre, Local Fields II.2
(blueprint: lem-pur-etale-coefficient-system-adjoint). -/
def strictEtaleIntegerMap (i : E →ₐ[Padic l] F) :
    Padic.coefficientExtensionIntegers l E →+* Padic.coefficientExtensionIntegers l F :=
  (i.toRingHom.comp (Padic.coefficientExtensionIntegers l E).subtype).codRestrict
    (Padic.coefficientExtensionIntegers l F) (strictEtaleIntegerMap_mem l i)
end IntegerMaps
end EfficientRealization

section ScalarTargetAssembly
private def brownConstantUnderlying (T : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    Etale.SystemProjection.constantModule T A ⋙
      sheafCompose T.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} A)
        AddCommGrpCat.{u + 1}) ≅
      SheafOfModules.toSheaf.{u + 1} ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj A)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by ext U x; rfl)

private theorem brownConstant_exact (T : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    PreservesFiniteLimits (Etale.SystemProjection.constantModule T A) ∧
      PreservesFiniteColimits (Etale.SystemProjection.constantModule T A) := by
  let F := Etale.SystemProjection.constantModule T A
  let V := sheafCompose T.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
  have : PreservesFiniteLimits (F ⋙ V) :=
    preservesFiniteLimits_of_natIso (brownConstantUnderlying T A).symm
  have : PreservesFiniteColimits (F ⋙ V) :=
    preservesFiniteColimits_of_natIso (brownConstantUnderlying T A).symm
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F V,
    preservesFiniteColimits_of_reflects_of_preserves F V⟩

private theorem brownConstant_faithful (T : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    (Etale.SystemProjection.constantModule T A).Faithful where
  map_injective {M N} {f g} h := by
    ext U x
    exact congrArg (fun k ↦ k.hom.app U x) h

private theorem brownRealization_isLE_iff
    {O : Type (u + 1)} [CommRing O] {t : O} {T : Scheme.{u}}
    {P : StrictEtaleEvaluation T O t} (R : StrictEtaleBrownRealization O t T P)
    (n : ℕ) (K : DerivedCategory (strictEtaleLevel T O t n)) (b : ℤ) :
    ((R.derived n).obj K).IsLE b ↔ K.IsLE b := by
  let := strictEtaleLevelDerived T O t n
  let F : strictEtaleLevel T O t n ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) :=
    strictEtaleBrownConstant O t T n
  have : F.Additive := R.val.ordinaryAdditive n
  have : PreservesFiniteLimits F :=
    (brownConstant_exact T (.of (strictEtaleBrownRing O t n))).1
  have : PreservesFiniteColimits F :=
    (brownConstant_exact T (.of (strictEtaleBrownRing O t n))).2
  have : F.Faithful := brownConstant_faithful T (.of (strictEtaleBrownRing O t n))
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (strictEtaleLevel T O t n) (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) (R.derived n) := ⟨R.factors n⟩
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (strictEtaleLevel T O t n) (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors⟩
  let e : R.derived n ≅ F.mapDerivedCategory := Localization.liftNatIso
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (R.derived n) F.mapDerivedCategory (Iso.refl _)
  constructor
  · intro h
    have := h
    have hm := DerivedCategory.TStructure.t.isLE_of_iso (e.app K) b
    apply (DerivedCategory.isLE_iff K b).mpr
    intro i hi
    exact F.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
      ((DerivedCategory.isLE_iff _ b).mp hm i hi)
  · intro h
    have := h
    have := F.isLE_mapDerivedCategory_obj K b
    exact DerivedCategory.TStructure.t.isLE_of_iso (e.app K).symm b

private theorem brownFiniteAmplitude
    (k : Type u) [Field k] [IsAlgClosed k] (p l : ℕ) [Fact p.Prime] [Fact l.Prime]
    [CharP k p] (hl : l ≠ p)
    {X Y : Scheme.{u}} (xk : X ⟶ Spec (.of k)) (yk : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType xk] [LocallyOfFiniteType yk]
    [QuasiCompact xk] [QuasiCompact yk]
    (f : X ⟶ Y) (hf : f ≫ yk = xk)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ N : ℕ, ∀ (c : Compactification f) (A : Type (u + 1)) [CommRing A] [Finite A],
      (∃ r : ℕ, (l : A) ^ r = 0) →
      ∀ (b : ℤ) (K : Etale.DerivedCategoryModule A X), K.IsLE b →
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).obj K).IsLE (b + (N : ℤ)) := by
  obtain ⟨N, hN⟩ := Etale.exceptionalConstantTensor k p l hl xk yk f hf
  refine ⟨N, fun c A _ _ ht ↦ (hN c A ?_).1⟩
  obtain ⟨r, hr⟩ := ht
  exact ⟨r, fun z ↦ by rw [hr, zero_mul]⟩

private theorem brownFiniteQuotient
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ha : ∃ r : ℕ, (l : A) ^ r = 0) (hb : ∃ r : ℕ, (l : B) ^ r = 0)
    (a : A →+* B)
    (ga : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X)
    (gb : Etale.DerivedCategoryModule B Y ⥤ Etale.DerivedCategoryModule B X)
    (aa : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ ga)
    (ab : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⊣ gb) :
    ∃ q : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        Etale.scalarExtension a Y ≅ Etale.scalarExtension a X ⋙
          Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c,
      q.hom = Etale.compactScalarMap a c ∧
        IsIso (mateEquiv aa ab (.mk _ _ _ _ q.inv)).natTrans := by
  obtain ⟨q, hq, r, _, rho, _, _, b, hb, _⟩ :=
    Etale.etaleCoefficientQuotientNormalization D l hl f c A B
      (by simpa only [Nat.cast_pow] using ha)
      (by simpa only [Nat.cast_pow] using hb) a ga gb aa ab
  refine ⟨q, hq, ?_⟩
  change IsIso (Etale.etaleCoefficientQuotientMate a c aa ab q)
  rw [← hb]
  infer_instance

private theorem brownInverseWord {C : Type*} [Category C]
    {V₀ V₁ V₂ V₃ V₄ V₅ : C}
    (a : V₀ ⟶ V₁) (b : V₁ ⟶ V₂) (c : V₂ ≅ V₃)
    (d : V₃ ≅ V₄) (e : V₄ ≅ V₅) (q : V₀ ≅ V₅)
    (h : a ≫ b ≫ c.hom ≫ d.hom ≫ e.hom = q.hom) :
    e.inv ≫ d.inv ≫ c.inv = q.inv ≫ a ≫ b := by
  apply (cancel_epi q.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id,
    Iso.hom_inv_id]

private theorem brownCubeMate_isIso
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    [c.ReflectsIsomorphisms]
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      K'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (hF : IsIso (mateEquiv adj adj' (.mk _ _ _ _ pF.inv)).natTrans)
    (hK : IsIso (mateEquiv adjK adjK' (.mk _ _ _ _ pK.inv)).natTrans)
    (hθ : IsIso (mateEquiv adj' adjK' (.mk _ _ _ _ θ')).natTrans) :
    IsIso (mateEquiv adj adjK (.mk _ _ _ _ θ)).natTrans := by
  have hFapp (M : B) : IsIso ((mateEquiv adj adj'
      (.mk _ _ _ _ pF.inv)).app M) := NatIso.isIso_app_of_isIso _ M
  have hKapp (M : D) : IsIso ((mateEquiv adjK adjK'
      (.mk _ _ _ _ pK.inv)).app M) := NatIso.isIso_app_of_isIso _ M
  have hθapp (M : B') : IsIso ((mateEquiv adj' adjK'
      (.mk _ _ _ _ θ')).app M) := NatIso.isIso_app_of_isIso _ M
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have he := exchangeMate_cube adj adjK adj' adjK' a b c d pF pG pH pK θ θ' hc M
  have hi : IsIso
      (c.map ((mateEquiv adj adjK (.mk _ _ _ _ θ)).app M) ≫
        (mateEquiv adjK adjK' (.mk _ _ _ _ pK.inv)).app (H.obj M) ≫
        S'.map (pH.hom.app M)) := by
    rw [he]
    infer_instance
  have : IsIso (c.map ((mateEquiv adj adjK (.mk _ _ _ _ θ)).app M)) :=
    IsIso.of_isIso_comp_right _
      ((mateEquiv adjK adjK' (.mk _ _ _ _ pK.inv)).app (H.obj M) ≫
        S'.map (pH.hom.app M))
  exact isIso_of_reflects_iso _ c

private theorem brownQuotientMate_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) {O : Type (u + 1)} [CommRing O] {t : O}
    (S : StrictEtaleCompactSupport O t c) (B : StrictEtaleBrownConstruction O t c S)
    (hfinite : ∀ n, Finite (strictEtaleBrownRing O t n))
    (htorsion : ∀ n, ∃ r : ℕ, (l : strictEtaleBrownRing O t n) ^ r = 0)
    (g : ∀ n, DerivedCategory (strictEtaleLevel Y O t n) ⥤
      DerivedCategory (strictEtaleLevel X O t n))
    (adjN : ∀ n, S.levelFunctor n ⊣ g n) {m n : ℕ} (h : n ≤ m) :
    IsIso (strictEtaleBrownQuotientMate B adjN h) := by
  have : Finite (strictEtaleBrownRing O t m) := hfinite m
  have : Finite (strictEtaleBrownRing O t n) := hfinite n
  have := B.realizationX.val.equivalence m
  have := B.realizationY.val.equivalence m
  have := B.realizationX.val.equivalence n
  have := B.realizationY.val.equivalence n
  let Fm := Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) c
  let Fn := Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c
  have : Fm.IsLeftAdjoint :=
    Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification _ c
  have : Fn.IsLeftAdjoint :=
    Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification _ c
  let am : Fm ⊣ Fm.rightAdjoint := Adjunction.ofIsLeftAdjoint Fm
  let an : Fn ⊣ Fn.rightAdjoint := Adjunction.ofIsLeftAdjoint Fn
  obtain ⟨q, hq, hib⟩ := brownFiniteQuotient D l hl f c
    (strictEtaleBrownRing O t m) (strictEtaleBrownRing O t n)
    (htorsion m) (htorsion n) (strictEtaleBrownRingMap O t h)
    Fm.rightAdjoint Fn.rightAdjoint am an
  have him := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (adjN m) am (B.realizationX.derived m) (B.realizationY.derived m)
    (B.levelComparison m).symm
  have hin := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (adjN n) an (B.realizationX.derived n) (B.realizationY.derived n)
    (B.levelComparison n).symm
  have hc (P : DerivedCategory (strictEtaleLevel X O t m)) :
      Fn.map ((B.realizationX.scalar h).inv.app P) ≫
        (B.levelComparison n).inv.app ((S.PX.scalar h).derived.obj P) ≫
        (B.realizationY.derived n).map ((B.projection h).hom.app P) =
      q.inv.app ((B.realizationX.derived m).obj P) ≫
        (Etale.scalarExtension (strictEtaleBrownRingMap O t h) Y).map
          ((B.levelComparison m).inv.app P) ≫
        (B.realizationY.scalar h).inv.app ((S.levelFunctor m).obj P) := by
    have he := B.projection_recorded_q h P
    rw [← hq] at he
    exact brownInverseWord _ _
      ((B.realizationY.derived n).mapIso ((B.projection h).app P)).symm
      ((B.levelComparison n).app ((S.PX.scalar h).derived.obj P))
      (Fn.mapIso ((B.realizationX.scalar h).app P))
      (q.app ((B.realizationX.derived m).obj P)) he
  exact brownCubeMate_isIso (adjN m) (adjN n) am an
    (B.realizationX.derived m) (B.realizationY.derived m)
    (B.realizationX.derived n) (B.realizationY.derived n)
    (B.levelComparison m) (B.realizationX.scalar h)
    (B.realizationY.scalar h) (B.levelComparison n)
    (B.projection h).hom q.inv hc him hin hib

end ScalarTargetAssembly

end AlgebraicGeometry

section IdentityTransportProof
attribute [local instance 6000]
  SheafOfModules.CoefficientSystemOrdinaryImage.systemInverseAdditive
  SheafOfModules.CoefficientSystemOrdinaryImage.inverseAdditive
set_option backward.isDefEq.respectTransparency true
universe v w
attribute [local instance 5000] AlgebraicGeometry.strictEtaleSystemDerived
  AlgebraicGeometry.strictEtaleLevelDerived
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.constantSheaf SheafOfModules.siteCoefficientTensor
  SheafOfModules.siteCoefficientTensorAdj
  SheafOfModules.coefficientQuotientMap
  AlgebraicGeometry.StrictEtaleCoefficientChange.sheaf

namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  {O : Type w} [CommRing O] {ell : O}

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem systemHom_ext {M N : CoefficientSystem (J := J) O ell}
    (f g : M.Hom N) (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr 1
  funext n
  exact h n

end SheafOfModules

namespace CategoryTheory
end CategoryTheory

namespace CategoryTheory
end CategoryTheory

namespace CategoryTheory
private theorem mate_identity
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {U : C ⥤ C} {V : D ⥤ D} (i : U ≅ 𝟭 C) (j : V ≅ 𝟭 D)
    (α : U ⋙ L ⟶ L ⋙ V)
    (h : ∀ X, α.app X ≫ j.hom.app (L.obj X) = L.map (i.hom.app X))
    (Y : D) :
    (mateEquiv adj adj (.mk _ _ _ _ α)).app Y ≫ R.map (j.hom.app Y) =
      i.hom.app (R.obj Y) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hn := adj.counit.naturality (j.hom.app Y)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [hn]
  have ht := mateEquiv_counit adj adj (.mk _ _ _ _ α) Y
  rw [reassoc_of% ht]
  have hu := j.hom.naturality (adj.counit.app Y)
  dsimp only [Functor.comp_map, Functor.id_map] at hu
  change V.map (adj.counit.app Y) ≫ j.hom.app Y =
    j.hom.app (L.obj (R.obj Y)) ≫ adj.counit.app Y at hu
  change α.app (R.obj Y) ≫ V.map (adj.counit.app Y) ≫ j.hom.app Y = _
  rw [hu, ← Category.assoc, h]

end CategoryTheory

end IdentityTransportProof

namespace CategoryTheory
end CategoryTheory

namespace AlgebraicGeometry
end AlgebraicGeometry
