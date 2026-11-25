/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionEquivalence
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence

/-!
# Completed lisse sheaves and normalized finite etale systems

Source: Bhatt--Scholze, Lemma 6.8.2, Corollary 5.1.5 and Proposition 6.8.4(1),(4),
pp. 35, 58--59 (blueprint: def-per-lisse-completed-system-data).

Positive exponent n+1 is indexed by n. The finite-free restriction of the recorded
Weil II system category is explicit. Coefficients are actual completed ring sheaves;
the continuous-function presentation is identified by its residue projections.
-/

@[expose] public noncomputable section
set_option Elab.async true
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CompletedLisse

/-- The coefficients and scheme in BS 6.8.4, with exactly the hypotheses of this node.
Source: BS 6.8.4 (blueprint: def-per-lisse-completed-system-data). -/
structure Base (l : ℕ) [Fact l.Prime] where
  E : Type (u + 1)
  field : Field E
  algebra : Algebra ℚ_[l] E
  finiteDimensional : FiniteDimensional ℚ_[l] E
  X : Scheme.{u}
  noetherian : IsNoetherian X
  separated : X.IsSeparated
  invertible : ∀ x : X, Invertible (l : X.residueField x)

attribute [instance] Base.field Base.algebra Base.finiteDimensional Base.noetherian
  Base.separated Base.invertible

variable (l : ℕ) [Fact l.Prime]

/-- Integral coefficients, using the recorded valuation ring.
Source: BS 6.8.2 (blueprint: def-per-lisse-completed-system-data). -/
noncomputable abbrev Integers (P : Base.{u} l) := Padic.coefficientExtensionIntegers l P.E

/-- The actual inverse limit of constant finite quotient ring sheaves.
Source: BS 6.8.2(1) (blueprint: def-per-lisse-completed-system-data). -/
noncomputable abbrev completedRing (P : Base.{u} l) :=
  adicLisseCompletedRing P.X
    (Ideal.span ({Padic.coefficientExtensionUniformizer l P.E} : Set (Integers l P)))

/-- The ring of continuous rational coefficients, canonically the localized completion.
Source: BS 6.8.2(2) (blueprint: def-per-lisse-completed-system-data). -/
noncomputable abbrev rationalRing (P : Base.{u} l) := lisseFieldSheafSized l P.E P.X

/-- The full category of completed lisse modules; finite rank may vary and may be zero.
Source: BS 6.8.3 (blueprint: def-per-lisse-completed-system-data). -/
noncomputable abbrev Integral (P : Base.{u} l) :=
  (SheafOfModules.isFiniteLocallyFree
    ((adicLisseForget P.X).obj (completedRing l P))).FullSubcategory

/-- Rational lisse modules over the continuous/localized coefficient sheaf.
Source: BS 6.8.3 (blueprint: def-per-lisse-completed-system-data). -/
noncomputable abbrev Rational (P : Base.{u} l) :=
  (SheafOfModules.isFiniteLocallyFree
    ((adicLisseForget P.X).obj (rationalRing l P))).FullSubcategory

/-- The finite-free restriction of the recorded normalized system category. Freeness is
expressed on every geometric stalk as an integral-linear isomorphism with A_n^r.
The recorded finite-local-constancy condition makes this exactly etale local freeness.
Source: Weil II (1.1.1) b), BS 6.8.4(1)
(blueprint: def-per-lisse-completed-system-data). -/
noncomputable def IsFreeSystem (P : Base.{u} l) (F : LisseIntegralSheaf l P.E P.X) : Prop :=
  ∀ (n : ℕ) (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ P.X),
    ∃ r : ℕ, Nonempty
      (((pointSmallEtale x).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} (Integers l P))).obj (F.obj.obj (op n)) ≃ₗ[Integers l P]
          (Fin r → Padic.coefficientExtensionRing l P.E (n + 1)))

/-- Normalized finite-free etale towers, with the recorded compatible-family morphisms.
Source: BS 6.8.4(1) (blueprint: def-per-lisse-completed-system-data). -/
noncomputable abbrev Systems (P : Base.{u} l) := ObjectProperty.FullSubcategory (IsFreeSystem l P)

/-- The raw rational category restricted to precisely the finite-free integral systems.
No idempotent completion or existence of a global lattice is imposed.
Source: BS 6.8.4(4), Weil II (1.1.1) c)
(blueprint: def-per-lisse-completed-system-data). -/
noncomputable abbrev RawRational (P : Base.{u} l) :=
  ObjectProperty.FullSubcategory
    (fun F : LisseRationalSheaf l P.E P.X ↦ IsFreeSystem l P F.integral)

/-- Forget only the module action, retaining the sheaf of abelian groups.
Source: BS 6.8.4(1) (blueprint: def-per-lisse-completed-system-data). -/
noncomputable abbrev integralForget (P : Base.{u} l) :=
  SheafOfModules.toSheaf.{u + 1} ((adicLisseForget P.X).obj (completedRing l P))

/-- Underlying abelian sheaves of the recorded normalized etale levels.
Source: BS 6.8.4(1) (blueprint: def-per-lisse-completed-system-data). -/
noncomputable def etaleDiagram (P : Base.{u} l) (F : Systems l P) :
    ℕᵒᵖ ⥤ Sheaf P.X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  F.obj.obj ⋙ sheafCompose _ (forget₂ (ModuleCat.{u + 1} (Integers l P)) AddCommGrpCat)

/-- The actual levelwise etale-to-pro-etale inverse image, on underlying abelian sheaves.
The coefficient actions are retained by the scalar equations in Comparison.
Source: BS 5.1.5, 6.8.4(1) (blueprint: def-per-lisse-completed-system-data). -/
noncomputable def proEtaleDiagram (P : Base.{u} l) (F : Systems l P) :
    ℕᵒᵖ ⥤ Sheaf (ProEt.topology P.X) AddCommGrpCat.{u + 1} :=
  etaleDiagram l P F ⋙ supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} P.X

/-- Constant scalar multiplication on completed modules, transported by the coefficient
identification. Its underlying abelian map is the same actual scalar endomorphism.
Source: BS 6.8.2 (blueprint: def-per-lisse-completed-system-data). -/
noncomputable def integralScalar (P : Base.{u} l)
    (e : lisseIntegerSheafSized l P.E P.X ≅ completedRing l P)
    (M : Integral l P) (a : Integers l P) :
    (integralForget l P).obj M.obj ⟶ (integralForget l P).obj M.obj :=
  (SheafOfModules.toSheaf (integralLisseRing l P.E P.X)).map
    (integralLisseScalar l P.E P.X
      ((SheafOfModules.restrictScalars ((adicLisseForget P.X).map e.hom)).obj M.obj) a)

/-- Multiplication by a rational constant on a rational module, with its actual action.
Source: BS 6.8.4(4) (blueprint: def-per-lisse-completed-system-data). -/
noncomputable def rationalScalar (P : Base.{u} l)
    (M : ringedSiteModules.{u + 1} ((adicLisseForget P.X).obj (rationalRing l P)))
    (a : P.E) : M ⟶ M :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom
       { toFun := fun x ↦ lisseFieldConstantSized l P.E P.X U a • x
         map_add' := smul_add _
         map_smul' := fun r x ↦ by
           change _ • (r • x) = r • (_ • x)
           rw [smul_smul, smul_smul]
           exact congrArg (fun c : (rationalRing l P).obj.obj U ↦ c • x) (mul_comm _ _) }
     naturality := fun {_U _V} f ↦ by
       ext x
       exact (M.val.map_smul f (lisseFieldConstantSized l P.E P.X _ a) x).symm }⟩

/-- The fixed completed-coefficient comparison at one base. Every functor is normalized
by quotient/limit universal properties and every rational map by its pure-tensor formula.
Source: BS 5.1.5, 6.8.2, 6.8.4(1),(4)
(blueprint: def-per-lisse-completed-system-data). -/
structure IntegralComparison (P : Base.{u} l) where
  integralComparison : IntegralLisseReductionEquivalence l P.E P.X
  coefficientIso : lisseIntegerSheafSized l P.E P.X ≅ completedRing l P
  coefficient_projection (n : ℕ) :
    coefficientIso.hom ≫ limit.π (adicLisseRingSystem P.X
      (Ideal.span ({Padic.coefficientExtensionUniformizer l P.E} : Set (Integers l P))))
        (op n) = integralLisseReduction l P.E P.X n ≫
          (integralComparison.finiteConstant n).inv
  equivalence : Integral l P ≌ Systems l P
  reduction (M : Integral l P) :
    (Functor.const ℕᵒᵖ).obj ((integralForget l P).obj M.obj) ⟶
      proEtaleDiagram l P (equivalence.functor.obj M)
  reduction_quotient (M : Integral l P) (n : ℕ) :
    ∃ h : integralScalar l P coefficientIso M
        (Padic.coefficientExtensionUniformizer l P.E ^ (n + 1)) ≫
          (reduction M).app (op n) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ ((reduction M).app (op n)) h))
  reduction_scalar (M : Integral l P) (n : ℕ) (a : Integers l P) :
    integralScalar l P coefficientIso M a ≫ (reduction M).app (op n) =
      (reduction M).app (op n) ≫
        (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} P.X).map
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (Integers l P)) AddCommGrpCat)).map
            (a • 𝟙 ((equivalence.functor.obj M).obj.obj.obj (op n))))
  reduction_natural {M N : Integral l P} (f : M ⟶ N) (n : ℕ) :
    (integralForget l P).map f.hom ≫ (reduction N).app (op n) =
      (reduction M).app (op n) ≫
        (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} P.X).map
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (Integers l P)) AddCommGrpCat)).map
            ((equivalence.functor.map f).hom.hom.app (op n)))
  completion (F : Systems l P) :
    (Functor.const ℕᵒᵖ).obj ((integralForget l P).obj (equivalence.inverse.obj F).obj) ⟶
      proEtaleDiagram l P F
  completion_limit (F : Systems l P) : IsLimit (Cone.mk _ (completion F))
  completion_natural {F G : Systems l P} (f : F ⟶ G) (n : ℕ) :
    (integralForget l P).map (equivalence.inverse.map f).hom ≫
        (completion G).app (op n) = (completion F).app (op n) ≫
      (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} P.X).map
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (Integers l P)) AddCommGrpCat)).map
          (f.hom.hom.app (op n)))
  unit_projection (M : Integral l P) (n : ℕ) :
    (integralForget l P).map (equivalence.unitIso.hom.app M).hom ≫
      (completion (equivalence.functor.obj M)).app (op n) = (reduction M).app (op n)
  counit_projection (F : Systems l P) (n : ℕ) :
    (reduction (equivalence.inverse.obj F)).app (op n) ≫
      (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} P.X).map
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (Integers l P)) AddCommGrpCat)).map
          ((equivalence.counitIso.hom.app F).hom.hom.app (op n))) = (completion F).app (op n)

/-- The integral comparison together with rational realization.
Source: BS 6.8.4(1),(4) (blueprint: def-per-lisse-completed-system-data). -/
structure Comparison (P : Base.{u} l) extends IntegralComparison l P where
  rationalRealization : RawRational l P ⥤ Rational l P
  rationalObject (F : RawRational l P) :
    (rationalRealization.obj F).obj ≅
      (completedAdicChange P.X (coefficientIso.inv ≫ lisseIntegerToFieldSized l P.E P.X)).obj
        (equivalence.inverse.obj ⟨F.obj.integral, F.property⟩).obj
  rational_map (F G : RawRational l P) (a : P.E)
      (f : F.obj.integral ⟶ G.obj.integral) :
    (rationalRealization.map ⟨TensorProduct.tmul (Integers l P) a f⟩).hom ≫
        (rationalObject G).hom =
      (rationalObject F).hom ≫
        (completedAdicChange P.X
          (coefficientIso.inv ≫ lisseIntegerToFieldSized l P.E P.X)).map
            (equivalence.inverse.map ⟨f⟩).hom ≫
        rationalScalar l P _ a
  rational_add (F G : RawRational l P) (f g : F ⟶ G) :
    rationalRealization.map ⟨f.hom + g.hom⟩ = rationalRealization.map f + rationalRealization.map g
  rationalFullyFaithful : rationalRealization.FullyFaithful

/-- A simultaneous scheme pullback and finite coefficient inclusion. Pure pullbacks
and pure coefficient extensions are obtained by taking the other map to be an identity.
Source: BS 6.8.4 and Weil II (1.1.1) d)
(blueprint: def-per-lisse-completed-system-data). -/
structure Arrow (P Q : Base.{u} l) where
  scheme : Q.X ⟶ P.X
  coefficient : P.E →ₐ[ℚ_[l]] Q.E

/-- Identity operation, including identity coefficient extension.
Source: BS 6.8.4 (blueprint: def-per-lisse-completed-system-data). -/
noncomputable def identity (P : Base.{u} l) : Arrow l P P := ⟨𝟙 P.X, AlgHom.id _ _⟩

/-- Composition retains the actual scheme composite and field inclusion composite.
Source: BS 6.8.4 (blueprint: def-per-lisse-completed-system-data). -/
noncomputable def composite {P Q S : Base.{u} l} (a : Arrow l P Q)
    (b : Arrow l Q S) : Arrow l P S :=
  ⟨b.scheme ≫ a.scheme, b.coefficient.comp a.coefficient⟩

/-- The ramified source index ceil((m+1)/e)-1 from the recorded scalar extension.
Source: Weil II (1.1.1) d) (blueprint: def-per-lisse-completed-system-data). -/
noncomputable abbrev sourceIndex {P Q : Base.{u} l} (a : Arrow l P Q) (m : ℕ) :=
  lisseScalarSourceIndex l P.E Q.E a.coefficient m

/-- The actual finite-level operation: etale module pullback and then sheafified
balanced scalar extension to A'_m, retaining the A'-action by restriction of scalars.
Source: BS 6.8.4(1), Weil II (1.1.1) d)
(blueprint: def-per-lisse-completed-system-data). -/
noncomputable def finiteLevel {P Q : Base.{u} l} (a : Arrow l P Q) (m : ℕ) :
    Systems l P ⥤ Sheaf Q.X.smallEtaleTopology (ModuleCat.{u + 1} (Integers l Q)) :=
  ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙
    (CategoryTheory.evaluation _ _).obj (op (sourceIndex l a m)) ⋙
      supportSiteEtaleComparisonPullback (ModuleCat.{u + 1} (Integers l P)) a.scheme ⋙
        Sheaf.ringExtendScalars.{u + 1, u + 1} Q.X.smallEtaleTopology
          (lisseScalarCoefficientMap l P.E Q.E a.coefficient m) ⋙
          sheafCompose _ (ModuleCat.restrictScalars.{u + 1}
            (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l Q.E (m + 1))))

/-- The canonical map to scalar extension, on underlying abelian sheaves. This is the
universal module unit followed by the actual sheafification unit, so sends x to 1 tensor x.
Source: Stacks, Modules on Sites, scalar extension; Weil II (1.1.1) d)
(blueprint: def-per-lisse-completed-system-data). -/
noncomputable def finiteScalarUnit {X : Scheme.{u}} {A B : Type (u + 1)} [Ring A] [Ring B]
    (φ : A →+* B) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat)).obj F ⟶
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat)).obj
        ((Sheaf.ringExtendScalars.{u + 1, u + 1} X.smallEtaleTopology φ).obj F) :=
  ⟨Functor.whiskerLeft F.obj (Functor.whiskerRight
      (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} φ).unit
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat)) ≫
    Functor.whiskerRight ((toSheafification X.smallEtaleTopology (ModuleCat.{u + 1} B)).app
      (F.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} φ))
      (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat)⟩

/-- The finite-level pullback/scalar-extension unit, with source quotient reindexed
by the ramification ceiling. Its two factors are the specified universal units.
Source: BS 6.8.4(1), Weil II (1.1.1) d)
(blueprint: def-per-lisse-completed-system-data). -/
noncomputable def finiteEtaleUnit {P Q : Base.{u} l} (a : Arrow l P Q) (F : Systems l P) (m : ℕ) :
    (etaleDiagram l P F).obj (op (sourceIndex l a m)) ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} a.scheme).obj
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (Integers l Q)) AddCommGrpCat)).obj
          ((finiteLevel l a m).obj F)) :=
  (sheafCompose _ (forget₂ (ModuleCat.{u + 1} (Integers l P)) AddCommGrpCat)).map
      ((supportSiteEtaleComparisonAdjunction
        (ModuleCat.{u + 1} (Integers l P)) a.scheme).unit.app
          (F.obj.obj.obj (op (sourceIndex l a m)))) ≫
    (Etale.lowerStar AddCommGrpCat.{u + 1} a.scheme).map
      (finiteScalarUnit (lisseScalarCoefficientMap l P.E Q.E a.coefficient m)
        ((supportSiteEtaleComparisonPullback
          (ModuleCat.{u + 1} (Integers l P)) a.scheme).obj
            (F.obj.obj.obj (op (sourceIndex l a m)))))

/-- The same finite unit on the pro-etale site, using precisely the canonical site
comparison mate. No preservation of an infinite limit by inverse image is asserted.
Source: BS 5.1.5, 6.8.4(1); the comparison-pullback dependency
(blueprint: def-per-lisse-completed-system-data). -/
noncomputable def finiteProEtaleUnit {P Q : Base.{u} l} (a : Arrow l P Q)
    (F : Systems l P) (m : ℕ) :
    (proEtaleDiagram l P F).obj (op (sourceIndex l a m)) ⟶
      (proEtaleSheafDirectImage a.scheme AddCommGrpCat.{u + 1}).obj
        ((supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} Q.X).obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (Integers l Q)) AddCommGrpCat)).obj
            ((finiteLevel l a m).obj F))) :=
  (supportSiteProEtaleComparisonAdjunction AddCommGrpCat.{u + 1} a.scheme).homEquiv _ _
    ((supportSiteComparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} a.scheme).inv.app
        ((etaleDiagram l P F).obj (op (sourceIndex l a m))) ≫
      (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} Q.X).map
        ((supportSiteEtaleComparisonAdjunction AddCommGrpCat.{u + 1} a.scheme).homEquiv _ _
          |>.symm (finiteEtaleUnit l a F m)))

/-- A finite tower with its prescribed finite-level scalar/pullback identifications.
Source: Weil II (1.1.1) d), BS 6.8.4(1)
(blueprint: def-per-lisse-completed-system-data). -/
structure EtaleOperation {P Q : Base.{u} l} (a : Arrow l P Q) where
  functor : Systems l P ⥤ Systems l Q
  level (m : ℕ) :
    functor ⋙ ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙
      (CategoryTheory.evaluation _ _).obj (op m) ≅ finiteLevel l a m

/-- The unit on the actual output levels, normalized by their finite tensor description.
Source: BS 6.8.4(1) (blueprint: def-per-lisse-completed-system-data). -/
noncomputable def EtaleOperation.unit {P Q : Base.{u} l} {a : Arrow l P Q}
    (T : EtaleOperation l a) (F : Systems l P) (m : ℕ) :
    (etaleDiagram l P F).obj (op (sourceIndex l a m)) ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} a.scheme).obj
        ((etaleDiagram l Q (T.functor.obj F)).obj (op m)) :=
  finiteEtaleUnit l a F m ≫ (Etale.lowerStar AddCommGrpCat.{u + 1} a.scheme).map
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (Integers l Q)) AddCommGrpCat)).map
      ((T.level m).inv.app F))

/-- The same normalized unit after site comparison, given by the specified adjoint mate.
Source: BS 5.1.5, 6.8.4(1) (blueprint: def-per-lisse-completed-system-data). -/
noncomputable def EtaleOperation.proEtaleUnit {P Q : Base.{u} l} {a : Arrow l P Q}
    (T : EtaleOperation l a) (F : Systems l P) (m : ℕ) :
    (proEtaleDiagram l P F).obj (op (sourceIndex l a m)) ⟶
      (proEtaleSheafDirectImage a.scheme AddCommGrpCat.{u + 1}).obj
        ((proEtaleDiagram l Q (T.functor.obj F)).obj (op m)) :=
  (supportSiteProEtaleComparisonAdjunction AddCommGrpCat.{u + 1} a.scheme).homEquiv _ _
    ((supportSiteComparisonCoefficientPullbackIso AddCommGrpCat.{u + 1} a.scheme).inv.app
        ((etaleDiagram l P F).obj (op (sourceIndex l a m))) ≫
      (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} Q.X).map
        ((supportSiteEtaleComparisonAdjunction AddCommGrpCat.{u + 1} a.scheme).homEquiv _ _
          |>.symm (T.unit l F m)))

/-- The coefficient maps are fixed on all continuous functions, and the completed
coefficient map by its continuous presentation. They are maps of actual ring sheaves.
Source: BS 6.8.2 and 6.8.4 (blueprint: def-per-lisse-completed-system-data). -/
structure RingOperation {P Q : Base.{u} l} (a : Arrow l P Q)
    (cP : Comparison l P) (cQ : Comparison l Q) where
  integral : lisseIntegerSheafSized l P.E P.X ⟶
    (proEtaleSheafDirectImage a.scheme CommRingCat.{u + 1}).obj
      (lisseIntegerSheafSized l Q.E Q.X)
  integral_sections (V : P.X.ProEt)
      (s : (lisseIntegerSheafSized l P.E P.X).obj.obj (op V))
      (z : ((proEtaleBaseChange a.scheme).obj V).left) :
    ((integral.hom.app (op V) s).down z : Q.E) =
      a.coefficient (s.down ((pullback.fst V.hom a.scheme).base z) : P.E)
  completed : completedRing l P ⟶
    (proEtaleSheafDirectImage a.scheme CommRingCat.{u + 1}).obj (completedRing l Q)
  completed_normalization : cP.coefficientIso.hom ≫ completed =
    integral ≫ (proEtaleSheafDirectImage a.scheme CommRingCat.{u + 1}).map cQ.coefficientIso.hom
  rational : rationalRing l P ⟶
    (proEtaleSheafDirectImage a.scheme CommRingCat.{u + 1}).obj (rationalRing l Q)
  rational_sections (V : P.X.ProEt)
      (s : (rationalRing l P).obj.obj (op V))
      (z : ((proEtaleBaseChange a.scheme).obj V).left) :
    (rational.hom.app (op V) s).down z =
      a.coefficient (s.down ((pullback.fst V.hom a.scheme).base z))
  localization_square : (cP.coefficientIso.inv ≫ lisseIntegerToFieldSized l P.E P.X) ≫
      rational = completed ≫
        (proEtaleSheafDirectImage a.scheme CommRingCat.{u + 1}).map
          (cQ.coefficientIso.inv ≫ lisseIntegerToFieldSized l Q.E Q.X)

/-- Completed module direct image with the specified coefficient map; no preservation
of infinite inverse limits by inverse image is used.
Source: Stacks 03D1; BS 6.8.4 (blueprint: def-per-lisse-completed-system-data). -/
noncomputable def RingOperation.integralPush {P Q : Base.{u} l} {a : Arrow l P Q}
    {cP : Comparison l P} {cQ : Comparison l Q} (R : RingOperation l a cP cQ) :
    ringedSiteModules.{u + 1} ((adicLisseForget Q.X).obj (completedRing l Q)) ⥤
      ringedSiteModules.{u + 1} ((adicLisseForget P.X).obj (completedRing l P)) :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange a.scheme)
    (J := ProEt.topology P.X) (K := ProEt.topology Q.X)
    (S := (adicLisseForget P.X).obj (completedRing l P))
    (R := (adicLisseForget Q.X).obj (completedRing l Q))
    ((adicLisseForget P.X).map R.completed)

/-- Rational module direct image, with the same continuous coefficient formula.
Source: Stacks 03D1; BS 6.8.4 (blueprint: def-per-lisse-completed-system-data). -/
noncomputable def RingOperation.rationalPush {P Q : Base.{u} l} {a : Arrow l P Q}
    {cP : Comparison l P} {cQ : Comparison l Q} (R : RingOperation l a cP cQ) :
    ringedSiteModules.{u + 1} ((adicLisseForget Q.X).obj (rationalRing l Q)) ⥤
      ringedSiteModules.{u + 1} ((adicLisseForget P.X).obj (rationalRing l P)) :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange a.scheme)
    (J := ProEt.topology P.X) (K := ProEt.topology Q.X)
    (S := (adicLisseForget P.X).obj (rationalRing l P))
    (R := (adicLisseForget Q.X).obj (rationalRing l Q))
    ((adicLisseForget P.X).map R.rational)

/-- The canonical ringed-module pullback is specified by its full adjunction, together
with its restriction to lisse objects and the resulting universal unit. This interface
retains independent site object and morphism universes.
Source: Stacks 03D2; BS 6.8.4 (blueprint: def-per-lisse-completed-system-data). -/
structure ModuleOperation {P Q : Base.{u} l} {a : Arrow l P Q}
    {cP : Comparison l P} {cQ : Comparison l Q} (R : RingOperation l a cP cQ) where
  integralAmbient :
    ringedSiteModules.{u + 1} ((adicLisseForget P.X).obj (completedRing l P)) ⥤
      ringedSiteModules.{u + 1} ((adicLisseForget Q.X).obj (completedRing l Q))
  integralAdjunction : integralAmbient ⊣ R.integralPush l
  integral : Integral l P ⥤ Integral l Q
  integralUnderlying : integral ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙ integralAmbient
  rationalAmbient :
    ringedSiteModules.{u + 1} ((adicLisseForget P.X).obj (rationalRing l P)) ⥤
      ringedSiteModules.{u + 1} ((adicLisseForget Q.X).obj (rationalRing l Q))
  rationalAdjunction : rationalAmbient ⊣ R.rationalPush l
  rational : Rational l P ⥤ Rational l Q
  rationalUnderlying : rational ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙ rationalAmbient

/-- The canonical unit x to 1 tensor x for the lisse integral module pullback.
Source: Stacks 03D2 (blueprint: def-per-lisse-completed-system-data). -/
noncomputable def ModuleOperation.integralUnit {P Q : Base.{u} l} {a : Arrow l P Q}
    {cP : Comparison l P} {cQ : Comparison l Q} {R : RingOperation l a cP cQ}
    (M : ModuleOperation l R) (N : Integral l P) :
    (integralForget l P).obj N.obj ⟶
      (proEtaleSheafDirectImage a.scheme AddCommGrpCat.{u + 1}).obj
        ((integralForget l Q).obj (M.integral.obj N).obj) :=
  (integralForget l P).map (M.integralAdjunction.unit.app N.obj) ≫
    (proEtaleSheafDirectImage a.scheme AddCommGrpCat.{u + 1}).map
      ((integralForget l Q).map (M.integralUnderlying.inv.app N))

/-- The same universal unit for rational module pullback.
Source: Stacks 03D2 (blueprint: def-per-lisse-completed-system-data). -/
noncomputable def ModuleOperation.rationalUnit {P Q : Base.{u} l} {a : Arrow l P Q}
    {cP : Comparison l P} {cQ : Comparison l Q} {R : RingOperation l a cP cQ}
    (M : ModuleOperation l R) (N : Rational l P) :
    (SheafOfModules.toSheaf ((adicLisseForget P.X).obj (rationalRing l P))).obj N.obj ⟶
      (proEtaleSheafDirectImage a.scheme AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf ((adicLisseForget Q.X).obj (rationalRing l Q))).obj
          (M.rational.obj N).obj) :=
  (SheafOfModules.toSheaf ((adicLisseForget P.X).obj (rationalRing l P))).map
      (M.rationalAdjunction.unit.app N.obj) ≫
    (proEtaleSheafDirectImage a.scheme AddCommGrpCat.{u + 1}).map
      ((SheafOfModules.toSheaf ((adicLisseForget Q.X).obj (rationalRing l Q))).map
        (M.rationalUnderlying.inv.app N))

/-- The comparison image of a map at one finite level, retaining exactly its underlying map.
Source: BS 5.1.5 (blueprint: def-per-lisse-completed-system-data). -/
noncomputable def levelMap {P : Base.{u} l} {F G : Systems l P} (f : F ⟶ G) (m : ℕ) :
    (proEtaleDiagram l P F).obj (op m) ⟶ (proEtaleDiagram l P G).obj (op m) :=
  (supportSiteComparisonCoefficientPullback AddCommGrpCat.{u + 1} P.X).map
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (Integers l P)) AddCommGrpCat)).map
      (f.hom.hom.app (op m)))

-- Their declared types are the API used by the normalization equations below.
attribute [irreducible] finiteScalarUnit finiteEtaleUnit finiteProEtaleUnit
  EtaleOperation.unit EtaleOperation.proEtaleUnit ModuleOperation.integralUnit
  ModuleOperation.rationalUnit

/-- Pullback and finite coefficient extension, with the finite transition equation,
quotient-normalized reduction comparison, projection-normalized reconstruction, and the
fraction-normalized rational realization square. All adjunctions are on ambient module
sheaves, so their left adjoints are genuine tensor pullbacks, without extra assumptions.
Source: BS 6.8.4(1),(4), Weil II (1.1.1) d)
(blueprint: def-per-lisse-completed-system-data). -/
structure IntegralOperation {P Q : Base.{u} l} (a : Arrow l P Q)
    (cP : Comparison l P) (cQ : Comparison l Q) where
  rings : RingOperation l a cP cQ
  modules : ModuleOperation l rings
  etale : EtaleOperation l a
  etale_transition (F : Systems l P) (m : ℕ) :
    etale.unit l F (m + 1) ≫ (Etale.lowerStar AddCommGrpCat.{u + 1} a.scheme).map
        ((etaleDiagram l Q (etale.functor.obj F)).map (homOfLE (Nat.le_succ m)).op) =
      (etaleDiagram l P F).map
        (homOfLE (lisseScalarSourceIndex_le l P.E Q.E a.coefficient m)).op ≫ etale.unit l F m
  reduction : modules.integral ⋙ cQ.equivalence.functor ≅
    cP.equivalence.functor ⋙ etale.functor
  reduction_normalization (M : Integral l P) (m : ℕ) :
    modules.integralUnit l M ≫
      (proEtaleSheafDirectImage a.scheme AddCommGrpCat.{u + 1}).map
        ((cQ.reduction (modules.integral.obj M)).app (op m) ≫
          levelMap l (reduction.hom.app M) m) =
      (cP.reduction M).app (op (sourceIndex l a m)) ≫
        etale.proEtaleUnit l (cP.equivalence.functor.obj M) m
  reconstruction : cP.equivalence.inverse ⋙ modules.integral ≅
    etale.functor ⋙ cQ.equivalence.inverse
  reconstruction_normalization (F : Systems l P) (m : ℕ) :
    modules.integralUnit l (cP.equivalence.inverse.obj F) ≫
      (proEtaleSheafDirectImage a.scheme AddCommGrpCat.{u + 1}).map
        ((integralForget l Q).map (reconstruction.hom.app F).hom ≫
          (cQ.completion (etale.functor.obj F)).app (op m)) =
      (cP.completion F).app (op (sourceIndex l a m)) ≫ etale.proEtaleUnit l F m

/-- The integral operation and its raw rational extension.
Source: BS 6.8.4(1),(4) (blueprint: def-per-lisse-completed-system-data). -/
structure Operation {P Q : Base.{u} l} (a : Arrow l P Q)
    (cP : Comparison l P) (cQ : Comparison l Q) extends IntegralOperation l a cP cQ where
  raw : RawRational l P ⥤ RawRational l Q
  rawIntegral (F : RawRational l P) : (raw.obj F).obj.integral ≅
    (etale.functor.obj ⟨F.obj.integral, F.property⟩).obj
  raw_map (F G : RawRational l P) (a' : P.E) (f : F.obj.integral ⟶ G.obj.integral) :
    (raw.map ⟨TensorProduct.tmul (Integers l P) a' f⟩).hom =
      TensorProduct.tmul (Integers l Q) (a.coefficient a')
        ((rawIntegral F).hom ≫ (etale.functor.map ⟨f⟩).hom ≫ (rawIntegral G).inv)
  raw_add (F G : RawRational l P) (f g : F ⟶ G) :
    (raw.map ⟨f.hom + g.hom⟩).hom = (raw.map f).hom + (raw.map g).hom
  rational : cP.rationalRealization ⋙ modules.rational ≅ raw ⋙ cQ.rationalRealization
  rational_normalization (F : RawRational l P) (V : P.X.ProEt)
      (x : (cP.equivalence.inverse.obj ⟨F.obj.integral, F.property⟩).obj.val.obj (op V)) :
    (cQ.rationalObject (raw.obj F)).hom.val.app
        (op ((proEtaleBaseChange a.scheme).obj V))
      ((rational.hom.app F).hom.val.app (op ((proEtaleBaseChange a.scheme).obj V))
        ((modules.rationalUnit l (cP.rationalRealization.obj F)).hom.app (op V)
          ((cP.rationalObject F).inv.val.app (op V)
            (completedAdicChangeTensor P.X
              (cP.coefficientIso.inv ≫ lisseIntegerToFieldSized l P.E P.X)
              (cP.equivalence.inverse.obj ⟨F.obj.integral, F.property⟩).obj (op V) 1 x)))) =
    completedAdicChangeTensor Q.X
      (cQ.coefficientIso.inv ≫ lisseIntegerToFieldSized l Q.E Q.X)
      (cQ.equivalence.inverse.obj ⟨(raw.obj F).obj.integral, (raw.obj F).property⟩).obj
      (op ((proEtaleBaseChange a.scheme).obj V)) 1
      ((cQ.equivalence.inverse.map ⟨(rawIntegral F).inv⟩).hom.val.app
        (op ((proEtaleBaseChange a.scheme).obj V))
        ((reconstruction.hom.app ⟨F.obj.integral, F.property⟩).hom.val.app
          (op ((proEtaleBaseChange a.scheme).obj V))
          ((modules.integralUnit l (cP.equivalence.inverse.obj
            ⟨F.obj.integral, F.property⟩)).hom.app (op V) x)))

/-- Underlying abelian sheaves for rational coefficients.
Source: BS 6.8.4(4) (blueprint: def-per-lisse-completed-system-data). -/
noncomputable abbrev rationalForget (P : Base.{u} l) :=
  SheafOfModules.toSheaf.{u + 1} ((adicLisseForget P.X).obj (rationalRing l P))

/-- The comparison over all allowed schemes and coefficient fields, including its
identity and composition equations. Composition covers two pullbacks, two finite
extensions, and mixed pullback/extension. The integral and rational operation comparisons
are normalized by the actual adjunction units and the chosen fibre-product comparisons.
Source: BS 6.8.4(1),(4), with its reduction/limit/localization maps
(blueprint: def-per-lisse-completed-system-data). -/
structure SystemCore where
  comparison (P : Base.{u} l) : Comparison l P
  operation {P Q : Base.{u} l} (a : Arrow l P Q) :
    Operation l a (comparison P) (comparison Q)
  integralId (P : Base.{u} l) : (operation (identity l P)).modules.integral ≅ 𝟭 _
  rationalId (P : Base.{u} l) : (operation (identity l P)).modules.rational ≅ 𝟭 _
  integralId_normalization (P : Base.{u} l) (M : Integral l P) :
    (operation (identity l P)).modules.integralUnit l M ≫
      (proEtaleSheafDirectImage (𝟙 P.X) AddCommGrpCat.{u + 1}).map
        ((integralForget l P).map ((integralId P).hom.app M).hom) ≫
      (lowerStarId AddCommGrpCat.{u + 1} P.X).hom.app ((integralForget l P).obj M.obj) = 𝟙 _
  rationalId_normalization (P : Base.{u} l) (M : Rational l P) :
    (operation (identity l P)).modules.rationalUnit l M ≫
      (proEtaleSheafDirectImage (𝟙 P.X) AddCommGrpCat.{u + 1}).map
        ((rationalForget l P).map ((rationalId P).hom.app M).hom) ≫
      (lowerStarId AddCommGrpCat.{u + 1} P.X).hom.app ((rationalForget l P).obj M.obj) = 𝟙 _
  integralComp {P Q S : Base.{u} l} (a : Arrow l P Q) (b : Arrow l Q S) :
    (operation a).modules.integral ⋙ (operation b).modules.integral ≅
      (operation (composite l a b)).modules.integral
  rationalComp {P Q S : Base.{u} l} (a : Arrow l P Q) (b : Arrow l Q S) :
    (operation a).modules.rational ⋙ (operation b).modules.rational ≅
      (operation (composite l a b)).modules.rational
  integralComp_normalization {P Q S : Base.{u} l}
      (a : Arrow l P Q) (b : Arrow l Q S) (M : Integral l P) :
    (operation a).modules.integralUnit l M ≫
      (proEtaleSheafDirectImage a.scheme AddCommGrpCat.{u + 1}).map
        ((operation b).modules.integralUnit l ((operation a).modules.integral.obj M)) ≫
      (lowerStarComp AddCommGrpCat.{u + 1} b.scheme a.scheme).hom.app
        ((integralForget l S).obj
          ((operation b).modules.integral.obj ((operation a).modules.integral.obj M)).obj) ≫
      (proEtaleSheafDirectImage (b.scheme ≫ a.scheme) AddCommGrpCat.{u + 1}).map
        ((integralForget l S).map ((integralComp a b).hom.app M).hom) =
      (operation (composite l a b)).modules.integralUnit l M
  rationalComp_normalization {P Q S : Base.{u} l}
      (a : Arrow l P Q) (b : Arrow l Q S) (M : Rational l P) :
    (operation a).modules.rationalUnit l M ≫
      (proEtaleSheafDirectImage a.scheme AddCommGrpCat.{u + 1}).map
        ((operation b).modules.rationalUnit l ((operation a).modules.rational.obj M)) ≫
      (lowerStarComp AddCommGrpCat.{u + 1} b.scheme a.scheme).hom.app
        ((rationalForget l S).obj
          ((operation b).modules.rational.obj ((operation a).modules.rational.obj M)).obj) ≫
      (proEtaleSheafDirectImage (b.scheme ≫ a.scheme) AddCommGrpCat.{u + 1}).map
        ((rationalForget l S).map ((rationalComp a b).hom.app M).hom) =
      (operation (composite l a b)).modules.rationalUnit l M

/-- The ambient operations and the transported system and rational coherence.
Source: BS 6.8.4(1),(4) (blueprint: def-per-lisse-completed-system-data). -/
structure System extends SystemCore l where
  etaleId (P : Base.{u} l) : (operation (identity l P)).etale.functor ≅ 𝟭 _
  rawId (P : Base.{u} l) : (operation (identity l P)).raw ≅ 𝟭 _
  reduction_id (P : Base.{u} l) :
    (operation (identity l P)).reduction.hom ≫
      Functor.whiskerLeft (comparison P).equivalence.functor (etaleId P).hom =
        Functor.whiskerRight (integralId P).hom (comparison P).equivalence.functor
  reconstruction_id (P : Base.{u} l) :
    (operation (identity l P)).reconstruction.hom ≫
      Functor.whiskerRight (etaleId P).hom (comparison P).equivalence.inverse =
        Functor.whiskerLeft (comparison P).equivalence.inverse (integralId P).hom
  realization_id (P : Base.{u} l) :
    (operation (identity l P)).rational.hom ≫
      Functor.whiskerRight (rawId P).hom (comparison P).rationalRealization =
        Functor.whiskerLeft (comparison P).rationalRealization (rationalId P).hom
  etaleComp {P Q S : Base.{u} l} (a : Arrow l P Q) (b : Arrow l Q S) :
    (operation a).etale.functor ⋙ (operation b).etale.functor ≅
      (operation (composite l a b)).etale.functor
  rawComp {P Q S : Base.{u} l} (a : Arrow l P Q) (b : Arrow l Q S) :
    (operation a).raw ⋙ (operation b).raw ≅ (operation (composite l a b)).raw
  reduction_comp {P Q S : Base.{u} l} (a : Arrow l P Q) (b : Arrow l Q S) :
    Functor.whiskerRight (integralComp a b).hom (comparison S).equivalence.functor ≫
      (operation (composite l a b)).reduction.hom =
    Functor.whiskerLeft (operation a).modules.integral (operation b).reduction.hom ≫
      Functor.whiskerRight (operation a).reduction.hom (operation b).etale.functor ≫
      Functor.whiskerLeft (comparison P).equivalence.functor (etaleComp a b).hom
  reconstruction_comp {P Q S : Base.{u} l} (a : Arrow l P Q) (b : Arrow l Q S) :
    Functor.whiskerLeft (comparison P).equivalence.inverse (integralComp a b).hom ≫
      (operation (composite l a b)).reconstruction.hom =
    Functor.whiskerRight (operation a).reconstruction.hom (operation b).modules.integral ≫
      Functor.whiskerLeft (operation a).etale.functor (operation b).reconstruction.hom ≫
      Functor.whiskerRight (etaleComp a b).hom (comparison S).equivalence.inverse
  realization_comp {P Q S : Base.{u} l} (a : Arrow l P Q) (b : Arrow l Q S) :
    Functor.whiskerLeft (comparison P).rationalRealization (rationalComp a b).hom ≫
      (operation (composite l a b)).rational.hom =
    Functor.whiskerRight (operation a).rational.hom (operation b).modules.rational ≫
      Functor.whiskerLeft (operation a).raw (operation b).rational.hom ≫
      Functor.whiskerRight (rawComp a b).hom (comparison S).rationalRealization

end AlgebraicGeometry.ProEtale.CompletedLisse
