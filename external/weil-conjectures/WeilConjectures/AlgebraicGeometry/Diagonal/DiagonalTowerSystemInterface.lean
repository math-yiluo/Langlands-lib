/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionSiteComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
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
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Adjunction

import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth

/-!
# The diagonal class in the derived category of strict torsion towers

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-system.md (blueprint: proposition-ell-adic-cycle-class-diagonal).
The index n denotes exponent n+1. Fixed-scalar module sheaves present modules over
constant ring sheaves; the underlying integer category is abelian sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u uA uB vA vB wA wS w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- Integral sheaves. Source: blueprint clause 1
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
abbrev DiagonalAb (W : Scheme.{u}) := Sheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}

/-- Discrete constant Z_l-module sheaves, not continuous-function coefficient sheaves.
Source: blueprint tower category (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
abbrev DiagonalMod (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :=
  Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))

/-- Strict inverse systems. Source: blueprint tower category
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
abbrev DiagonalSystems (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :=
  ℕᵒᵖ ⥤ DiagonalMod ℓ W

/-- The canonical abelian structure, named once to share all its sheafification
witnesses throughout the strict-system specification. This is the existing Mathlib
structure, with no choice of a replacement category.
Source: blueprint coefficient conventions (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
instance (priority := 2000) diagonalModuleSheafAbelian
    (A : Type (u + 1)) [CommRing A] (W : Scheme.{u}) :
    Abelian (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} A)) :=
  { (inferInstance : Abelian (Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} A))) with
    toPreadditive := Preadditive.fullSubcategory _ }

/-- The canonical abelian-sheaf structure, with its witnesses shared by name.
Source: blueprint coefficient conventions (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
instance (priority := 2000) diagonalAbSheafAbelian (W : Scheme.{u}) :
    Abelian (DiagonalAb W) :=
  { (inferInstance : Abelian (DiagonalAb W)) with
    toPreadditive := Preadditive.fullSubcategory _ }

/-- Ordinary extension from abelian groups to Z_l, before reduction, sheafified
sectionwise. Source: blueprint clause 2 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalScalarExtension (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    DiagonalAb W ⥤ DiagonalMod ℓ W :=
  sheafToPresheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringRight W.ProEtᵒᵖ AddCommGrpCat.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))).obj
        ((forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
          ModuleCat.extendScalars (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))) ⋙
    presheafToSheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))

/-- Forget scalars through the unique integer action.
Source: blueprint clause 2 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalForget (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    DiagonalMod ℓ W ⥤ DiagonalAb W :=
  sheafCompose (Scheme.ProEt.topology W)
    (ModuleCat.restrictScalars (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ])) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})

/-- The usual insertion-of-one scalar adjunction, lifted to sheaves.
Source: blueprint clause 2 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalScalarAdjunction (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    diagonalScalarExtension ℓ W ⊣ diagonalForget ℓ W :=
  Sheaf.adjunction (Scheme.ProEt.topology W)
    ((forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence.symm.toAdjunction.comp
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1}
        (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))))

/-- Forgetting constant scalars is exact.
Source: blueprint clause 2 (blueprint: proposition-ell-adic-cycle-class-diagonal).
Proof: kernels are sectionwise; cokernels are sheafifications of the same additive
quotients. The unique integer action changes neither construction. -/
theorem diagonalForget_exact (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits (diagonalForget ℓ W) ∧
      PreservesFiniteColimits (diagonalForget ℓ W) := by
  constructor
  · have := (diagonalScalarAdjunction ℓ W).rightAdjoint_preservesLimits
    infer_instance
  · let G := ModuleCat.restrictScalars
        (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ])) ⋙
        forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
    have : (ModuleCat.restrictScalars.{u + 1}
        (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, 0, u + 1}
        (Int.castRingHom (ULift.{u + 1} ℤ_[ℓ]))).isLeftAdjoint
    have : G.IsLeftAdjoint := inferInstance
    let J := Scheme.ProEt.topology W
    let e : Sheaf.composeAndSheafify J G ≅ sheafCompose J G :=
      Functor.isoWhiskerLeft (sheafCompose J G)
        (sheafificationNatIso J AddCommGrpCat.{u + 1}).symm ≪≫
        Functor.rightUnitor (sheafCompose J G)
    have : (Sheaf.composeAndSheafify J G).IsLeftAdjoint := inferInstance
    have : (sheafCompose J G).IsLeftAdjoint := Functor.isLeftAdjoint_of_iso e
    exact inferInstanceAs (PreservesFiniteColimits (sheafCompose J G))

/-- Exact scalar forgetting, limits. Source: blueprint clause 2
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
instance diagonalForgetLimits (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits (diagonalForget ℓ W) := (diagonalForget_exact ℓ W).1

/-- Exact scalar forgetting, colimits. Source: blueprint clause 2
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
instance diagonalForgetColimits (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteColimits (diagonalForget ℓ W) := (diagonalForget_exact ℓ W).2

/-- Additivity of scalar forgetting. Source: blueprint clause 2
(blueprint: proposition-ell-adic-cycle-class-diagonal).
Proof: the underlying section maps add pointwise and forgetting retains them. -/
theorem diagonalForget_additive (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    (diagonalForget ℓ W).Additive := by
  dsimp only [diagonalForget, sheafCompose]
  infer_instance

attribute [instance] diagonalForget_additive

/-- A strict ordinary reduction functor, characterized by its quotient universal
properties and quotient transitions. With L=extension to Z_l this is tensor with the
whole coefficient system; with L=identity this is its integral version.
Source: blueprint clause 2 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
structure DiagonalReductionPresentation
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] (L : A ⥤ B) where
  /-- One functor into the strict system category. -/
  E : A ⥤ (ℕᵒᵖ ⥤ B)
  /-- Termwise tensor is additive. -/
  [additive : E.Additive]
  /-- Quotient of extension by the positive prime power. -/
  π : ∀ n : ℕ, L ⟶ E ⋙ (evaluation ℕᵒᵖ B).obj (op n)
  /-- Its kernel relation. -/
  zero : ∀ (n : ℕ) (M : A),
    (ℓ ^ (n + 1) • 𝟙 (L.obj M)) ≫ (π n).app M = 0
  /-- The quotient is a cokernel, fixing its scalar action and maps. -/
  quotient : ∀ (n : ℕ) (M : A),
    IsColimit (CokernelCofork.ofπ ((π n).app M) (zero n M))
  /-- The transitions are the coefficient quotient maps, not independent level maps. -/
  transition : ∀ (n : ℕ) (M : A),
    (π (n + 1)).app M ≫ (E.obj M).map (homOfLE (Nat.le_succ n)).op = (π n).app M

attribute [instance] DiagonalReductionPresentation.additive

/-- The everywhere-defined left derived functor of a strict reduction presentation.
The universal counit and pointwise condition retain functoriality on all unbounded
complexes. Source: blueprint clause 2 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
structure DiagonalDerivedReduction
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] (L : A ⥤ B)
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wS} (ℕᵒᵖ ⥤ B)] where
  /-- The ordinary simultaneous reduction. -/
  ordinary : DiagonalReductionPresentation ℓ L
  /-- Its left derived functor, valued in the derived category of strict systems. -/
  T : DerivedCategory A ⥤ DerivedCategory (ℕᵒᵖ ⥤ B)
  /-- Universal comparison with termwise scalar tensor. -/
  ε : DerivedCategory.Q ⋙ T ⟶ ordinary.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  /-- The left derived universal property determines T. -/
  universal : T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))
  /-- It exists pointwise at every complex. -/
  pointwise :
    (ordinary.E.mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q).HasPointwiseLeftDerivedFunctor (HomologicalComplex.quasiIso A (.up ℤ))
  /-- Exactness, including its shift comparison. -/
  triangulated : ∃ (_ : T.CommShift ℤ), T.IsTriangulated

/-- The source identification is the universal derived counit on a degree-zero
flat supported constant, with the standard single-complex comparisons.
Source: blueprint clause 3 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalDerivedSingleCounit
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] (L : A ⥤ B)
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wS} (ℕᵒᵖ ⥤ B)]
    (D : DiagonalDerivedReduction ℓ L) (M : A) :
    D.T.obj ((DerivedCategory.singleFunctor A 0).obj M) ⟶
      (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj (D.ordinary.E.obj M) :=
  D.T.map ((DerivedCategory.singleFunctorIsoCompQ A 0).hom.app M) ≫
    D.ε.app ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex D.ordinary.E (.up ℤ) 0).hom.app M) ≫
    (DerivedCategory.singleFunctorIsoCompQ (ℕᵒᵖ ⥤ B) 0).inv.app (D.ordinary.E.obj M)

/-- The positive-exponent finite coefficient ring, lifted to the sheaf universe.
Source: blueprint clauses 3--4 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
abbrev diagonalResidue (ℓ n : ℕ) := cartierResidueRing.{u} ℓ (n + 1)

/-- The coefficient projection from Z_l to the lifted finite ring.
Source: blueprint clauses 2--4 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalResidueProjection (ℓ n : ℕ) [Fact ℓ.Prime] :
    ULift.{u + 1} ℤ_[ℓ] →+* diagonalResidue.{u} ℓ n :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((PadicInt.toZModPow (n + 1)).comp ULift.ringEquiv.toRingHom)

/-- A finite-coefficient module, read as a Z_l-module through the specified projection.
Source: blueprint clause 4 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalFiniteToPadic (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)) ⥤
      DiagonalMod ℓ W :=
  sheafCompose (Scheme.ProEt.topology W)
    (ModuleCat.restrictScalars (diagonalResidueProjection.{u} ℓ n))

/-- Finite coefficient restriction is exact and additive.
Source: blueprint clause 4 (blueprint: proposition-ell-adic-cycle-class-diagonal).
Proof: the underlying abelian kernels and sheafified cokernels are unchanged;
restriction retains every additive section map. -/
theorem diagonalFiniteToPadic_exact (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits (diagonalFiniteToPadic ℓ n W) ∧
    PreservesFiniteColimits (diagonalFiniteToPadic ℓ n W) ∧
    (diagonalFiniteToPadic ℓ n W).Additive := by
  constructor
  · have := (Sheaf.adjunction (Scheme.ProEt.topology W)
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        (diagonalResidueProjection.{u} ℓ n))).rightAdjoint_preservesLimits
    exact inferInstanceAs (PreservesFiniteLimits
      (sheafCompose (Scheme.ProEt.topology W)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (diagonalResidueProjection.{u} ℓ n))))
  constructor
  · let q := diagonalResidueProjection.{u} ℓ n
    have hadj := ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} q
    have : PreservesLimitsOfSize.{u, u + 1}
        (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} q) :=
      hadj.rightAdjoint_preservesLimits
    have : (Scheme.ProEt.topology W).HasSheafCompose
        (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} q) :=
      hasSheafCompose_of_preservesLimitsOfSize _
    have := (Sheaf.adjunction (Scheme.ProEt.topology W) hadj).isLeftAdjoint
    let J := Scheme.ProEt.topology W
    let G := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q
    let e : Sheaf.composeAndSheafify J G ≅ sheafCompose J G :=
      Functor.isoWhiskerLeft (sheafCompose J G)
        (sheafificationNatIso J (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[ℓ]))).symm ≪≫
        Functor.rightUnitor (sheafCompose J G)
    exact preservesFiniteColimits_of_natIso e
  · dsimp only [diagonalFiniteToPadic, sheafCompose]
    infer_instance

/-- Exact restriction, limits. Source: blueprint clause 4
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
instance diagonalFiniteToPadicLimits (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteLimits (diagonalFiniteToPadic ℓ n W) :=
  (diagonalFiniteToPadic_exact ℓ n W).1

/-- Exact restriction, colimits. Source: blueprint clause 4
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
instance diagonalFiniteToPadicColimits (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    PreservesFiniteColimits (diagonalFiniteToPadic ℓ n W) :=
  (diagonalFiniteToPadic_exact ℓ n W).2.1

/-- Additive restriction. Source: blueprint clause 4
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
instance diagonalFiniteToPadicAdditive (ℓ n : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :
    (diagonalFiniteToPadic ℓ n W).Additive :=
  (diagonalFiniteToPadic_exact ℓ n W).2.2

/-- The product of two projective lines. Source: blueprint opening
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
abbrev diagonalSurface (Y : Scheme.{u}) :=
  pullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)

/-- The diagonal. Source: blueprint opening
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
abbrev diagonalImmersion (Y : Scheme.{u}) : ProjectiveLine Y ⟶ diagonalSurface Y :=
  pullback.diagonal (ProjectiveLine Y ↘ Y)

/-- The diagonal of the separated projective line is closed.
Source: blueprint step 1 (blueprint: def-sfb-diagonal-system-interface). -/
instance diagonalImmersionClosed (Y : Scheme.{u}) :
    IsClosedImmersion (diagonalImmersion Y) := by
  change IsClosedImmersion (pullback.diagonal (ProjectiveLine Y ↘ Y))
  infer_instance

/-- The diagonal is Cartier over every base, including the empty base.
Source: blueprint proof step 1 (blueprint: proposition-ell-adic-cycle-class-diagonal).
Proof: the first projection of the surface is smooth of relative dimension one,
as a base change of the projective line. Its composite with the diagonal is the
identity. The closed subscheme defined by the kernel of the diagonal is isomorphic
to the diagonal, so its projection is an isomorphism, hence finite, flat and locally
of finite presentation. The relative Cartier criterion gives the invertible ideal. -/
theorem diagonalImmersion_cartier (Y : Scheme.{u}) :
    (diagonalImmersion Y).ker.IsInvertible := by
  let d := diagonalImmersion Y
  let p := pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)
  have : IsClosedImmersion d := diagonalImmersionClosed Y
  have : SmoothOfRelativeDimension 1 p :=
    smoothOfRelativeDimension_pullback_fst 1 _ _
  let j := d.ker.subschemeι
  have hker : d.ker = j.ker := by simp [j]
  let e := IsClosedImmersion.lift d j hker.le
  have : IsIso e := IsClosedImmersion.isIso_lift d j hker
  have he : e ≫ d = j := IsClosedImmersion.lift_fac d j hker.le
  have hp : j ≫ p = e := by
    rw [← he, Category.assoc]
    simp [d, p, diagonalImmersion]
  have : IsIso (j ≫ p) := hp.symm ▸ inferInstance
  exact Scheme.IdealSheafData.isInvertible_of_isFinite_of_flat p
    (J := d.ker)
      (by change IsFinite (j ≫ p); rw [hp]; exact MorphismProperty.of_isIso @IsFinite e)
      (by change Flat (j ≫ p); rw [hp]; exact MorphismProperty.of_isIso @Flat e)
      (by change LocallyOfFinitePresentation (j ≫ p); rw [hp]; infer_instance)

/-- Invertibility pulls from the base to the diagonal surface and all powers.
Source: blueprint standing hypothesis (blueprint: proposition-ell-adic-cycle-class-diagonal).
Proof: apply the ring map of global sections for W→Y to the given unit, then take
its positive power. This also applies to the zero ring of the empty scheme. -/
theorem diagonalSurface_power_unit (ℓ : ℕ) (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤))) (n : ℕ) :
    IsUnit ((ℓ ^ (n + 1) : ℕ) : Γ(diagonalSurface Y, ⊤)) := by
  let f : diagonalSurface Y ⟶ Y :=
    pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) ≫
      (ProjectiveLine Y ↘ Y)
  simpa using (hY.map f.appTop.hom).pow (n + 1)

/-- The supported integral constant on the pro-etale site.
Source: blueprint clause 1 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
abbrev diagonalIntegralSource (Y : Scheme.{u}) :=
  (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y)).obj
    ((constantSheaf (Scheme.ProEt.topology (ProjectiveLine Y)) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- Units mean exact comparison pullback of etale units.
Source: blueprint clause 1 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
abbrev diagonalComparisonUnits (Y : Scheme.{u}) :=
  (comparisonUpperStar AddCommGrpCat.{u + 1} (diagonalSurface Y)).obj
    (diagonalSurface Y).gmSheaf

/-- Transport an integral extension along an exact functor and a source isomorphism.
Source: naturality of Ext (blueprint: def-sfb-diagonal-system-interface). -/
def transportBoundarySource
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasExt.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{wS} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S U : A} {Q : B} (a : F.obj S ≅ Q) (δ : Ext S U 1) : Ext Q (F.obj U) 1 :=
  (Ext.mk₀ a.inv).comp (δ.mapExactFunctor F) (zero_add 1)

/-- The positive roof boundary: Ext uses the negative cone projection, so negate it.
This is the roof with [G_m→M] in degrees -1,0, quotient on the left and positive
projection on the right. The pole extension sends t inverse to +1.
Source: blueprint clause 1 and proof steps 1--2
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def diagonalIntegralBoundary (Y : Scheme.{u}) :
    Ext (diagonalIntegralSource Y) (diagonalComparisonUnits Y) 1 :=
  -(transportBoundarySource (comparisonUpperStar AddCommGrpCat.{u + 1} (diagonalSurface Y))
    (cartierIntegralSourceIso (diagonalImmersion Y))
    (Etale.cartierPoleBoundary (diagonalImmersion Y) (diagonalImmersion_cartier Y)))

/-- The integral derived-completion formula, with both inverse limits total right
derived functors on strict systems. The integral reduction is independently fixed by
the cokernels of l^(n+1) on the identity functor. Thus its composite with integral
Rlim is exactly Rlim_n(K tensor^L Z/l^(n+1)). The displayed natural isomorphism
retains the comparison after forgetting the constant Z_l action. In addition the
output is right orthogonal to every complex on which l is invertible, the intrinsic
derived l-completeness criterion. The natural unit is universal for maps to all
such complete complexes, so this asserts derived completion, not just a limit formula.
Source: blueprint clause 2 and Stacks 099M, 091S and 091Z
(blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def DiagonalCompletionSpec (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W)) : Prop :=
  ∃ (I : DiagonalDerivedReduction ℓ (𝟭 (DiagonalAb W)))
    (RF : DerivedCategory (DiagonalSystems ℓ W) ⥤ DerivedCategory (DiagonalMod ℓ W))
    (η : (lim : DiagonalSystems ℓ W ⥤ DiagonalMod ℓ W).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (RZ : DerivedCategory (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DerivedCategory (DiagonalAb W))
    (ηZ : (lim : (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DiagonalAb W).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RZ),
    RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso (DiagonalSystems ℓ W) (.up ℤ)) ∧
    RZ.IsRightDerivedFunctor ηZ
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ DiagonalAb W) (.up ℤ)) ∧
    Nonempty (D.T ⋙ RF ⋙ (diagonalForget ℓ W).mapDerivedCategory ≅ I.T ⋙ RZ) ∧
    ∃ unit : 𝟭 (DerivedCategory (DiagonalAb W)) ⟶
        D.T ⋙ RF ⋙ (diagonalForget ℓ W).mapDerivedCategory,
      (∀ (K P : DerivedCategory (DiagonalAb W)), IsIso (ℓ • 𝟙 P) →
        Subsingleton (P ⟶ (D.T ⋙ RF ⋙ (diagonalForget ℓ W).mapDerivedCategory).obj K)) ∧
      ∀ (K N : DerivedCategory (DiagonalAb W)),
        (∀ P : DerivedCategory (DiagonalAb W), IsIso (ℓ • 𝟙 P) → Subsingleton (P ⟶ N)) →
        Function.Bijective (fun f :
          (D.T ⋙ RF ⋙ (diagonalForget ℓ W).mapDerivedCategory).obj K ⟶ N ↦
            unit.app K ≫ f)

/-- The levelwise finite-source comparison preserves the quotient unit, not an
arbitrary automorphism of the supported constant.
Source: blueprint clauses 3--4 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def DiagonalSourceNormalization (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (D : DiagonalReductionPresentation ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (n : ℕ)
    (s : (D.E.obj (diagonalIntegralSource Y)).obj (op n) ≅
      (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
        ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)) (diagonalImmersion Y)).obj
          (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y)))) : Prop :=
  HEq
    ((diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
      (diagonalForget ℓ (diagonalSurface Y)).map ((D.π n).app (diagonalIntegralSource Y) ≫
        s.hom))
    (cartierProIntegralGenerator (diagonalResidue.{u} ℓ n) (diagonalImmersion Y))

attribute [local irreducible] CategoryTheory.Abelian.Ext
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  transportBoundarySource
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierEtaleKummerUnit cartierProKummerUnit cartierProIntegralGenerator cartierProRootMap
  cartierReducedEtale cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierResidueReducedPro diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The normalized Kummer target of a boundary with a fixed source identification.
Source: diagonal proof steps 5--7 (blueprint: def-sfb-diagonal-system-interface). -/
def normalizedBoundaryTarget
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A] [HasExt.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{w} B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (L : A ⥤ B) (F : B ⥤ A) (D : DiagonalDerivedReduction ℓ L)
    (S U : A) (δ : Ext S U 1) (rootsTower : ℕᵒᵖ ⥤ A) (Q R : ℕ → B)
    (sourceNorm : ∀ n, ((D.ordinary.E.obj S).obj (op n) ≅ Q n) → Prop)
    (rootNorm : ∀ (H : ℕᵒᵖ ⥤ B), (H ⋙ F ≅ rootsTower) →
      ∀ n, (H.obj (op n) ≅ R n) → Prop)
    (finiteClass : ∀ n, Ext (Q n) (R n) 2 → Prop)
    (a : D.T.obj ((DerivedCategory.singleFunctor A 0).obj S) ≅
      (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj (D.ordinary.E.obj S)) : Prop :=
  ∃ (H : ℕᵒᵖ ⥤ B) (roots : H ⋙ F ≅ rootsTower)
    (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj U)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧),
    ∀ n, ∃ (s : (D.ordinary.E.obj S).obj (op n) ≅ Q n)
      (t : H.obj (op n) ≅ R n),
      sourceNorm n s ∧ rootNorm H roots n t ∧
      finiteClass n ((Ext.mk₀ s.inv).comp
        (((Ext.homEquiv.symm (a.inv ≫ D.T.map δ.hom ≫ b.hom)).mapExactFunctor
          ((evaluation ℕᵒᵖ B).obj (op n))).comp
          (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2))

/-- Abstract simultaneous boundary with specified normalized finite evaluations.
Source: diagonal clauses 3--4 (blueprint: def-sfb-diagonal-system-interface). -/
def normalizedBoundarySystem
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A] [HasExt.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{w} B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (L : A ⥤ B) (F : B ⥤ A) (D : DiagonalDerivedReduction ℓ L)
    (S U : A) (δ : Ext S U 1) (rootsTower : ℕᵒᵖ ⥤ A) (Q R : ℕ → B)
    (sourceNorm : ∀ n, ((D.ordinary.E.obj S).obj (op n) ≅ Q n) → Prop)
    (rootNorm : ∀ (H : ℕᵒᵖ ⥤ B), (H ⋙ F ≅ rootsTower) →
      ∀ n, (H.obj (op n) ≅ R n) → Prop)
    (finiteClass : ∀ n, Ext (Q n) (R n) 2 → Prop) : Prop :=
  ∃ (H : ℕᵒᵖ ⥤ B) (roots : H ⋙ F ≅ rootsTower)
    (a : D.T.obj ((DerivedCategory.singleFunctor A 0).obj S) ≅
      (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj (D.ordinary.E.obj S))
    (b : D.T.obj (((DerivedCategory.singleFunctor A 0).obj U)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ B) 0).obj H)⟦(2 : ℤ)⟧)
    (c : Ext (D.ordinary.E.obj S) H 2),
    a.hom = diagonalDerivedSingleCounit ℓ L D S ∧
    c.hom = a.inv ≫ D.T.map δ.hom ≫ b.hom ∧
    ∀ n, ∃ (s : (D.ordinary.E.obj S).obj (op n) ≅ Q n)
      (t : H.obj (op n) ≅ R n),
      sourceNorm n s ∧ rootNorm H roots n t ∧
      finiteClass n ((Ext.mk₀ s.inv).comp
        ((c.mapExactFunctor ((evaluation ℕᵒᵖ B).obj (op n))).comp
          (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2))

/-- Eliminating the uniquely determined Ext class preserves the system assertion.
Source: the Ext/Hom equivalence (blueprint: def-sfb-diagonal-system-interface). -/
theorem normalizedBoundarySystem_iff_target
    (ℓ : ℕ) {A : Type uA} [Category.{vA} A] [Abelian A] [HasExt.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{w} B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (L : A ⥤ B) (F : B ⥤ A) (D : DiagonalDerivedReduction ℓ L)
    (S U : A) (δ : Ext S U 1) (rootsTower : ℕᵒᵖ ⥤ A) (Q R : ℕ → B)
    (sourceNorm : ∀ n, ((D.ordinary.E.obj S).obj (op n) ≅ Q n) → Prop)
    (rootNorm : ∀ (H : ℕᵒᵖ ⥤ B), (H ⋙ F ≅ rootsTower) →
      ∀ n, (H.obj (op n) ≅ R n) → Prop)
    (finiteClass : ∀ n, Ext (Q n) (R n) 2 → Prop) :
    normalizedBoundarySystem ℓ L F D S U δ rootsTower Q R
      sourceNorm rootNorm finiteClass ↔
      ∃ a, a.hom = diagonalDerivedSingleCounit ℓ L D S ∧
        normalizedBoundaryTarget ℓ L F D S U δ rootsTower Q R
          sourceNorm rootNorm finiteClass a := by
  constructor
  · rintro ⟨H, roots, a, b, c, ha, hc, hn⟩
    refine ⟨a, ha, H, roots, b, ?_⟩
    have he : c = Ext.homEquiv.symm (a.inv ≫ D.T.map δ.hom ≫ b.hom) :=
      Ext.homEquiv.injective (hc.trans (Ext.homEquiv.apply_symm_apply _).symm)
    simpa only [← he] using hn
  · rintro ⟨a, ha, H, roots, b, hn⟩
    refine ⟨H, roots, a, b, Ext.homEquiv.symm (a.inv ≫ D.T.map δ.hom ≫ b.hom),
      ha, ?_, hn⟩
    exact Ext.homEquiv.apply_symm_apply _

/-- The usual exact-functor image of an Ext class, with its interfaces shared.
Source: exact functoriality of Ext (blueprint: def-sfb-diagonal-system-interface). -/
def exactFunctorExtImage
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasExt.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasExt.{wS} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S U : A} {n : ℕ} (δ : Ext S U n) : Ext (F.obj S) (F.obj U) n :=
  δ.mapExactFunctor F

/-- The actual diagonal endpoints and normalizations for simultaneous Kummer reduction.
Source: diagonal clauses 3--4 (blueprint: def-sfb-diagonal-system-interface). -/
def diagonalBoundaryTarget (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y))) :
    Prop :=
  normalizedBoundaryTarget ℓ (diagonalScalarExtension ℓ (diagonalSurface Y))
    (diagonalForget ℓ (diagonalSurface Y)) D
    (diagonalIntegralSource Y) (diagonalComparisonUnits Y) (diagonalIntegralBoundary Y)
    (Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime))
    (fun n ↦ (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
      ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)) (diagonalImmersion Y)).obj
        (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y))))
    (fun n ↦ (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
      (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
        (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)))
    (DiagonalSourceNormalization ℓ Y D.ordinary)
    (fun _H roots n t ↦ HEq ((diagonalForget ℓ (diagonalSurface Y)).map t.hom)
      (roots.hom.app (op n) ≫
        cartierProRootMap (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
          (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)
          (pow_pos (Fact.out : ℓ.Prime).pos _) (diagonalSurface_power_unit ℓ Y hY n)))
    (fun n e ↦ HEq e
      (exactFunctorExtImage (diagonalFiniteToPadic ℓ n (diagonalSurface Y))
        (cartierResidueReducedPro ℓ (Fact.out : ℓ.Prime) (n + 1) (diagonalImmersion Y)
          (diagonalImmersion_cartier Y) (diagonalSurface_power_unit ℓ Y hY n)))) a

/-- A single arrow in D(strict systems), its prescribed source and target, and its
finite cycle-class identifications. Ext^2 is used only as the standard homEquiv
presentation of a morphism from a degree-zero system to a system shifted by two.
Source: blueprint clauses 3--4 (blueprint: proposition-ell-adic-cycle-class-diagonal). -/
def DiagonalCycleSystemSpec (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y))) : Prop :=
  ∃ a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)),
    a.hom = diagonalDerivedSingleCounit ℓ
      (diagonalScalarExtension ℓ (diagonalSurface Y)) D (diagonalIntegralSource Y) ∧
    diagonalBoundaryTarget ℓ Y hY D a

end AlgebraicGeometry.ProEtale
