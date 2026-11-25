/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousModuleEncodingUniverses
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModelOpenClosedBasic
public import WeilConjectures.AlgebraicGeometry.LatticePullbackProof.ContinuousCoefficientPullbackIsoSupplement
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientImmersionRestriction
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
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Mathlib.Topology.Connected.TotallyDisconnected
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
public import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteModelStratumFiltration
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Continuous coefficient filtrations with admissible strata

Source: Bhatt--Scholze, Definitions 6.8.3, 6.8.6 and 6.8.10, Lemma 6.8.13,
Proposition 6.8.14(2), and Lemma 6.8.2
(blueprint: lem-per-continuous-filtration-admissible-strata).

The compatible norm on a finite extension is its unique extended p-adic norm.
The continuous coefficient ring is the published lattice presentation
`ULift C(|U|, E)`, canonically the localization of the completed integral coefficients.
Open pieces use the actual slice restriction and extension-by-zero counit.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale
namespace ContinuousFiltration

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E]

/-- The tensor-formula continuous module inverse image, with the canonical coefficient map.
Source: Bhatt--Scholze, Definition 6.8.1 and Remark 6.8.15
(blueprint: lem-per-continuous-filtration-admissible-strata). -/
def pull {Y X : Scheme.{u}} (f : Y ⟶ X) :
    SheafOfModules.{u + 1} (latticeModuleRing X E) ⥤
      SheafOfModules.{u + 1} (latticeModuleRing Y E) :=
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  letI := LatticePullbackProof.continuousCoefficientInverseImageMap_isIso f E
  Scheme.proEtaleRingModulePullback f (latticeCoefficientSheaf X E)
    (latticeCoefficientSheaf Y E) (asIso (continuousCoefficientInverseImageMap f E))

/-- The open-support piece `v_!v^*`, in the canonical slice presentation of the open site.
Source: Stacks Tags 09BN and 03DI; Bhatt--Scholze, Lemma 6.8.13
(blueprint: lem-per-continuous-filtration-admissible-strata). -/
def piece {X : Scheme.{u}} (V : X.Opens) :=
  SheafOfModules.overFunctor.{u + 1} (latticeModuleRing X E) (Scheme.ProEt.mk V.ι) ⋙
    Scheme.proEtaleRingedExtensionByZero (Scheme.ProEt.mk V.ι) (latticeCoefficientSheaf X E)

/-- The actual extension-by-zero/restriction counit, without any chosen map into F.
Source: Stacks Tag 03DI; Bhatt--Scholze, Lemma 6.8.13
(blueprint: lem-per-continuous-filtration-admissible-strata). -/
def counit {X : Scheme.{u}} (V : X.Opens)
    (F : SheafOfModules.{u + 1} (latticeModuleRing X E)) :
    (piece E V).obj F ⟶ F := by
  classical
  refine (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (latticeModuleRing X E).obj)).symm ?_
  refine
    { app := fun _ => ModuleCat.ofHom
        (DirectSum.toModule _ _ _ (fun _ => LinearMap.id))
      naturality := ?_ }
  intro W W' f
  ext x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of φ x =>
    change (DirectSum.toModule _ _ _ (fun _ => LinearMap.id))
      (SheafOfModules.extensionByZeroPresheafRestrictAdd
        (latticeModuleRing X E) (Scheme.ProEt.mk V.ι)
        ((SheafOfModules.overFunctor _ _).obj F) f (DirectSum.of _ φ x)) =
      F.val.map f ((DirectSum.toModule _ _ _ (fun _ => LinearMap.id))
        (DirectSum.of _ φ x))
    dsimp only [SheafOfModules.extensionByZeroPresheafRestrictAdd]
    erw [DirectSum.toAddMonoid_of, DirectSum.toModule_lof, DirectSum.toModule_lof]
    rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Ordinary continuous closed direct image followed by continuous open extension by zero,
with the stratum object exactly the successive restriction of F.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks Tags 03D6 and 03DI
(blueprint: lem-per-continuous-filtration-admissible-strata). -/
def stratumPiece {X : Scheme.{u}} (V : X.Opens) {S : Scheme.{u}}
    (t : S ⟶ V.toScheme) (F : SheafOfModules.{u + 1} (latticeModuleRing X E)) :=
  (continuousModuleExtensionByZero (Scheme.ProEt.mk V.ι) E).obj
    ((continuousModuleDirectImage t E).obj
      ((pull l E t).obj ((pull l E V.ι).obj F)))

end ContinuousFiltration

/-- A rational constructible continuous module has an admissible finite open filtration.
The canonical section-action equivalence retains the underlying abelian sheaves, identifies
finite free scalar models, and intertwines locally closed restriction.
Source: Bhatt--Scholze, Definitions 6.8.3, 6.8.6 and 6.8.10, Lemma 6.8.13,
Proposition 6.8.14(2), and Lemma 6.8.2
(blueprint: lem-per-continuous-filtration-admissible-strata).

Proof plan, following the seven DAG steps:
1. `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` gives the Noetherian space.
The continuous realization and internal/sectionwise equivalence identify E-valued local
models with the finite constant models: e tensor (c_i) maps to (e*c_i), with inverse
(e_i) maps to the sum of e_i tensor the coordinate vectors. These formulas commute with
restriction and preserve the underlying abelian sheaves. The comparisons of
`lem-sfb-internal-module-operations-transport` carry each given stratum restriction and
its trivializing cover to the internal category, proving constructibility there.
2. Apply `lem-sfb-finite-model-stratum-filtration` to get ordered opens, their reduced
closed differences, qcqs open immersions, monic counits and successive quotients.
3. The field clause of `lem-sfb-scalar-finite-free-resolutions` gives a finite basis of
each scalar model. Tensor its coordinate isomorphism and inverse with the coefficient
ring. The restriction comparisons identify the resulting locally finite free L_k.
4. `lem-sfb-internal-module-operations-transport` preserves exactness and the actual
adjunction counits. With `lem-weil-pbc-proetale-ringed-open-closed` and the normalized
continuous coefficient restriction, it transports the internal filtration and cokernels
to the displayed sectionwise operations, retaining their underlying abelian sheaves.
5. `lem-weil-pbc-noetherian-open-subscheme-noetherian` gives Noetherian V_k. Affine
closed pieces have quotient rings of Noetherian rings, and are quasi-compact closed
subsets, so S_k is Noetherian as well (def-weil-pbc-noetherian-ring, pqf-def-locnoeth).
6. `lem-weil-pbc-open-subspace-dimension-monotone` bounds the dimension of each V_k.
Closed embeddings carry strict irreducible closed chains to such chains in V_k, so
also bound dim S_k. Open stalk identifications and local ring maps preserve the unit l.
7. For empty X take m=0; the empty-cover sheaf condition makes F zero. All inclusions
are non-strict and ranks may be zero, so zero objects and zero quotients are included. -/
theorem exists_continuousFiltration_admissibleStrata
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X]
    (_hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (F : SheafOfModules.{u + 1} (latticeModuleRing X E))
    (hF : ∃ s : X.FiniteLocallyClosedStratification, ∀ a : Fin s.n,
      ((ContinuousFiltration.pull l E (s.immersion a)).obj F).IsFiniteLocallyFree) :
    IsConstantModelConstructible (Profinite.continuousCoefficientRingObj E) X
      ((CondensedRing.continuousFieldModuleEquivalenceUniverse l E X).inverse.obj F) ∧
    (∀ T : Scheme.{u}, Nonempty
      ((CondensedRing.continuousFieldModuleEquivalenceUniverse l E T).functor ⋙
          SheafOfModules.toSheaf (latticeModuleRing T E) ≅
        Mod.forget (condensedRingObj (Profinite.continuousCoefficientRingObj E) T))) ∧
    (∀ (T : Scheme.{u}) (n : ℕ), Nonempty
      ((CondensedRing.continuousFieldModuleEquivalenceUniverse l E T).functor.obj
          (Mod.finiteFree (condensedRingObj (Profinite.continuousCoefficientRingObj E) T) n) ≅
        SheafOfModules.free (R := latticeModuleRing T E) (ULift.{u + 1} (Fin n)))) ∧
    (∀ (Y Z : Scheme.{u}) (i : Z ⟶ Y) [IsImmersion i], Nonempty
      (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj E) i ⋙
          (CondensedRing.continuousFieldModuleEquivalenceUniverse l E Z).functor ≅
        (CondensedRing.continuousFieldModuleEquivalenceUniverse l E Y).functor ⋙
          ContinuousFiltration.pull l E i)) ∧
    ∃ (m : ℕ) (V : Fin (m + 1) → X.Opens),
      Monotone V ∧ V 0 = ⊥ ∧ V (Fin.last m) = ⊤ ∧
      ∃ (S : Fin m → Scheme.{u}) (t : ∀ k : Fin m, S k ⟶ (V k.succ).toScheme),
        (∀ k : Fin m, IsClosedImmersion (t k) ∧ IsReduced (S k) ∧
          Set.range (t k) = {x | (V k.succ).ι x ∉ V k.castSucc}) ∧
        (∀ k : Fin (m + 1), IsNoetherian (V k).toScheme ∧
          topologicalKrullDim (V k).toScheme ≤ topologicalKrullDim X ∧
          (∀ x : (V k).toScheme, IsUnit (l : (V k).toScheme.presheaf.stalk x)) ∧
          QuasiCompact (V k).ι ∧ QuasiSeparated (V k).ι) ∧
        (∀ k : Fin m, IsNoetherian (S k) ∧
          topologicalKrullDim (S k) ≤ topologicalKrullDim X ∧
          (∀ x : S k, IsUnit (l : (S k).presheaf.stalk x)) ∧
          QuasiCompact ((V k.succ).ι ⁻¹ᵁ V k.castSucc).ι ∧
          QuasiSeparated ((V k.succ).ι ⁻¹ᵁ V k.castSucc).ι ∧
          ((ContinuousFiltration.pull l E (t k)).obj
            ((ContinuousFiltration.pull l E (V k.succ).ι).obj F)).IsFiniteLocallyFree) ∧
        (∀ k : Fin (m + 1), Mono (ContinuousFiltration.counit E (V k) F)) ∧
        IsZero ((ContinuousFiltration.piece E (V 0)).obj F) ∧
        IsIso (ContinuousFiltration.counit E (V (Fin.last m)) F) ∧
        ∃ d : ∀ k : Fin m,
          (ContinuousFiltration.piece E (V k.castSucc)).obj F ⟶
            (ContinuousFiltration.piece E (V k.succ)).obj F,
          (∀ k : Fin m, d k ≫ ContinuousFiltration.counit E (V k.succ) F =
            ContinuousFiltration.counit E (V k.castSucc) F) ∧
          (∀ k : Fin m, Mono (d k)) ∧
          (∀ k : Fin m, Nonempty
            (cokernel (d k) ≅ ContinuousFiltration.stratumPiece l E (V k.succ) (t k) F)) := by
  sorry

end AlgebraicGeometry.ProEtale
