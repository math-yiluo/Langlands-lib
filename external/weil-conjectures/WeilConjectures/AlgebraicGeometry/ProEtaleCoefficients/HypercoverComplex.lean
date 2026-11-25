/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.HypercoverExistence
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWContractibleSectionsDerived
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.EssentiallySmall
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import WeilConjectures.CategoryTheory.RingedHypercoverInjectiveAugmentationRing
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.Algebra.Exact.Basic
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.CategoryTheory.RingedHypercoverFiniteCones
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.Data.Fin.VecNotation
import WeilConjectures.Algebra.Homology.BoundedBelowAugmentation
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.BoundedBelowTotalComparison
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Algebra.Homology.KInjectiveResolution
import WeilConjectures.AlgebraicGeometry.ProEtale.Hypercover.ProEtaleHypercoverComputesBoundedComplexSupplement

/-!
# Derived abelian sections from a weakly contractible hypercover

The helpers realize the alternating section total for arbitrary ring sheaves.
The existing `hypercoverTotal` has commutative coefficients and a module-valued target.
Here all values and derived categories use the common larger coefficient universe;
the pro-etale site's object and morphism universes stay different.

## References

* Stacks Project, Tag 09A2, the construction of `s(E(K))`
* Stacks Project, Tag 09A2, construction of the total complex
-/

@[expose] public section

set_option autoImplicit false

universe t u v wA wB

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme.ProEt

private instance : Preadditive (CosimplicialObject AddCommGrpCat.{u}) :=
  inferInstanceAs (Preadditive (SimplexCategory ⥤ AddCommGrpCat.{u}))

/-- Cosimplicial underlying abelian sections, with the actual sheaf restriction maps. -/
noncomputable def hypercoverAbelianSections (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (U : X.ProEt)
    (W : SimplicialObject (Over U)) :
    ringedSiteModules.{max u v (t + 1)} R ⥤
      CosimplicialObject AddCommGrpCat.{max u v (t + 1)} :=
  SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj ⋙
    (Functor.whiskeringLeft _ _ _).obj (W ⋙ Over.forget U).rightOp

/-- The alternating section rows, extended by zero in negative simplicial degrees.
The differential from degree r to r+1 is the sum of `(-1)^i` times the i-th
face restriction, for i in `Fin (r+2)`. No hypercover condition enters this data. -/
noncomputable def hypercoverAbelianRows (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (U : X.ProEt)
    (W : SimplicialObject (Over U)) :
    ringedSiteModules.{max u v (t + 1)} R ⥤
      CochainComplex AddCommGrpCat.{max u v (t + 1)} ℤ :=
  hypercoverAbelianSections X R U W ⋙
    AlgebraicTopology.alternatingCofaceMapComplex _ ⋙
    ComplexShape.embeddingUpNat.extendFunctor _

/-- Additivity needed to apply the alternating section rows to a coefficient complex. -/
theorem hypercoverAbelianRows_additive (X : Scheme.{t})
    (R : Sheaf (topology X) RingCat.{u}) (U : X.ProEt)
    (W : SimplicialObject (Over U)) :
    (hypercoverAbelianRows.{t, u, v} X R U W).Additive := by
  let : (hypercoverAbelianSections.{t, u, v} X R U W).Additive :=
    { map_add := by intros; rfl }
  let : (AlgebraicTopology.alternatingCofaceMapComplex
      AddCommGrpCat.{max u v (t + 1)}).Additive := { map_add := by intros; rfl }
  unfold hypercoverAbelianRows
  infer_instance

attribute [instance] hypercoverAbelianRows_additive

variable (X : Scheme.{t}) (R : Sheaf (topology X) RingCat.{u})
  (U : X.ProEt) (W : SimplicialObject (Over U))

private instance hypercoverAbelianSections_additive :
    (hypercoverAbelianSections.{t, u, v} X R U W).Additive where
  map_add := by intros; rfl

private instance sectionEvaluation_additive (p : ℕ) :
    (hypercoverAbelianSections X R U W ⋙ (CategoryTheory.evaluation _ _).obj ⦋p⦌).Additive where
  map_add {_I _J} {f g} := congr_app
    ((hypercoverAbelianSections X R U W).map_add (f := f) (g := g)) ⦋p⦌

private instance sectionEvaluation_preservesZero (p : ℕ) :
    (hypercoverAbelianSections.{t, u, v} X R U W ⋙
      (CategoryTheory.evaluation _ _).obj ⦋p⦌).PreservesZeroMorphisms where
  map_zero := by intros; rfl

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `AddCommGrpCat.{max u v (t + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem sectionsEvaluation_preservesHomology (R : Sheaf (topology X) RingCat.{u})
    (p : ℕ)
    (hweak : (topology X).IsWeaklyContractible.{max u v (t + 1)} (W _⦋p⦌).left) :
    (hypercoverAbelianSections.{t, u, v} X R U W ⋙
      (CategoryTheory.evaluation _ _).obj ⦋p⦌).PreservesHomology := by
  let q : X.ProEt ≌ AsSmall.{max u v (t + 1)} X.ProEt := AsSmall.equiv
  let J := q.inverse.inducedTopology (topology X)
  have : HasSheafify (topology X) AddCommGrpCat.{max u v (t + 1)} :=
    q.hasSheafify (topology X) J _
  have : (topology X).WEqualsLocallyBijective AddCommGrpCat.{max u v (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.transport (topology X) J q.inverse
      (Functor.IsDenseSubsite.coverPreserving _ _ _)
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{max u v (t + 1)} R) :=
    (moduleSheaves_colimits_forgetful R).2.2.1
  let ev := SheafOfModules.evaluation.{max u v (t + 1)} R (op (W _⦋p⦌).left)
  have : ev.PreservesEpimorphisms := by
    constructor
    intro M N f hf
    let g := (SheafOfModules.toSheaf R).map f
    have : Epi g := inferInstance
    have : Sheaf.IsLocallySurjective g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u v (t + 1)} g).mpr
        inferInstance
    let g' := (sheafCompose (topology X)
      (CategoryTheory.forget AddCommGrpCat.{max u v (t + 1)})).map g
    have : Sheaf.IsLocallySurjective g' := inferInstance
    exact (ModuleCat.epi_iff_surjective (ev.map f)).mpr (hweak g' inferInstance)
  have : ev.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels ev
  have : PreservesFiniteLimits ev := Functor.preservesFiniteLimits_of_preservesHomology ev
  have : PreservesFiniteColimits ev := Functor.preservesFiniteColimits_of_preservesHomology ev
  let G := forget₂
    (ModuleCat.{max u v (t + 1)} (R.obj.obj (op (W _⦋p⦌).left)))
      AddCommGrpCat.{max u v (t + 1)}
  have : PreservesColimits G :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max u v (t + 1), u,
      max u v (t + 1), max u v (t + 1)} (R.obj.obj (op (W _⦋p⦌).left))
  change (ev ⋙ G).PreservesHomology
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sectionColumnIso
    (E : CochainComplex (ringedSiteModules.{max u v (t + 1)} R) ℤ) (p : ℕ) :
    (HomologicalComplex₂.flip
      (((hypercoverAbelianRows X R U W).mapHomologicalComplex (.up ℤ)).obj E)).X (p : ℤ) ≅
      (((hypercoverAbelianSections X R U W ⋙
        (CategoryTheory.evaluation _ _).obj ⦋p⦌).mapHomologicalComplex
        (.up ℤ)).obj E) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun q ↦
    (((AlgebraicTopology.alternatingCofaceMapComplex _).obj
      ((hypercoverAbelianSections X R U W).obj (E.X q))).extendXIso
        ComplexShape.embeddingUpNat (i := p) rfl)) ?_
  intro q r h
  symm
  change ((ComplexShape.embeddingUpNat.extendFunctor _).map
    ((AlgebraicTopology.alternatingCofaceMapComplex _).map
      ((hypercoverAbelianSections X R U W).map (E.d q r)))).f (p : ℤ) ≫ _ = _
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := p) rfl]
  simp

private theorem sectionBicomplex_zero
    (E : CochainComplex (ringedSiteModules.{max u v (t + 1)} R) ℤ)
    (N : ℤ) [E.IsStrictlyGE N] (p q : ℤ) (h : p < 0 ∨ q < N) :
    IsZero (((HomologicalComplex₂.flip
      (((hypercoverAbelianRows X R U W).mapHomologicalComplex (.up ℤ)).obj E)).X p).X q) := by
  change IsZero (((hypercoverAbelianRows X R U W).obj (E.X q)).X p)
  rcases h with hp | hq
  · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p (by
      intro i hi
      change (i : ℤ) = p at hi
      omega)
  · exact (HomologicalComplex.eval _ _ p).map_isZero
      ((hypercoverAbelianRows X R U W).map_isZero (E.isZero_of_isStrictlyGE N q hq))

-- Comparing section-column maps unfolds the section and extension functor compositions.
-- The comparison expands the evaluation, single-complex and section functors.
-- Transporting the site unfolds pushforward, restriction of scalars and extension functors.
-- The unit comparisons expand the resolution and localization functor compositions.
end AlgebraicGeometry.Scheme.ProEt
