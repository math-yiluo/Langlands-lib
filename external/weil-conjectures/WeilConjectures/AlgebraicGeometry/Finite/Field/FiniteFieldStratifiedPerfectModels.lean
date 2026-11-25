/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Topology.Constructible
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations

import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSiteBoundedConstantModels
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Stratified perfect constant models over a finite field

Source: Bhatt--Scholze, The pro-etale topology for schemes, Proposition 6.6.11,
forward implication (residue stratification), and Proposition 6.8.11(3);
Stacks Project, Tags 095E, 03RZ and 094G
(blueprint: lem-weil-pbc-finite-field-stratified-perfect-models).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

private theorem commonStratification
    (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] [Finite k]
    (F : ℤ → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k))
    (hF : ∀ q, Scheme.IsConstructibleEtaleModuleSheaf (F q)) (s : Finset ℤ) :
    ∃ S : Scheme.Stratification X, ∀ q ∈ s, ∀ i : Fin S.n,
      Scheme.IsFiniteLocallyConstantSheaf
        ((Etale.upperStar (ModuleCat.{u + 1} k) (S.immersion i)).obj (F q)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      obtain ⟨S, _⟩ := hF 0
      exact ⟨S, by simp⟩
  | @insert q s hq ih =>
      obtain ⟨S, hS⟩ := ih
      obtain ⟨T, hT⟩ :=
        (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf (F q)).mp (hF q)
      refine ⟨S.inter T, ?_⟩
      intro r hr i
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact (S.inter_refines_right T).isFiniteLocallyConstantSheaf_upperStar (F r) hT i
      · exact (S.inter_refines_left T).isFiniteLocallyConstantSheaf_upperStar
          (F r) (hS r hr) i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteLocalModels
    {X : Scheme.{u}} (k : Type (u + 1)) [CommRing k] [Finite k]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k))
    [Scheme.IsFiniteLocallyConstantSheaf F] (V : X.Etale) :
    ∃ (I : Type (u + 1)) (U : I → X.Etale) (f : ∀ i, U i ⟶ V),
      Sieve.ofArrows U f ∈ X.smallEtaleTopology V ∧
      ∀ i, ∃ M : ModuleCat.{u + 1} k, Module.Finite k M ∧ Nonempty
        (F.over (U i) ≅
          (constantSheaf (X.smallEtaleTopology.over (U i)) (ModuleCat.{u + 1} k)).obj M) := by
  classical
  let A := ModuleCat.{u + 1} k
  have : Scheme.IsFiniteLocallyConstantSheaf ((Etale.upperStar A V.hom).obj F) :=
    Scheme.IsFiniteLocallyConstantSheaf.upperStar V.hom F
  obtain ⟨d, hd⟩ := (Scheme.finite_locally_constant_module_values_iff
    ((Etale.upperStar A V.hom).obj F)).1.mpr inferInstance
  let U (i : ULift.{u + 1, u} d.cover.I₀) : X.Etale :=
    Scheme.Etale.mk (d.cover.f i.down ≫ V.hom)
  let f (i : ULift.{u + 1, u} d.cover.I₀) : U i ⟶ V :=
    MorphismProperty.Over.homMk (d.cover.f i.down) rfl
  refine ⟨_, U, f, ?_, ?_⟩
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (f := f)).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, y, hy⟩ := d.cover.exists_eq x
    exact Set.mem_iUnion.mpr ⟨⟨i⟩, y, hy⟩
  · intro i
    obtain ⟨M, hM, ⟨e⟩⟩ := hd i.down
    have := hM
    refine ⟨M, Module.Finite.of_finite, ⟨?_⟩⟩
    let W := d.cover.etalePrecoverageToEtale i.down
    letI : (Scheme.Etale.overEquiv W).inverse.IsDenseSubsite
        W.left.smallEtaleTopology (V.left.smallEtaleTopology.over W) :=
      Scheme.Etale.overEquiv_inverse_isDenseSubsite W
    let E := Scheme.Etale.overSheafEquiv (U i) A
    let e' : (Etale.upperStar A (U i).hom).obj F ≅
        (constantSheaf (U i).left.smallEtaleTopology A).obj M :=
      (Etale.upperStarComp A (d.cover.f i.down) V.hom).app F ≪≫
        (Scheme.overSheafEquivFunctorObjOverIso A W _).symm ≪≫
        (Scheme.Etale.overSheafEquiv W A).functor.mapIso e ≪≫
        ((Scheme.Etale.overEquiv W).constantSheafSheafCongrIso
          (V.left.smallEtaleTopology.over W) W.left.smallEtaleTopology A
          CategoryTheory.Over.mkIdTerminal).app M
    exact E.functor.preimageIso
      (Scheme.overSheafEquivFunctorObjOverIso A (U i) F ≪≫ e' ≪≫
        (((Scheme.Etale.overEquiv (U i)).constantSheafSheafCongrIso
          (X.smallEtaleTopology.over (U i)) (U i).left.smallEtaleTopology A
          CategoryTheory.Over.mkIdTerminal).app M).symm)

private noncomputable def coefficientComparisonPullbackIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (k : Type (u + 1))
    [CommRing k] [Finite k] [TopologicalSpace k] [DiscreteTopology k] :
    finiteCoefficientComparison Y k ⋙ finiteCoefficientPullback Y k f ≅
      Etale.upperStar (ModuleCat.{u + 1} k) f ⋙ finiteCoefficientComparison X k :=
  (Functor.isoWhiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} k) Y)
    (Functor.isoWhiskerRight (finiteCoefficientRealization Y k).asEquivalence.unitIso.symm
      (upperStar (ModuleCat.{u + 1} k) f ⋙ finiteCoefficientRealization X k))) ≪≫
    Functor.isoWhiskerRight
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} k) f)
      (finiteCoefficientRealization X k)

private noncomputable def derivedCoefficientComparisonPullbackIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (k : Type (u + 1))
    [CommRing k] [Finite k] [TopologicalSpace k] [DiscreteTopology k] :
    finiteCoefficientDerivedComparison Y k ⋙ finiteCoefficientDerivedPullback Y k f ≅
      (Etale.upperStar (ModuleCat.{u + 1} k) f).mapDerivedCategory ⋙
        finiteCoefficientDerivedComparison X k :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (coefficientComparisonPullbackIso f k) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm

private noncomputable def comparisonConstantComplexIso
    (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] [Finite k]
    [TopologicalSpace k] [DiscreteTopology k]
    (P : CochainComplex (ModuleCat.{u + 1} k) ℤ) :
    (finiteCoefficientDerivedComparison X k).obj
      (DerivedCategory.Q.obj
        (((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) ≅
      (finiteCoefficientRealization X k).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          (((constantSheaf (Scheme.ProEt.topology X)
            (ModuleCat.{u + 1} k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm.app _ ≪≫
    (finiteCoefficientRealization X k).mapDerivedCategory.mapIso
      ((comparisonUpperStar (ModuleCat.{u + 1} k) X).mapDerivedCategoryFactors.app _ ≪≫
        DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
          (comparisonUpperStarConstantSheafIso k X) (ComplexShape.up ℤ)).app P))

/-- A bounded constructible etale complex over a finite field has, on an etale cover
of each constructible locally closed stratum, an actual bounded finite-dimensional
constant complex model. The same complex models its pro-etale comparison pullback,
in the continuous-function coefficient-ring presentation.

Source: Bhatt--Scholze, Proposition 6.6.11, forward implication, and 6.8.11(3);
Stacks Project, Tags 095E, 03RZ and 094G
(blueprint: lem-weil-pbc-finite-field-stratified-perfect-models).

Proof:
1. Choose cohomological bounds a <= b. Constructibility gives a finite stratification
for each of the finitely many cohomology degrees in this interval. Repeatedly use
lem-weil-pbc-constructible-stratification-intersection to obtain a common refinement,
using actual fibre products of stratum schemes and constructible intersections.
The first stratification starts the induction; empty fibre products may be retained.
2. Exact inverse image (situation-conventions) identifies homology
on a refined stratum with the inverse image of the original homology. Pull back each
trivializing etale cover along the refinement projection. The natural constant-module
comparison (lem-sfb-geometric-inverse-image-constant-module) preserves its finite values.
This works on every etale object of the stratum, and outside the bounds use zero.
3. Apply lem-weil-pbc-etale-site-bounded-constant-models, Stacks 094G, on each stratum.
It gives an etale cover and actual complexes of finite k-modules, zero outside [a,b],
whose constant differentials give the required derived models. A finite k-module is
finite-dimensional because its finite set of elements spans it.
4. Every k-vector space is projective (lem-weil-pbc-vector-space-projective). Thus
these bounded finite-dimensional complexes themselves witness IsPerfectRingComplex
(def-pc-perfect-ring-complex), including the zero complex and zero terms.
5. Put h = v followed by the stratum immersion. The canonical comparison-pullback
isomorphisms (proposition-comparison-etale-derived-category--5) commute inverse image with nu^*.
Exactness (lem-pe-constant-left-module-inverse-image) descends them termwise to derived
categories. The constant-preserving coefficient identification of
prop-weil-pbc-proetale-constant-ring-map is precisely the realization used by
finiteCoefficientDerivedComparison and finiteCoefficientDerivedPullback.
6. Apply nu^* to the etale model. Naturality in every module differential of
lem-sfb-geometric-inverse-image-constant-module gives the same constant complex on
the pro-etale site, not merely isomorphic graded objects. Realize it over the recorded
coefficient ring sheaf. Etale covers are pro-etale covers (lem-pur-etale-proetale-cover).
There is no integral lifting or completeness hypothesis; empty strata need no model. -/
theorem finite_field_stratified_perfect_models
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (k : Type (u + 1)) [Field k] [Finite k] [TopologicalSpace k] [DiscreteTopology k]
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)))
    (hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q → IsZero
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) q).obj L))
    (hconstructible : ∀ q : ℤ, Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) q).obj L)) :
    ∃ S : Scheme.FiniteLocallyClosedStratification X,
      (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
      ∀ i : Fin S.n, ∃ 𝒰 : Cover.{u} etalePrecoverage (S.domain i),
        ∀ j : 𝒰.I₀, ∃ (P : CochainComplex (ModuleCat.{u + 1} k) ℤ) (a b : ℤ),
          P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ q : ℤ, Module.Finite k (P.X q)) ∧
          @DerivedCategory.IsPerfectRingComplex k _ (HasDerivedCategory.standard _)
            ((@DerivedCategory.Q (ModuleCat.{u + 1} k) _ _
              (HasDerivedCategory.standard _)).obj P) ∧
          Nonempty
            ((Etale.upperStar (ModuleCat.{u + 1} k)
                (𝒰.f j ≫ S.immersion i)).mapDerivedCategory.obj L ≅
              DerivedCategory.Q.obj
                (((constantSheaf (𝒰.X j).smallEtaleTopology
                  (ModuleCat.{u + 1} k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ∧
          Nonempty
            ((finiteCoefficientDerivedPullback X k (𝒰.f j ≫ S.immersion i)).obj
                ((finiteCoefficientDerivedComparison X k).obj L) ≅
              (finiteCoefficientRealization (𝒰.X j) k).mapDerivedCategory.obj
                (DerivedCategory.Q.obj
                  (((constantSheaf (Scheme.ProEt.topology (𝒰.X j))
                    (ModuleCat.{u + 1} k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) := by
  classical
  obtain ⟨a, b, hab, hvan⟩ := hbounded
  let A := ModuleCat.{u + 1} k
  let H (q : ℤ) := (DerivedCategory.homologyFunctor
    (Sheaf X.smallEtaleTopology A) q).obj L
  obtain ⟨S, hS⟩ := commonStratification X k H hconstructible (Finset.Icc a b)
  let T : Scheme.FiniteLocallyClosedStratification X :=
    { n := S.n
      stratum := S.stratum
      isLocallyClosed_stratum := S.isLocallyClosed_stratum
      iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
      pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  refine ⟨T, S.isConstructible_stratum, ?_⟩
  intro i
  let F := Etale.upperStar A (S.immersion i)
  let K := F.mapDerivedCategory.obj L
  have hvanK (q : ℤ) (hq : q < a ∨ b < q) : IsZero
      ((DerivedCategory.homologyFunctor (Sheaf (S.domain i).smallEtaleTopology A) q).obj K) :=
    F.isZero_homologyFunctor_mapDerivedCategory_obj (hvan q hq)
  have hlocal (q : ℤ) : Scheme.IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor (Sheaf (S.domain i).smallEtaleTopology A) q).obj K) := by
    by_cases hq : q ∈ Finset.Icc a b
    · have : Scheme.IsFiniteLocallyConstantSheaf
          ((DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology A) q ⋙ F).obj L) :=
        hS q hq i
      exact Scheme.IsFiniteLocallyConstantSheaf.of_iso
        ((F.mapDerivedCategoryHomologyFunctorIso q).app L)
    · have hz := hvanK q (by simpa only [Finset.mem_Icc, not_and_or, not_le] using hq)
      exact Scheme.IsFiniteLocallyConstantSheaf.of_isZero hz
  obtain ⟨𝒰, h𝒰⟩ := Etale.etale_site_bounded_constant_models (S.domain i) k K a b hab
    hvanK (fun q V ↦ by
      have := hlocal q
      exact finiteLocalModels k _ V)
  refine ⟨𝒰, fun j ↦ ?_⟩
  obtain ⟨P, hfinite, hsupport, ⟨emodel⟩⟩ := h𝒰 j
  have hge : P.IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_iff P a).mpr (fun q hq ↦ hsupport q (.inl hq))
  have hle : P.IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_iff P b).mpr (fun q hq ↦ hsupport q (.inr hq))
  have hfin (q : ℤ) : Module.Finite k (P.X q) := by
    have := hfinite q
    exact Module.Finite.of_finite
  let e : (Etale.upperStar A (𝒰.f j ≫ S.immersion i)).mapDerivedCategory.obj L ≅
      DerivedCategory.Q.obj
        (((constantSheaf (𝒰.X j).smallEtaleTopology A).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
    (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp A (𝒰.f j)
      (S.immersion i))).app L ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm.app L ≪≫ emodel
  refine ⟨P, a, b, hge, hle, hfin, ?_, ⟨e⟩, ?_⟩
  · exact ⟨P, a, b, hge, hle, fun q ↦ ⟨inferInstance, hfin q⟩, ⟨Iso.refl _⟩⟩
  · exact ⟨(derivedCoefficientComparisonPullbackIso (𝒰.f j ≫ S.immersion i) k).app L ≪≫
      (finiteCoefficientDerivedComparison (𝒰.X j) k).mapIso e ≪≫
      comparisonConstantComplexIso (𝒰.X j) k P⟩

end AlgebraicGeometry.ProEtale
