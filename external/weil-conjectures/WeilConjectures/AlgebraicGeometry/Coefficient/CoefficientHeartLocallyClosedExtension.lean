/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction

/-!
# Exact locally closed extension of condensed coefficient modules

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-coefficient-heart,
introductory closure-factorization paragraph and proof paragraphs (1), (3);
Stacks Project, Tags 09BM, 03DJ, 010N, 015F
(blueprint: lem-sfb-coefficient-heart-locally-closed-extension).

The functor is the existing canonical open extension into the scheme-theoretic image
followed by its closed direct image. Cohomology comparisons are natural in complexes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- All locally closed subschemes of a Noetherian scheme are Noetherian. The canonical
closure factorization has exact coefficient-module factors and exact composite; its
termwise functor commutes naturally with cohomology, preserves quasi-isomorphisms and
descends to the unbounded derived categories with its localization comparison.

Source: blueprint lemma-constructible-sheaves, introductory paragraph and proof (1), (3);
Stacks Tags 01OW, 01OZ, 01OY, 01R8, 09BM, 03DJ, 010N, 015F
(blueprint: lem-sfb-coefficient-heart-locally-closed-extension).

Proof plan:
1. Open subschemes are Noetherian by lem-weil-pbc-noetherian-open-subscheme-noetherian.
Closed subschemes of them are finite type (lem-weil-pbc-closed-immersion-proper), hence
Noetherian by lem-weil-pbc-finite-type-over-noetherian. Their spaces are Noetherian by
lem-weil-pbc-noetherian-scheme-closed-subsets-minimal. Every subset is compact by
lem-sfb-noetherian-space-compact-subsets, so every open immersion is quasi-compact.
Use lem-weil-pbc-locally-noetherian-quasi-separated for quasi-separatedness.
2. Compactness of every subset of the source proves quasi-compactness of a and its
diagonal. By lemma-nagata-immersion-open-in-scheme-image, a.toImage is open and dense.
The image inclusion is closed, with composite a (lemma-schematic-closure-uniqueness--1);
density identifies its range with the topological closure of the range of a.
3. Use sk-def-sfb-sheaf-tensor and
def-weil-pbc-internal-abelian-sheaf-module-equivalence to identify internal modules with
sectionwise modules over the actual coefficient ring sheaf. Their categories are abelian
by situation-conventions. The canonical coefficient identifications are
sk-def-sfb-coefficient-morphisms and apply to any commutative condensed ring.
4. The complement of the closed factor is quasi-compact by step 1. Apply
lem-sfb-proetale-identified-open-closed to its coefficient identification. Under the
module equivalences, its direct image agrees with prose-03-02: both keep
the underlying direct-image sheaf and maps, with action r*m = eta_i(r)*m. This comparison
is natural and linear. Equivalences preserve and reflect finite limits and colimits,
so the actual internal-module closed direct image is exact.
5. The actual open functor is exact by prose-03-02. The composite
in def-sfb-locally-closed-coefficient-extension is therefore exact.
6. Apply lem-weil-pbc-exact-functor-complex-cohomology for the natural homology
isomorphisms in every integer degree. Naturality identifies the homology of the image
of a quasi-isomorphism with the image of its homology, which is invertible.
7. Apply situation-conventions for the unbounded localization
square of sk-def-sfb-derived-categories. No resolution or boundedness is required.
The same argument allows empty schemes and zero complexes: the comparisons there are
the unique isomorphisms of zero objects. -/
theorem coefficientHeart_locallyClosedExtension
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [IsNoetherian X] :
    (∀ (T : Scheme.{u}) (b : T ⟶ X), IsImmersion b →
      IsNoetherian T ∧ TopologicalSpace.NoetherianSpace T ∧ QuasiSeparatedSpace T ∧
        ∀ (V : Scheme.{u}) (j : V ⟶ T), IsOpenImmersion j → QuasiCompact j) ∧
    ∀ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a),
      QuasiCompact a ∧ QuasiSeparated a ∧
      Set.range a.imageι = closure (Set.range a) ∧
      a.toImage ≫ a.imageι = a ∧ IsClosedImmersion a.imageι ∧
      Exists fun [_hu : IsOpenImmersion a.toImage] ↦
        PreservesFiniteLimits (CondensedRing.openImmersionLowerShriek Λ a.toImage) ∧
        PreservesFiniteColimits (CondensedRing.openImmersionLowerShriek Λ a.toImage) ∧
        PreservesFiniteLimits (CondensedRing.lowerStar Λ a.imageι) ∧
        PreservesFiniteColimits (CondensedRing.lowerStar Λ a.imageι) ∧
        PreservesFiniteLimits (coefficientHeartLocallyClosedExtension Λ a ha) ∧
        PreservesFiniteColimits (coefficientHeartLocallyClosedExtension Λ a ha) ∧
        Exists fun [_hadd : (coefficientHeartLocallyClosedExtension Λ a ha).Additive] ↦
          (∀ n : ℤ, Nonempty
            ((coefficientHeartLocallyClosedExtension Λ a ha).mapHomologicalComplex (.up ℤ) ⋙
              HomologicalComplex.homologyFunctor _ (.up ℤ) n ≅
              HomologicalComplex.homologyFunctor _ (.up ℤ) n ⋙
                coefficientHeartLocallyClosedExtension Λ a ha)) ∧
          (∀ (K L : CochainComplex
              (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) ℤ)
            (f : K ⟶ L), QuasiIso f →
              QuasiIso (((coefficientHeartLocallyClosedExtension Λ a ha).mapHomologicalComplex
                (.up ℤ)).map f)) ∧
          ∃ D : DerivedCategory
              (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) ⥤
                DerivedCategory
                  (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
            Nonempty (DerivedCategory.Q ⋙ D ≅
              (coefficientHeartLocallyClosedExtension Λ a ha).mapHomologicalComplex (.up ℤ) ⋙
                DerivedCategory.Q) := by
  have hsource (T : Scheme.{u}) (b : T ⟶ X) (hb : IsImmersion b) :
      IsNoetherian T ∧ TopologicalSpace.NoetherianSpace T ∧ QuasiSeparatedSpace T ∧
        ∀ (V : Scheme.{u}) (j : V ⟶ T), IsOpenImmersion j → QuasiCompact j := by
    have : IsImmersion b := hb
    have : TopologicalSpace.NoetherianSpace T := b.isEmbedding.isInducing.noetherianSpace
    have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian b
    exact ⟨⟨⟩, inferInstance, inferInstance, fun _ _ _ ↦ inferInstance⟩
  refine ⟨hsource, ?_⟩
  intro S a ha
  have : IsImmersion a := ha
  have : TopologicalSpace.NoetherianSpace S := (hsource S a ha).2.1
  have : QuasiCompact a := inferInstance
  have : IsOpenImmersion a.toImage := inferInstance
  have hrange : Set.range a.imageι = closure (Set.range a) := by
    change Set.range a.ker.subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]
  let V : X.Opens := ⟨(Set.range a.imageι)ᶜ, a.imageι.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hcomp : Set.range a.imageι.base = (Set.range V.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact (compl_compl (Set.range a.imageι)).symm
  have : PreservesFiniteColimits (CondensedRing.lowerStar Λ a.imageι) :=
    CondensedRing.closedSupport_lowerStarExact Λ a.imageι V.ι hcomp
  have : PreservesFiniteLimits (coefficientHeartLocallyClosedExtension Λ a ha) := by
    unfold coefficientHeartLocallyClosedExtension
    infer_instance
  have : PreservesFiniteColimits (coefficientHeartLocallyClosedExtension Λ a ha) := by
    unfold coefficientHeartLocallyClosedExtension
    infer_instance
  have : (coefficientHeartLocallyClosedExtension Λ a ha).Additive := by
    unfold coefficientHeartLocallyClosedExtension
    infer_instance
  refine ⟨inferInstance, inferInstance, hrange, a.toImage_imageι, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro n
    exact ⟨Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor _ (.up ℤ) n)
      (ShortComplex.homologyFunctorIso (coefficientHeartLocallyClosedExtension Λ a ha))⟩
  · intro K L f hf
    have : QuasiIso f := hf
    infer_instance
  · exact ⟨(coefficientHeartLocallyClosedExtension Λ a ha).mapDerivedCategory,
      ⟨(coefficientHeartLocallyClosedExtension Λ a ha).mapDerivedCategoryFactors⟩⟩

end AlgebraicGeometry.ProEtale
