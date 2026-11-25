/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
import WeilConjectures.AlgebraicGeometry.ExternalGlobalSectionsRestrictionComparisonLeft
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Finite-cover descent in the first factor

Source: Stacks Project, Tag 0BED, lemma-kunneth, the degree-zero finite-cover argument.
(blueprint: lem-sc-external-global-sections-tensor-finite-cover-left).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

private theorem isIso_app_of_pairwise_limits
    {k : Type w} [Field k]
    {Z : TopCat.{w}} {A B : Z.Presheaf (ModuleCat.{w} k)}
    {ι : Type w} (U : ι → TopologicalSpace.Opens Z) (c : A ⟶ B)
    (hA : IsLimit (A.mapCone (Pairwise.cocone U).op))
    (hB : IsLimit (B.mapCone (Pairwise.cocone U).op))
    (hc : ∀ j : Pairwise ι, IsIso (c.app (op ((Pairwise.diagram U).obj j)))) :
    IsIso (c.app (op (iSup U))) := by
  let d := Functor.whiskerLeft (Pairwise.diagram U).op c
  have : ∀ j, IsIso (d.app j) := fun j ↦ hc j.unop
  have : IsIso d := NatIso.isIso_of_isIso_app d
  let e := hA.conePointsIsoOfNatIso hB (asIso d)
  have he : c.app (op (iSup U)) = e.hom := by
    apply hB.hom_ext
    intro j
    rw [IsLimit.conePointsIsoOfNatIso_hom_comp]
    exact (c.naturality ((Pairwise.cocone U).op.π.app j)).symm
  rw [he]
  infer_instance

/-- Bijectivity descends from a finite cover of the first factor and its overlaps.
There are no quasi-coherence, compactness, or affine-diagonal assumptions in this lemma.
Source: Stacks Project, Tag 0BED, degree-zero part of equation-kunneth-on-cech.
(blueprint: lem-sc-external-global-sections-tensor-finite-cover-left).

Proof: For an open V of X, the cartesian open-immersion square identifies V times Y
with the inverse image of V under pr_1 : X times Y -> X. The canonical open-immersion
pullback/restriction comparison and the composition comparisons for tensor pullback
identify the external coefficient on V times Y with the restriction of the original
external coefficient. The unit equations for these comparisons and the pure tensor
formula for pullback of a tensor show that restricting an external product is the
external product of the restricted first section and the same second section.
Tensor induction gives this compatibility for all tensors and for every overlap.
Put N = Gamma(Y,G), as a k-vector space. The sheaf equalizer for F on the finite cover U
identifies Gamma(X,F) with the kernel of the difference of the two restriction maps
from the product of F(U_i) to the product of F(U_i intersect U_j). Tensoring with N
preserves this kernel because N is flat over the field. It also preserves the two
products because their indexing sets are finite. The sheaf equalizer for the external
coefficient on the inverse-image cover identifies its global sections with the
corresponding kernel. The restriction compatibility above gives a commuting diagram
of the two kernel diagrams. The hypotheses make the middle and right vertical maps
bijective. The inverse middle map preserves the kernels, since the right vertical
map is injective and the diagram commutes. Thus the middle map restricts to a
bijection of kernels, whose forward map is the displayed canonical external map.
If the indexing type is empty, hcover forces X to be empty; the section modules and
both equalizers are zero. Empty overlaps, empty Y, and zero coefficients are also
covered by the same kernel and finite-product argument. No infinite-product or
positive-cohomology comparison is used. -/
theorem externalGlobalSectionsTensor_bijective_of_finite_cover_left
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules)
    {ι : Type w} [Finite ι] (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (hU : ∀ i, Function.Bijective
      (externalGlobalSectionsTensor ((U i).ι ≫ f) g (F.restrict (U i).ι) G))
    (hUU : ∀ i j, Function.Bijective
      (externalGlobalSectionsTensor ((U i ⊓ U j).ι ≫ f) g
        (F.restrict (U i ⊓ U j).ι) G)) :
    Function.Bijective (externalGlobalSectionsTensor f g F G) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨c, htop, hlocal⟩ := exists_externalSectionsRestrictionComparisonLeft f g F G
  have hcomponent (V : X.Opens)
      (hV : Function.Bijective
        (externalGlobalSectionsTensor (V.ι ≫ f) g (F.restrict V.ι) G)) :
      IsIso (c.app (op V)) := by
    obtain ⟨eS, eT, he⟩ := hlocal V
    have : IsIso (ModuleCat.ofHom
        (externalGlobalSectionsTensor (V.ι ≫ f) g (F.restrict V.ι) G)) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hV
    have : IsIso (c.app (op V) ≫ eT.hom) := by rw [he]; infer_instance
    exact IsIso.of_isIso_comp_right _ eT.hom
  have hA := (TopCat.Presheaf.IsSheaf.isSheafPairwiseIntersections
    U (scalarPresheaf_isSheaf f F)).some
  have hAt := isLimitOfPreserves
    (MonoidalCategory.tensorRight (scalarObj g G (op ⊤))) hA
  have hB : TopCat.Presheaf.IsSheaf (externalSectionsPushforwardLeft f g F G) :=
    TopCat.Sheaf.pushforward_sheaf_of_sheaf (pullback.fst f g).base
      (scalarPresheaf_isSheaf (pullback.fst f g ≫ f) (externalCupCoefficients f g F G))
  have hBt := (TopCat.Presheaf.IsSheaf.isSheafPairwiseIntersections U hB).some
  have hsup := isIso_app_of_pairwise_limits U c hAt hBt (by
    rintro (i | ⟨i, j⟩)
    · exact hcomponent (U i) (hU i)
    · exact hcomponent (U i ⊓ U j) (hUU i j))
  rw [hcover] at hsup
  have : IsIso (c.app (op ⊤)) := hsup
  have : IsIso (ModuleCat.ofHom (externalGlobalSectionsTensor f g F G)) := by
    rw [← htop]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective
    (ModuleCat.ofHom (externalGlobalSectionsTensor f g F G))).1 inferInstance

end AlgebraicGeometry.Scheme.Modules
