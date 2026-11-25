/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison
import WeilConjectures.AlgebraicGeometry.ExternalGlobalSectionsRestrictionComparison
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Finite-cover descent for the external section comparison

Source: Stacks Project, Tag 0BED, lemma-kunneth, the degree-zero finite-cover argument.
(blueprint: lem-sc-external-global-sections-tensor-finite-cover).
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

/-- Bijectivity descends from a finite cover of the second factor and its overlaps.
There are no quasi-coherence, compactness, or affine-diagonal assumptions in this lemma.
Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, degree-zero cover argument.
(blueprint: lem-sc-external-global-sections-tensor-finite-cover).

Proof: Let M = Gamma(X,F), with its k-action. For each open V of Y, the open immersion
V -> Y gives X times V as the inverse image of V under pr_2 : X times Y -> Y.
The open-immersion pullback/restriction comparison and composition of pullback adjunctions
identify the external coefficient restricted to this open with the external coefficient
formed from F and G restricted to V. The unit equations and naturality of tensor sections
show that these comparisons take the external product of sections to its restriction.
This compatibility holds on pure tensors and then on all tensors by induction.
Take the sheaf equalizer for G on the cover U and the equalizer for the external
coefficient on the inverse-image cover. The first equalizer consists of tuples whose
restrictions to every U_i intersect U_j agree. Tensoring the first equalizer with M
preserves it: k-vector spaces are flat, and the cover and its pairs have finite index
sets, so tensor commutes with both products. The local external comparisons therefore
give a commuting diagram of these two equalizers. The hypotheses hU and hUU say its
middle and right vertical arrows are bijective. Their inverses commute with the two
restriction arrows. Restricting these inverses to the equalizers gives an inverse to
the left vertical arrow, which is the displayed canonical external section map by the
restriction compatibility. An empty cover forces Y empty, and the zero equalizers give
the same result; empty overlaps and zero section modules cause no exception.
-/
theorem externalGlobalSectionsTensor_bijective_of_finite_cover
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules)
    {ι : Type w} [Finite ι] (U : ι → Y.Opens) (hcover : iSup U = ⊤)
    (hU : ∀ i, Function.Bijective
      (externalGlobalSectionsTensor f ((U i).ι ≫ g) F (G.restrict (U i).ι)))
    (hUU : ∀ i j, Function.Bijective
      (externalGlobalSectionsTensor f ((U i ⊓ U j).ι ≫ g) F
        (G.restrict (U i ⊓ U j).ι))) :
    Function.Bijective (externalGlobalSectionsTensor f g F G) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨c, htop, hlocal⟩ := exists_externalSectionsRestrictionComparison f g F G
  have hcomponent (V : Y.Opens)
      (hV : Function.Bijective
        (externalGlobalSectionsTensor f (V.ι ≫ g) F (G.restrict V.ι))) :
      IsIso (c.app (op V)) := by
    obtain ⟨eS, eT, he⟩ := hlocal V
    have : IsIso (ModuleCat.ofHom
        (externalGlobalSectionsTensor f (V.ι ≫ g) F (G.restrict V.ι))) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hV
    have : IsIso (c.app (op V) ≫ eT.hom) := by rw [he]; infer_instance
    exact IsIso.of_isIso_comp_right _ eT.hom
  have hA := (TopCat.Presheaf.IsSheaf.isSheafPairwiseIntersections
    U (scalarPresheaf_isSheaf g G)).some
  have hAt := isLimitOfPreserves
    (MonoidalCategory.tensorLeft (scalarObj f F (op ⊤))) hA
  have hB : TopCat.Presheaf.IsSheaf (externalSectionsPushforward f g F G) :=
    TopCat.Sheaf.pushforward_sheaf_of_sheaf (pullback.snd f g).base
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
