/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Every module is a directed colimit of finitely presented modules

Source: Stacks Project, Algebra, Tag 058G, proof of Lazard's theorem, paragraph beginning
"For the converse, first recall that any module M can be written as the colimit of a
 directed system of finitely presented modules"
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Module

noncomputable section

private abbrev freeMap (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] : (M →₀ R) →ₗ[R] M :=
  Finsupp.linearCombination R id

private abbrev PresentationIndex (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :=
  {a : Finset M × Submodule R (M →₀ R) //
    a.2.FG ∧ a.2 ≤ Finsupp.supported R R (a.1 : Set M) ∧ a.2 ≤ (freeMap R M).ker}

private instance indexNonempty (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] : Nonempty (PresentationIndex R M) :=
  ⟨⟨(∅, ⊥), Submodule.fg_bot, bot_le, bot_le⟩⟩

private instance indexDirected (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    IsDirected (PresentationIndex R M) (· ≤ ·) where
  directed i j := by
    classical
    refine ⟨⟨(i.1.1 ∪ j.1.1, i.1.2 ⊔ j.1.2), i.2.1.sup j.2.1, ?_,
      sup_le i.2.2.2 j.2.2.2⟩, ?_, ?_⟩
    · exact sup_le (i.2.2.1.trans (Finsupp.supported_mono (Finset.coe_subset.mpr
        Finset.subset_union_left))) (j.2.2.1.trans
          (Finsupp.supported_mono (Finset.coe_subset.mpr Finset.subset_union_right)))
    · exact ⟨Finset.subset_union_left, le_sup_left⟩
    · exact ⟨Finset.subset_union_right, le_sup_right⟩

private abbrev stageFree {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (i : PresentationIndex R M) :=
  Finsupp.supported R R (i.1.1 : Set M)

private abbrev stageRelations {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (i : PresentationIndex R M) :=
  i.1.2.comap (stageFree i).subtype

private abbrev stage {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (i : PresentationIndex R M) :=
  (stageFree i) ⧸ stageRelations i

private theorem stageFP {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (i : PresentationIndex R M) :
    FinitePresentation R (stage i) := by
  let e := Finsupp.supportedEquivFinsupp (R := R) (M := R) (i.1.1 : Set M)
  let : FinitePresentation R (stageFree i) := FinitePresentation.of_equiv e.symm
  apply finitePresentation_of_surjective (stageRelations i).mkQ
    (stageRelations i).mkQ_surjective
  rw [Submodule.ker_mkQ]
  apply Submodule.fg_of_fg_map_injective (stageFree i).subtype Subtype.val_injective
  simpa only [stageRelations, Submodule.map_comap_subtype, inf_eq_right.mpr i.2.2.1]
    using i.2.1

private def stageInclusion {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {i j : PresentationIndex R M}
    (h : i ≤ j) : stageFree i →ₗ[R] stageFree j :=
  Submodule.inclusion (Finsupp.supported_mono (Finset.coe_subset.mpr h.1))

private def stageMap {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {i j : PresentationIndex R M}
    (h : i ≤ j) : stage i →ₗ[R] stage j :=
  (stageRelations i).mapQ (stageRelations j) (stageInclusion h) (fun _ hx ↦ h.2 hx)

private def presentationDiagram (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    PresentationIndex R M ⥤ ModuleCat.{max u v} R where
  obj i := ModuleCat.of R (stage i)
  map h := ModuleCat.ofHom (stageMap (leOfHom h))
  map_id i := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

private def stageToModule {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (i : PresentationIndex R M) :
    stage i →ₗ[R] M :=
  (stageRelations i).liftQ ((freeMap R M).comp (stageFree i).subtype)
    (fun _ hx ↦ i.2.2.2 hx)

private def presentationCocone (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] : Cocone (presentationDiagram R M) where
  pt := ModuleCat.of R (ULift.{u} M)
  ι.app i := ModuleCat.ofHom ((ULift.moduleEquiv.symm : M ≃ₗ[R] ULift.{u} M).toLinearMap
    ∘ₗ stageToModule i)
  ι.naturality i j h := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

private def singletonIndex {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (m : M) : PresentationIndex R M :=
  ⟨({m}, ⊥), Submodule.fg_bot, bot_le, bot_le⟩

private def basisAt {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (i : PresentationIndex R M)
    (m : M) (hm : m ∈ i.1.1) : stageFree i :=
  ⟨Finsupp.single m 1, Finsupp.single_mem_supported R 1 hm⟩

private def coconeFreeMap {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (c : Cocone (presentationDiagram R M)) :
    (M →₀ R) →ₗ[R] c.pt :=
  Finsupp.linearCombination R (fun m ↦ c.ι.app (singletonIndex (R := R) m)
    ((stageRelations (singletonIndex (R := R) m)).mkQ
      (basisAt (singletonIndex (R := R) m) m (by simp [singletonIndex]))))

private theorem coconeFreeMap_restrict {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (c : Cocone (presentationDiagram R M))
    (i : PresentationIndex R M) :
    (coconeFreeMap c).comp (stageFree i).subtype =
      (c.ι.app i).hom.comp (stageRelations i).mkQ := by
  classical
  let e := Finsupp.supportedEquivFinsupp (R := R) (M := R) (i.1.1 : Set M)
  have he : ((coconeFreeMap c).comp (stageFree i).subtype).comp e.symm.toLinearMap =
      ((c.ι.app i).hom.comp (stageRelations i).mkQ).comp e.symm.toLinearMap := by
    ext m
    have hmi : singletonIndex (R := R) m.1 ≤ i :=
      ⟨Finset.singleton_subset_iff.mpr m.2, bot_le⟩
    have hw := congrArg (fun f ↦ f ((stageRelations (singletonIndex (R := R) m.1)).mkQ
      (basisAt (singletonIndex (R := R) m.1) m.1 (by simp [singletonIndex])))) (c.w (homOfLE hmi))
    have heq : e.symm (Finsupp.single m 1) = basisAt i m.1 m.2 := by
      apply Subtype.ext
      exact Finsupp.supportedEquivFinsupp_symm_single (i.1.1 : Set M) m 1
    change coconeFreeMap c (e.symm (Finsupp.single m 1)) =
      (c.ι.app i).hom ((stageRelations i).mkQ (e.symm (Finsupp.single m 1)))
    rw [heq]
    simp only [coconeFreeMap, basisAt, Finsupp.linearCombination_single, one_smul]
    exact hw.symm
  ext x
  obtain ⟨y, rfl⟩ := e.symm.surjective x
  exact LinearMap.congr_fun he y

private theorem coconeFreeMap_kills {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (c : Cocone (presentationDiagram R M)) :
    (freeMap R M).ker ≤ (coconeFreeMap c).ker := by
  classical
  intro x hx
  let i : PresentationIndex R M :=
    ⟨(x.support, Submodule.span R {x}), Submodule.fg_span_singleton x,
      Submodule.span_le.mpr (by
        intro y hy
        have hxy : y = x := Set.mem_singleton_iff.mp hy
        rw [hxy]
        exact Finsupp.mem_supported_support R x),
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)⟩
  let y : stageFree i := ⟨x, Finsupp.mem_supported_support R x⟩
  have hy : (stageRelations i).mkQ y = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span (by simp [y, i]))
  have h := LinearMap.congr_fun (coconeFreeMap_restrict c i) y
  change coconeFreeMap c x = 0
  change coconeFreeMap c x = (c.ι.app i).hom ((stageRelations i).mkQ y) at h
  simpa only [hy, map_zero] using h

private def presentationDesc {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (c : Cocone (presentationDiagram R M)) :
    ULift.{u} M →ₗ[R] c.pt :=
  (((freeMap R M).ker.liftQ (coconeFreeMap c) (coconeFreeMap_kills c)).comp
    ((freeMap R M).quotKerEquivOfSurjective
      (Finsupp.linearCombination_surjective R Function.surjective_id)).symm.toLinearMap).comp
    ULift.moduleEquiv.toLinearMap

private theorem presentationDesc_free {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (c : Cocone (presentationDiagram R M))
    (x : M →₀ R) : presentationDesc c (ULift.up (freeMap R M x)) = coconeFreeMap c x := by
  simp [presentationDesc]

private def presentationIsColimit (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] :
    IsColimit (presentationCocone R M) where
  desc c := ModuleCat.ofHom (presentationDesc c)
  fac c i := by
    apply ModuleCat.hom_ext
    apply Submodule.quot_hom_ext
    intro x
    change presentationDesc c (ULift.up (freeMap R M x.1)) = _
    rw [presentationDesc_free]
    exact LinearMap.congr_fun (coconeFreeMap_restrict c i) x
  uniq c f hf := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨m⟩ := x
    have h := congrArg (fun g ↦ g ((stageRelations (singletonIndex (R := R) m)).mkQ
      (basisAt (singletonIndex (R := R) m) m (by simp [singletonIndex]))))
      (hf (singletonIndex (R := R) m))
    change f (ULift.up (freeMap R M (Finsupp.single m 1))) = _ at h
    simp only [freeMap, Finsupp.linearCombination_single, id_eq, one_smul] at h
    have hd := presentationDesc_free c (Finsupp.single m 1)
    simp only [freeMap, Finsupp.linearCombination_single, id_eq, one_smul,
      coconeFreeMap] at hd
    exact h.trans hd.symm

/-- Every module is a colimit of a small nonempty directed poset of finitely presented modules.
Source: Stacks Project, Algebra, Tag 058G, proof of Lazard's theorem
(auxiliary; not a blueprint node).

The common universe `max u v` accommodates the finite free modules over `R`, their quotients,
and the index set. The cocone vertex is the canonical universe lift of `M`; this is the same
module via `ULift.moduleEquiv`. Functoriality supplies identity and composition for the
transition maps, and cocone naturality supplies compatibility of the maps to `M`.

Proof:
1. Form the free module `P = M →₀ R`, with basis vectors indexed by `M`
   (def-weil-pbc-free-module). The linear combination map `p : P →ₗ[R] M` is surjective;
   write `K` for its kernel.
2. Index by pairs `(J, N)`, where `J` is a finite subset of `M` and `N` is a finitely generated
   submodule of `P`, supported on `J` and contained in `K`. Componentwise inclusion is a
   partial order, and the pairs form a set in the common universe.
3. The pair `(∅, 0)` gives nonemptiness. Union of the finite supports and sum of the finitely
   generated relation submodules give a common upper bound for any two pairs.
4. At `(J, N)` take `P_J / N`. A finite generating list of `N` supplies a map from a finite
   free module onto `N`; the quotient therefore has a finite presentation
   (def-sc-finitely-presented-module), also when the generators or relations are empty.
5. Inclusion of supports and relations induces the transition maps. Quotient formulas give
   their identity and composition laws. The maps induced by `p` are a compatible cocone.
6. Given any compatible cocone to `T`, use the singleton stages to assign an image in `T`
   to every basis vector of `P`. Extend by finite linear combinations to a linear map
   `h : P →ₗ[R] T`. Compatibility identifies its restriction to each `P_J` with the given
   stage map followed by the quotient map.
7. For `x ∈ K`, the stage with its finite support and relation submodule `R x` kills `x`.
   Hence `h` vanishes on `K` and descends uniquely along the surjection `p` to `M`.
8. The descended map factors all the stage maps; singleton stages prove uniqueness.
   This is exactly `IsColimit` (def-weil-pbc-category-colimit). -/
theorem exists_directed_colimit_finitePresentation
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    ∃ (I : Type (max u v)) (p : PartialOrder I) (_ : Nonempty I)
      (_ : IsDirected I p.toLE.le),
      ∃ (F : @Functor I (@Preorder.smallCategory I p.toPreorder)
          (ModuleCat.{max u v} R) inferInstance),
        (∀ i, Module.FinitePresentation R (F.obj i)) ∧
        ∃ (c : Cocone F), c.pt = ModuleCat.of R (ULift.{u} M) ∧
          Nonempty (IsColimit c) := by
  refine ⟨PresentationIndex R M, inferInstance, inferInstance, inferInstance,
    presentationDiagram R M, stageFP, presentationCocone R M, rfl,
    ⟨presentationIsColimit R M⟩⟩

end

end Module
