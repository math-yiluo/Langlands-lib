import Langlands.Representation.Category.CoproductCompression
import Langlands.Representation.Category.SubrepresentationSums
import Langlands.Representation.Category.IrreducibleSubquotientExistence
import Langlands.Representation.Category.FiniteGenerationExhaustion
import Langlands.CategoryTheory.RenardCategoryDecomposition

/-! # Coproducts with disjoint irreducible constituents -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.SmoothRep

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI}

/-- A cofan is colimiting when actual summation is bijective, independently
of the index and carrier universes. -/
def cofanIsColimitOfBijective [DecidableEq I]
    (A : I → SmoothRep.{0, uG, uV} ℂ G) (s : Cofan A)
    (h : Function.Bijective (cofanDirectSumMap A s)) : IsColimit s := by
  let e := (cofanDirectSumMap A s).ofBijective h
  refine Cofan.IsColimit.mk _ (fun t =>
    ofHom ((cofanDirectSumMap A t).comp e.symm.toIntertwiningMap)) ?_ ?_
  · intro t i
    ext v
    change cofanDirectSumMap A t (e.symm (hom (s.inj i) v)) = hom (t.inj i) v
    have he : e.symm (hom (s.inj i) v) = DirectSum.lof ℂ I (fun i => A i) i v := by
      apply e.injective
      exact (e.apply_symm_apply _).trans (cofanDirectSumMap_lof A s i v).symm
    rw [he, cofanDirectSumMap_lof]
  · intro t m hm
    ext v
    obtain ⟨x, rfl⟩ := h.surjective v
    change hom m (e x) = cofanDirectSumMap A t (e.symm (e x))
    rw [e.symm_apply_apply]
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i w =>
      rw [show e (DirectSum.of (fun i => A i) i w) = hom (s.inj i) w from
        cofanDirectSumMap_lof A s i w]
      exact (congrArg (fun f => hom f w) (hm i)).trans
        (cofanDirectSumMap_lof A t i w).symm
    | add x y hx hy => simp only [map_add, hx, hy]

/-- Invariant subspaces with no common irreducible actual subquotients form
an independent family, with no size restriction on its index. -/
theorem iSupIndep_of_no_common_irreducibleSubquotient
    {A : SmoothRep.{0, uG, uV} ℂ G}
    (W : I → Subrepresentation A.representation)
    (hW : ∀ i j, i ≠ j → ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      D.IsIrreducible → IsSubquotient D (subrepresentation A (W i)) →
        IsSubquotient D (subrepresentation A (W j)) → False) :
    iSupIndep (fun i => (W i).toSubmodule) := by
  rw [iSupIndep_def]
  intro i
  let Q : Subrepresentation A.representation := ⨆ j : {j : I // j ≠ i}, W j.val
  suffices h : Disjoint (W i).toSubmodule Q.toSubmodule by
    simpa only [Q, Langlands.Subrepresentation.toSubmodule_iSup, iSup_subtype] using h
  rw [Submodule.disjoint_def]
  intro x hx hQ
  by_contra hx0
  let B := subrepresentation A (W i ⊓ Q)
  let : Nontrivial B :=
    ⟨⟨⟨x, ⟨hx, hQ⟩⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨D, hD, hDB⟩ := exists_isIrreducible_isSubquotient_of_nontrivial B
  have hDi : IsSubquotient D (subrepresentation A (W i)) :=
    smoothSubquotientTransitivity ℂ G _ _ _ hDB
      (IsSubrepresentation.isSubquotient ⟨subrepresentationInclusion inf_le_left,
        subrepresentationInclusion_injective inf_le_left⟩)
  have hDQ : IsSubquotient D (subrepresentation A Q) :=
    smoothSubquotientTransitivity ℂ G _ _ _ hDB
      (IsSubrepresentation.isSubquotient ⟨subrepresentationInclusion inf_le_right,
        subrepresentationInclusion_injective inf_le_right⟩)
  obtain ⟨j, hj⟩ := irreducibleSubquotient_iSup hD
    (fun j : {j : I // j ≠ i} => W j.val) hDQ
  exact hW i j.val j.property.symm D hD hDi hj

/-- Intersect every summand of an actual cofan with an invariant subspace. -/
def subrepresentationCofan
    (A : I → SmoothRep.{0, uG, uV} ℂ G) (s : Cofan A)
    (S : Subrepresentation s.pt.representation) :
    Cofan (fun i => subrepresentation (A i) (subrepresentationPreimage (s.inj i) S)) :=
  Cofan.mk (subrepresentation s.pt S)
    (fun i => subrepresentationPreimageMap (s.inj i) S)

/-- With disjoint irreducible constituents, intersecting the summands with
an arbitrary invariant subspace preserves the actual coproduct cofan. -/
def subrepresentationCofanIsColimit [DecidableEq I]
    (A : I → SmoothRep.{0, uG, uV} ℂ G) (s : Cofan A) (hs : IsColimit s)
    (hA : ∀ i j, i ≠ j → ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      D.IsIrreducible → IsSubquotient D (A i) → IsSubquotient D (A j) → False)
    (S : Subrepresentation s.pt.representation) :
    IsColimit (subrepresentationCofan A s S) := by
  let B := fun i => subrepresentation (A i) (subrepresentationPreimage (s.inj i) S)
  let t := subrepresentationCofan A s S
  let L := DirectSum.lmap
    (fun i => (hom (subtype (A i) (subrepresentationPreimage (s.inj i) S))).toLinearMap)
  have hL : Function.Injective L :=
    (DirectSum.lmap_injective _).mpr (fun i => subtype_injective _ _)
  have hcomm : (hom (subtype s.pt S)).toLinearMap.comp
      (cofanDirectSumMap B t).toLinearMap = (cofanDirectSumMap A s).toLinearMap.comp L := by
    apply DirectSum.linearMap_ext
    intro i
    ext v
    simp only [LinearMap.comp_apply, L]
    rfl
  have hcomm_apply (x) :
      hom (subtype s.pt S) (cofanDirectSumMap B t x) = cofanDirectSumMap A s (L x) :=
    LinearMap.congr_fun hcomm x
  apply cofanIsColimitOfBijective B t
  constructor
  · intro x y hxy
    apply hL
    apply cofanDirectSumMap_injective A s hs
    exact (hcomm_apply x).symm.trans
      ((congrArg (hom (subtype s.pt S)) hxy).trans (hcomm_apply y))
  · intro v
    let q := mkQ s.pt S
    let f : ∀ i, A i ⟶ quotient s.pt S := fun i => s.inj i ≫ q
    let W := fun i => (hom (f i)).range
    have hW : iSupIndep (fun i => (W i).toSubmodule) := by
      apply iSupIndep_of_no_common_irreducibleSubquotient W
      intro i j hij D hD hDi hDj
      exact hA i j hij D hD
        (smoothSubquotientTransitivity ℂ G _ _ _ hDi (image_isQuotient (f i)).isSubquotient)
        (smoothSubquotientTransitivity ℂ G _ _ _ hDj (image_isQuotient (f j)).isSubquotient)
    let r := DirectSum.lmap (fun i => (hom (f i)).toLinearMap.rangeRestrict)
    have hr : (DirectSum.coeLinearMap (fun i => (W i).toSubmodule)).comp r =
        (hom q).toLinearMap.comp (cofanDirectSumMap A s).toLinearMap := by
      apply DirectSum.linearMap_ext
      intro i
      ext w
      simp only [LinearMap.comp_apply, r]
      rfl
    have hr_apply (x) :
        DirectSum.coeLinearMap (fun i => (W i).toSubmodule) (r x) =
          hom q (cofanDirectSumMap A s x) := LinearMap.congr_fun hr x
    obtain ⟨x, hx⟩ := cofanDirectSumMap_surjective A s hs v.val
    have hrx : r x = 0 := by
      apply hW.dfinsupp_lsum_injective
      change DirectSum.coeLinearMap (fun i => (W i).toSubmodule) (r x) =
        DirectSum.coeLinearMap (fun i => (W i).toSubmodule) 0
      rw [hr_apply, hx, map_zero]
      exact (Submodule.Quotient.mk_eq_zero S.toSubmodule).mpr v.property
    have hmem : ∀ i, x i ∈ subrepresentationPreimage (s.inj i) S := by
      intro i
      apply (Submodule.Quotient.mk_eq_zero S.toSubmodule).mp
      have hi := congrArg (fun y => (y i).val) hrx
      exact hi
    have hxL : x ∈ LinearMap.range L := by
      rw [DirectSum.range_lmap]
      intro i _
      exact ⟨⟨x i, hmem i⟩, rfl⟩
    obtain ⟨y, hy⟩ := hxL
    refine ⟨y, ?_⟩
    apply Subtype.ext
    change hom (subtype s.pt S) (cofanDirectSumMap B t y) = v.val
    exact (hcomm_apply y).trans ((congrArg (cofanDirectSumMap A s) hy).trans hx)

/-- Disjoint predicates on irreducible constituents split every subrepresentation
of an object already presented as a coproduct of its supported components. -/
theorem isCoproductOfComponents_subrepresentation
    (P : I → ObjectProperty (SmoothRep.{0, uG, uV} ℂ G))
    (hP : ∀ i j, i ≠ j → ∀ D : SmoothRep.{0, uG, uV} ℂ G,
      D.IsIrreducible → P i D → P j D → False)
    {V : SmoothRep.{0, uG, uV} ℂ G}
    (hV : Renard.IsCoproductOfComponents
      (fun i A => ∀ D : SmoothRep.{0, uG, uV} ℂ G,
        D.IsIrreducible → IsSubquotient D A → P i D) V)
    (S : Subrepresentation V.representation) :
    Renard.IsCoproductOfComponents
      (fun i A => ∀ D : SmoothRep.{0, uG, uV} ℂ G,
        D.IsIrreducible → IsSubquotient D A → P i D) (subrepresentation V S) := by
  classical
  obtain ⟨A, ι, hA, ⟨hs⟩⟩ := hV
  let s := Cofan.mk V ι
  refine ⟨_, (subrepresentationCofan A s S).inj, ?_,
    ⟨subrepresentationCofanIsColimit A s hs ?_ S⟩⟩
  · intro i D hD hDB
    exact hA i D hD
      (smoothSubquotientTransitivity ℂ G _ _ _ hDB
        (subrepresentation_isSubrepresentation _).isSubquotient)
  · intro i j hij D hD hDi hDj
    exact hP i j hij D hD (hA i D hD hDi) (hA j D hD hDj)

/-- With no common irreducible actual subquotient, every morphism vanishes. -/
theorem hom_eq_zero_of_no_common_irreducibleSubquotient
    {A B : SmoothRep.{0, uG, uV} ℂ G}
    (h : ∀ D : SmoothRep.{0, uG, uV} ℂ G, D.IsIrreducible →
      IsSubquotient D A → IsSubquotient D B → False) (f : A ⟶ B) : f = 0 := by
  by_contra hf
  have hv : ∃ v : A, hom f v ≠ 0 := by
    by_contra hn
    apply hf
    ext v
    exact Classical.not_not.mp (not_exists.mp hn v)
  obtain ⟨v, hv⟩ := hv
  let : Nontrivial (image f) :=
    ⟨⟨⟨hom f v, ⟨v, rfl⟩⟩, 0, fun heq => hv (congrArg Subtype.val heq)⟩⟩
  obtain ⟨D, hD, hDI⟩ := exists_isIrreducible_isSubquotient_of_nontrivial (image f)
  exact h D hD
    (smoothSubquotientTransitivity ℂ G _ _ _ hDI (image_isQuotient f).isSubquotient)
    (smoothSubquotientTransitivity ℂ G _ _ _ hDI
      (subrepresentation_isSubrepresentation (hom f).range).isSubquotient)

end Langlands.SmoothRep
