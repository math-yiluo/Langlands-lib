import Langlands.Representation.Category.ConstituentDichotomy
import Langlands.Representation.SubrepresentationLattice
import Langlands.Representation.Filtration.SubquotientAlgebraProof

/-!
# Actual subrepresentation sums and their irreducible subquotients

All sums are invariant submodule suprema inside a fixed smooth representation.
-/

noncomputable section

open CategoryTheory

namespace Langlands.SmoothRep

universe uR uG uV uJ

variable {R : Type uR} [Field R] {G : Type uG} [Group G] [TopologicalSpace G]
  {A B D : SmoothRep.{uR, uG, uV} R G}

/-- The actual inclusion between two ordered invariant subrepresentations. -/
def subrepresentationInclusion {S T : Subrepresentation A.representation} (h : S ≤ T) :
    subrepresentation A S ⟶ subrepresentation A T :=
  ofHom {
    toLinearMap := S.toSubmodule.inclusion h
    isIntertwining' g := by
      ext v
      rfl }

theorem subrepresentationInclusion_injective {S T : Subrepresentation A.representation}
    (h : S ≤ T) : Function.Injective (hom (subrepresentationInclusion h)) := by
  intro x y hxy
  change (⟨x.val, h x.property⟩ : T.toSubmodule) = ⟨y.val, h y.property⟩ at hxy
  exact Subtype.ext (congrArg (fun z : T.toSubmodule => z.val) hxy)

/-- The inverse image of an actual invariant subrepresentation along an intertwiner. -/
def subrepresentationPreimage (f : A ⟶ B) (S : Subrepresentation B.representation) :
    Subrepresentation A.representation where
  toSubmodule := S.toSubmodule.comap (hom f).toLinearMap
  apply_mem_toSubmodule g v hv := by
    change hom f (A.representation g v) ∈ S
    rw [Representation.IntertwiningMap.isIntertwining]
    exact S.apply_mem_toSubmodule g hv

/-- The restriction of an intertwiner to the inverse image of an invariant submodule. -/
def subrepresentationPreimageMap (f : A ⟶ B) (S : Subrepresentation B.representation) :
    subrepresentation A (subrepresentationPreimage f S) ⟶ subrepresentation B S :=
  ofHom {
    toLinearMap :=
      ((hom f).toLinearMap.comp (subrepresentationPreimage f S).toSubmodule.subtype).codRestrict
        S.toSubmodule (fun v => v.property)
    isIntertwining' g := by
      ext v
      exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ (hom f) g v.val) }

theorem subrepresentationPreimageMap_injective (f : A ⟶ B)
    (S : Subrepresentation B.representation) (hf : Function.Injective (hom f)) :
    Function.Injective (hom (subrepresentationPreimageMap f S)) := by
  intro x y hxy
  exact Subtype.ext (hf (congrArg Subtype.val hxy))

/-- A constituent of a binary invariant sum occurs in one of its summands. -/
theorem irreducibleSubquotient_sup (hD : D.IsIrreducible)
    (S T : Subrepresentation A.representation)
    (h : IsSubquotient D (subrepresentation A (S ⊔ T))) :
    IsSubquotient D (subrepresentation A S) ∨ IsSubquotient D (subrepresentation A T) := by
  let B := subrepresentation A (S ⊔ T)
  let W := subrepresentationPreimage (subtype A (S ⊔ T)) S
  rcases irreducibleSubquotient_dichotomy hD h W with hS | hT
  · left
    exact smoothSubquotientTransitivity R G _ _ _ hS
      (IsSubrepresentation.isSubquotient
        ⟨subrepresentationPreimageMap (subtype A (S ⊔ T)) S,
          subrepresentationPreimageMap_injective _ _ (subtype_injective _ _)⟩)
  · right
    let q : subrepresentation A T ⟶ quotient B W :=
      subrepresentationInclusion (le_sup_right : T ≤ S ⊔ T) ≫ mkQ B W
    have hq : Function.Surjective (hom q) := by
      intro z
      obtain ⟨v, rfl⟩ := mkQ_surjective B W z
      obtain ⟨s, hs, t, ht, heq⟩ := Submodule.mem_sup.mp v.property
      refine ⟨⟨t, ht⟩, ?_⟩
      apply (Submodule.Quotient.eq W.toSubmodule).mpr
      change t - v.val ∈ S
      have ht' : t - v.val = -s := by rw [← heq]; abel
      rw [ht']
      exact S.toSubmodule.neg_mem hs
    exact smoothSubquotientTransitivity R G _ _ _ hT
      (IsQuotient.isSubquotient ⟨q, hq⟩)

/-- A nonzero irreducible object is not a subquotient of the zero invariant submodule. -/
theorem not_irreducibleSubquotient_bot (hD : D.IsIrreducible) :
    ¬ IsSubquotient D (subrepresentation A ⊥) := by
  let := hD
  intro h
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp h
  have hz (d : D) : d = 0 := by
    obtain ⟨c, rfl⟩ := hq d
    have hzero : hom i c = 0 := by
      apply Subtype.ext
      change (hom i c).val = 0
      exact (Submodule.mem_bot R).mp (hom i c).property
    have hc : c = 0 := hi (hzero.trans (map_zero _).symm)
    rw [hc, map_zero]
  apply (bot_ne_top : (⊥ : Subrepresentation D.representation) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  ext d
  rw [hz d]
  exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩

/-- A constituent of a finite invariant sum occurs in one of its summands. -/
theorem irreducibleSubquotient_finset_sup (hD : D.IsIrreducible)
    {J : Type uJ} (F : J → Subrepresentation A.representation) (s : Finset J)
    (h : IsSubquotient D (subrepresentation A (s.sup F))) :
    ∃ j ∈ s, IsSubquotient D (subrepresentation A (F j)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact False.elim (not_irreducibleSubquotient_bot hD h)
  | @insert j s hj ih =>
    rw [Finset.sup_insert] at h
    rcases irreducibleSubquotient_sup hD (F j) (s.sup F) h with h | h
    · exact ⟨j, Finset.mem_insert_self _ _, h⟩
    · obtain ⟨k, hk, h⟩ := ih h
      exact ⟨k, Finset.mem_insert_of_mem hk, h⟩

/-- A constituent of a nonempty directed invariant sum occurs in a member. -/
theorem irreducibleSubquotient_directed_iSup (hD : D.IsIrreducible)
    {J : Type uJ} [Nonempty J] (F : J → Subrepresentation A.representation)
    (hF : Directed (· ≤ ·) F)
    (h : IsSubquotient D (subrepresentation A (⨆ j, F j))) :
    ∃ j, IsSubquotient D (subrepresentation A (F j)) := by
  let := hD
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp h
  have hn : ∃ d : D, d ≠ 0 := by
    by_contra! hz
    apply (bot_ne_top : (⊥ : Subrepresentation D.representation) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    ext d
    rw [hz d]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  obtain ⟨d, hd⟩ := hn
  obtain ⟨c, hc⟩ := hq d
  have hm : (hom i c).val ∈ ⨆ j, (F j).toSubmodule := by
    rw [← Langlands.Subrepresentation.toSubmodule_iSup]
    exact (hom i c).property
  have hF' : Directed (· ≤ ·) (fun j => (F j).toSubmodule) := hF
  obtain ⟨j, hj⟩ := (Submodule.mem_iSup_of_directed _ hF').mp hm
  let f : C ⟶ A := i ≫ subtype A (⨆ j, F j)
  let W := subrepresentationPreimage f (F j)
  let r : subrepresentation C W ⟶ D := subtype C W ≫ q
  have hr : Function.Surjective (hom r) := by
    rcases Representation.IsIrreducible.surjective_or_eq_zero (hom r) with hs | hz
    · exact hs
    · have hz' := congrArg (fun t => t ⟨c, hj⟩) hz
      change hom q c = 0 at hz'
      exact False.elim (hd (hc.symm.trans hz'))
  refine ⟨j, isSubquotient_iff_exists.mpr
    ⟨subrepresentation C W, subrepresentationPreimageMap f (F j), r, ?_, hr⟩⟩
  exact subrepresentationPreimageMap_injective _ _
    ((subtype_injective _ _).comp hi)

/-- Every irreducible actual subquotient of an arbitrary invariant sum occurs
in one of the summands, with no restriction on the indexing universe. -/
theorem irreducibleSubquotient_iSup (hD : D.IsIrreducible)
    {J : Type uJ} (F : J → Subrepresentation A.representation)
    (h : IsSubquotient D (subrepresentation A (⨆ j, F j))) :
    ∃ j, IsSubquotient D (subrepresentation A (F j)) := by
  classical
  let T : Finset J → Subrepresentation A.representation := fun s => s.sup F
  have hT : Directed (· ≤ ·) T := by
    intro s t
    exact ⟨s ∪ t, Finset.sup_mono Finset.subset_union_left,
      Finset.sup_mono Finset.subset_union_right⟩
  have hsup : (⨆ s, T s) = ⨆ j, F j := by
    apply le_antisymm
    · exact iSup_le fun s => Finset.sup_le fun j _ => le_iSup F j
    · refine iSup_le fun j => ?_
      exact le_iSup_of_le {j} (by simp [T])
  rw [← hsup] at h
  obtain ⟨s, hs⟩ := irreducibleSubquotient_directed_iSup hD T hT h
  obtain ⟨j, _, hj⟩ := irreducibleSubquotient_finset_sup hD F s hs
  exact ⟨j, hj⟩

end Langlands.SmoothRep
