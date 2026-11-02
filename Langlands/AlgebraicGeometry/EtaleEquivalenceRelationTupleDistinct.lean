import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleReindex
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationGeometry
import Mathlib.Topology.Clopen

/-! # The clopen locus of distinct related tuples -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u})

/-- The identity section of an étale relation is an open immersion. -/
instance unit_isOpenImmersion : IsOpenImmersion E.unit := by
  let : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion @Etale :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
      (fun _ _ f _ => inferInstanceAs (IsOpenImmersion (pullback.diagonal f)))
  let := E.etale_s
  have : IsOpenImmersion (E.unit ≫ E.s) := by rw [E.unit_s]; infer_instance
  exact MorphismProperty.of_postcomp @IsOpenImmersion E.unit E.s ‹Etale E.s› this

/-- The identity section is closed when the source map of the relation is separated. -/
instance unit_isClosedImmersion [IsSeparated E.s] : IsClosedImmersion E.unit := by
  have : IsClosedImmersion (E.unit ≫ E.s) := by rw [E.unit_s]; infer_instance
  exact IsClosedImmersion.of_comp E.unit E.s

/-- The unique relation arrow between two coordinates of a related tuple. -/
noncomputable def tupleRelation (n : ℕ) (i j : Fin (n + 1)) :
    E.tupleScheme n ⟶ E.R :=
  (E.tupleProjection_related n i j).choose

@[reassoc (attr := simp)]
lemma tupleRelation_t (n : ℕ) (i j : Fin (n + 1)) :
    E.tupleRelation n i j ≫ E.t = E.tupleProjection n i :=
  (E.tupleProjection_related n i j).choose_spec.1

@[reassoc (attr := simp)]
lemma tupleRelation_s (n : ℕ) (i j : Fin (n + 1)) :
    E.tupleRelation n i j ≫ E.s = E.tupleProjection n j :=
  (E.tupleProjection_related n i j).choose_spec.2

@[reassoc]
lemma tupleReindex_relation {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1)) (i j : Fin (m + 1)) :
    E.tupleReindex a ≫ E.tupleRelation m i j =
      E.tupleRelation n (a i) (a j) := by
  apply E.hom_ext <;> simp

/-- The equality locus of two coordinates, defined by pulling back the identity
section of the relation, rather than comparing underlying point images. -/
noncomputable def tupleEqualOpen (n : ℕ) (i j : Fin (n + 1)) :
    (E.tupleScheme n).Opens :=
  E.tupleRelation n i j ⁻¹ᵁ E.unit.opensRange

lemma tupleEqualOpen_isClosed [IsSeparated E.s] (n : ℕ) (i j : Fin (n + 1)) :
    IsClosed (E.tupleEqualOpen n i j : Set (E.tupleScheme n)) :=
  E.unit.isClosedEmbedding.isClosed_range.preimage (E.tupleRelation n i j).continuous

/-- A scheme-valued tuple factors through an equality locus exactly when its
two coordinate morphisms agree. -/
lemma range_subset_tupleEqualOpen_iff (n : ℕ) (i j : Fin (n + 1))
    {T : Scheme.{u}} (f : T ⟶ E.tupleScheme n) :
    Set.range f ⊆ E.tupleEqualOpen n i j ↔
      f ≫ E.tupleProjection n i = f ≫ E.tupleProjection n j := by
  constructor
  · intro h
    have h' : Set.range (f ≫ E.tupleRelation n i j) ⊆ Set.range E.unit := by
      rintro _ ⟨x, rfl⟩
      exact h ⟨x, rfl⟩
    let g := IsOpenImmersion.lift E.unit (f ≫ E.tupleRelation n i j) h'
    have hg : g ≫ E.unit = f ≫ E.tupleRelation n i j :=
      IsOpenImmersion.lift_fac _ _ _
    have ht := congrArg (fun k => k ≫ E.t) hg
    have hs := congrArg (fun k => k ≫ E.s) hg
    simp only [Category.assoc, E.unit_t, E.unit_s, Category.comp_id,
      E.tupleRelation_t, E.tupleRelation_s] at ht hs
    exact ht.symm.trans hs
  · intro h
    have hr : f ≫ E.tupleRelation n i j = f ≫ E.tupleProjection n i ≫ E.unit := by
      apply E.hom_ext <;> simp [h]
    rintro _ ⟨x, rfl⟩
    change (f ≫ E.tupleRelation n i j) x ∈ Set.range E.unit
    rw [hr]
    exact ⟨(f ≫ E.tupleProjection n i) x, rfl⟩

lemma tupleReindex_preimage_equalOpen {m n : ℕ}
    (a : Fin (m + 1) → Fin (n + 1)) (i j : Fin (m + 1)) :
    E.tupleReindex a ⁻¹ᵁ E.tupleEqualOpen m i j =
      E.tupleEqualOpen n (a i) (a j) := by
  simp only [tupleEqualOpen, ← Scheme.Hom.comp_preimage, E.tupleReindex_relation]

/-- The open locus of related tuples with pairwise distinct geometric coordinates. -/
noncomputable def tupleDistinctOpen [IsSeparated E.s] (n : ℕ) :
    (E.tupleScheme n).Opens :=
  ⟨⋂ i : Fin (n + 1), ⋂ j : Fin (n + 1), ⋂ (_ : i ≠ j),
      (E.tupleEqualOpen n i j : Set (E.tupleScheme n))ᶜ,
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => (E.tupleEqualOpen_isClosed n i j).isOpen_compl⟩

@[simp] lemma mem_tupleDistinctOpen [IsSeparated E.s] (n : ℕ) (x : E.tupleScheme n) :
    x ∈ E.tupleDistinctOpen n ↔
      ∀ i j : Fin (n + 1), i ≠ j → x ∉ E.tupleEqualOpen n i j := by
  simp [tupleDistinctOpen]

lemma tupleDistinctOpen_isClosed [IsSeparated E.s] (n : ℕ) :
    IsClosed (E.tupleDistinctOpen n : Set (E.tupleScheme n)) :=
  isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    (E.tupleEqualOpen n i j).isOpen.isClosed_compl

lemma tupleDistinctOpen_isClopen [IsSeparated E.s] (n : ℕ) :
    IsClopen (E.tupleDistinctOpen n : Set (E.tupleScheme n)) :=
  ⟨E.tupleDistinctOpen_isClosed n, (E.tupleDistinctOpen n).isOpen⟩

/-- The scheme of related tuples with pairwise distinct geometric coordinates. -/
noncomputable abbrev tupleDistinctScheme [IsSeparated E.s] (n : ℕ) : Scheme.{u} :=
  (E.tupleDistinctOpen n).toScheme

instance tupleDistinctOpen_isClosedImmersion [IsSeparated E.s] (n : ℕ) :
    IsClosedImmersion (E.tupleDistinctOpen n).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact E.tupleDistinctOpen_isClosed n)

instance tupleDistinctScheme_isAffine [IsAffine E.U] [IsAffine E.R]
    [IsSeparated E.s] (n : ℕ) : IsAffine (E.tupleDistinctScheme n) :=
  isAffine_of_isAffineHom (E.tupleDistinctOpen n).ι

/-- A coordinate on the distinct-tuple scheme. -/
noncomputable abbrev tupleDistinctProjection [IsSeparated E.s] (n : ℕ)
    (i : Fin (n + 1)) : E.tupleDistinctScheme n ⟶ E.U :=
  (E.tupleDistinctOpen n).ι ≫ E.tupleProjection n i

instance tupleDistinctProjection_etale [IsSeparated E.s] (n : ℕ) (i : Fin (n + 1)) :
    Etale (E.tupleDistinctProjection n i) := by
  unfold tupleDistinctProjection
  infer_instance

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
