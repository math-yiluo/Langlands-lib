import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.PieceRefinementData
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.PieceMatching
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.MatchingCoefficientLifts
import Langlands.Geometry.Analytic.SpecialCoverIntersectionQuotient
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraGluing

/-! # Matching sections and separation on the full-domain intersection refinement -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.PieceRefinement

open CategoryTheory PairTransitions

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K} {c : Domain.FiniteCover (Domain.whole K R)} {F : LocalAlgebras c}
  (t : PairTransitions F) {V : Domain K R} (d : Domain.FiniteCover V)

local notation "G" => localAlgebras c d F
local notation "T" => transitions c d F t

private def component (m : t.pieceMatching V) (k : Fin (cover c d).size) : (G).algebra k :=
  (t.matchingRestrict (d.map (label c d k).1).subset m).val (label c d k).2

private theorem components_match (m : t.pieceMatching V) (k l : Fin (cover c d).size) :
    (T).leftRestriction k l (component t d m k) = (T).rightRestriction k l (component t d m l) := by
  let E := (G).overlap k l
  let hi := (G).overlapLeft k l
  let hj := (G).overlapRight k l
  let i := (label c d k).2
  let j := (label c d l).2
  let a := (label c d k).1
  let b := (label c d l).1
  let p := (extendMemberInclusion c d k E hi).subset
  let q := (extendMemberInclusion c d l E hj).subset
  let pi := inter_subset_inter (d.map a).subset i
  let qj := inter_subset_inter (d.map b).subset j
  let ei := baseChangeEquiv c d F k E hi
  let ej := baseChangeEquiv c d F l E hj
  let e := t.transitionEquiv i j (V.extend E) (p.trans (member_subset c d k)) (q.trans (member_subset c d l))
  have hl : ei ((G).localMap k E hi (component t d m k)) =
      F.restrict i (p.trans pi) (inter_subset_member V i) (m.val i) := by
    have he := congrArg (fun f => f (component t d m k)) (baseChangeEquiv_left c d F k E hi)
    exact he.trans (F.restrict_restrict i p pi (inter_subset_member V i) (m.val i))
  have hr : ej ((G).localMap l E hj (component t d m l)) =
      F.restrict j (q.trans qj) (inter_subset_member V j) (m.val j) := by
    have he := congrArg (fun f => f (component t d m l)) (baseChangeEquiv_left c d F l E hj)
    exact he.trans (F.restrict_restrict j q qj (inter_subset_member V j) (m.val j))
  apply ej.toAlgEquiv.injective
  change ej (ej.symm (e (ei ((G).localMap k E hi (component t d m k))))) =
    ej ((G).localMap l E hj (component t d m l))
  rw [ej.apply_symm_apply]
  let x := F.restrict i (p.trans pi) (inter_subset_member V i) (m.val i)
  let y := F.restrict j (q.trans qj) (inter_subset_member V j) (m.val j)
  calc
    _ = e x := congrArg e hl
    _ = t.transition i j (V.extend E) (p.trans (member_subset c d k)) (q.trans (member_subset c d l)) x :=
      congrArg (fun f : BoundedAlgHom K
        (F.baseChange i (V.extend E) (p.trans (member_subset c d k)))
        (F.baseChange j (V.extend E) (q.trans (member_subset c d l))) => f x)
        (t.transitionEquiv_eq i j (V.extend E)
          (p.trans (member_subset c d k)) (q.trans (member_subset c d l)))
    _ = y := m.property i j (V.extend E) (p.trans pi) (q.trans qj)
    _ = _ := hr.symm

/-- The original matching sections restrict to the matching algebra on the
refined cover of the entire spectrum of `V.algebra`. -/
def restrictMatching : t.pieceMatching V →ₐ[K] (T).MatchingAlgebra :=
  (AlgHom.pi fun k =>
    (Pi.evalAlgHom K (fun i => t.piece (d.obj (label c d k).1) i) (label c d k).2).comp
      ((t.pieceMatching (d.obj (label c d k).1)).val.comp
        (t.matchingRestrict (d.map (label c d k).1).subset))).codRestrict
    (T).matchingSubalgebra (components_match t d)

@[simp] theorem restrictMatching_projection (m : t.pieceMatching V) (k : Fin (cover c d).size) :
    (T).projection k (restrictMatching t d m) =
      (t.matchingRestrict (d.map (label c d k).1).subset m).val (label c d k).2 := rfl

/-- The restriction to the refined matching algebra preserves the whole
structural map from the given algebra of the domain. -/
theorem restrictMatching_structure :
    (restrictMatching t d).comp (t.matchingStructure V) = (T).structuralMap.toAlgHom := by
  apply AlgHom.ext
  intro x
  apply (T).matching_ext
  intro k
  let a := (label c d k).1
  let i := (label c d k).2
  let W := member c d k
  let D := V.inter (c.obj i)
  let h := inter_subset_inter (d.map a).subset i
  let hv : D.locus ⊆ V.locus := Set.inter_subset_left
  have hc : (restriction h).comp (restriction hv) = (memberInclusion c d k).restriction :=
    (restriction_comp h hv).trans (restriction_eq (memberInclusion c d k) _)
  change ((T).projection k) (restrictMatching t d (t.matchingStructure V x)) =
    (T).projection k ((T).structuralMap x)
  rw [restrictMatching_projection]
  change F.restrict i h (inter_subset_member V i)
      (F.baseMap i D (inter_subset_member V i) (restriction hv x)) = _
  have h₁ := congrArg (fun f => f (restriction hv x)) (F.restrict_baseMap i h (inter_subset_member V i))
  have h₂ := congrArg (F.baseMap i W (member_subset c d k))
    (congrArg (fun f : BoundedAlgHom K V.algebra W.algebra => f x) hc)
  have h₃ := congrArg (fun f : BoundedAlgHom K V.algebra ((G).algebra k) => f x)
    (((T).projection_structuralMap k).trans ((G).structuralMap_eq k))
  exact h₁.trans (h₂.trans h₃.symm)

private def fixedPieceCover (i : Fin c.size) :
    Domain.FiniteCover (Domain.whole K (V.inter (c.obj i)).algebra) where
  size := d.size
  obj a := (V.inter (c.obj i)).relative ((d.obj a).inter (c.obj i))
    (Domain.inclusionOfSubset _ _ (inter_subset_inter (d.map a).subset i))
  map a := ⟨((V.inter (c.obj i)).relative ((d.obj a).inter (c.obj i))
    (Domain.inclusionOfSubset _ _ (inter_subset_inter (d.map a).subset i))).baseMap, rfl⟩
  covers x _ := by
    let D := V.inter (c.obj i)
    have hx : D.spectrumMap x ∈ V.locus ∧ D.spectrumMap x ∈ (c.obj i).locus :=
      D.represents.hasImageIn x
    obtain ⟨a, ha⟩ := d.covers (D.spectrumMap x) hx.1
    refine ⟨a, ?_⟩
    rw [D.relative_locus_eq_preimage]
    exact ⟨ha, hx.2⟩

private theorem eq_of_pieceRestrictions (i : Fin c.size) (x y : t.piece V i)
    (hxy : ∀ a : Fin d.size, t.pieceRestrict (d.map a).subset i x =
      t.pieceRestrict (d.map a).subset i y) : x = y := by
  let D := V.inter (c.obj i)
  let q := F.baseMap i D (inter_subset_member V i)
  let C := (fixedPieceCover (c := c) d i).pullbackWhole q
  apply C.algebra_ext_of_restrict_eq
  intro a
  change Fin d.size at a
  let h := inter_subset_inter (d.map a).subset i
  let e := F.furtherBaseChangeEquiv i h (inter_subset_member V i)
  apply e.toAlgEquiv.injective
  exact (congrArg (fun f => f x) (F.furtherBaseChangeEquiv_left i h (inter_subset_member V i))).trans
    ((hxy a).trans ((congrArg (fun f => f y)
      (F.furtherBaseChangeEquiv_left i h (inter_subset_member V i))).symm))

/-- The original sections over `V` are separated by the refined restrictions. -/
theorem restrictMatching_injective : Function.Injective (restrictMatching t d) := by
  intro m m' h
  apply Subtype.ext
  funext i
  apply eq_of_pieceRestrictions t d i
  intro a
  let p : Fin d.size × Fin c.size → Prop := fun j =>
    (t.matchingRestrict (d.map j.1).subset m).val j.2 =
      (t.matchingRestrict (d.map j.1).subset m').val j.2
  have hp (k : Fin (cover c d).size) : p (label c d k) :=
    congrArg (fun z : (T).MatchingAlgebra => (T).projection k z) h
  have hpair : p (a, i) := (label_index c d a i) ▸ hp (index c d a i)
  exact hpair


/-- If the tuple generates all restricted local pieces on the refined cover,
it generates every matching family on the original domain. -/
theorem generates_of_piecesGenerate {n : ℕ} (s : Fin n → t.pieceMatching V)
    (hs : ∀ a, t.PiecesGenerate (d.obj a)
      (fun k => t.matchingRestrict (d.map a).subset (s k))) : t.Generates V s := by
  let b : Fin n → (T).MatchingAlgebra := fun k => restrictMatching t d (s k)
  have hgen (k : Fin (cover c d).size) :
      Function.Surjective (((G).map k).coefficientMap (fun j => (T).projection k (b j))) := by
    intro y
    exact hs (label c d k).1 (label c d k).2 y
  obtain ⟨M, _, hlift⟩ := (T).exists_matching_coefficient_lifts b hgen
  intro m
  obtain ⟨a, ha, _⟩ := hlift (restrictMatching t d m)
  refine ⟨a, restrictMatching_injective t d ?_⟩
  have hstructure (x : V.algebra) :
      restrictMatching t d (t.matchingStructure V x) = (T).structuralMap x :=
    congrArg (fun f : V.algebra →ₐ[K] (T).MatchingAlgebra => f x) (restrictMatching_structure t d)
  calc
    restrictMatching t d (∑ k, t.matchingStructure V (a k) * s k) =
        (T).structuralMap.coefficientMap b a := by
      rw [map_sum, BoundedAlgHom.coefficientMap_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [map_mul, hstructure]
    _ = _ := ha

end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.PieceRefinement
