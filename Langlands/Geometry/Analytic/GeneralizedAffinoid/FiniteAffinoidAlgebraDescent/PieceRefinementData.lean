import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.LocalBaseChangeEquivalence
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocalization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Proof

/-! # Finite local algebras on the intersections of two full-domain covers -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.PieceRefinement

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K}
  (c : Domain.FiniteCover (Domain.whole K R)) {V : Domain K R} (d : Domain.FiniteCover V)

/-- The index that records one member of the cover of `V` and one original
cover member. -/
def index (a : Fin d.size) (i : Fin c.size) : Fin (d.size * c.size) :=
  finProdFinEquiv (a, i)

/-- Decode the two original cover indices. -/
def label (k : Fin (d.size * c.size)) : Fin d.size × Fin c.size := finProdFinEquiv.symm k

@[simp] theorem label_index (a : Fin d.size) (i : Fin c.size) : label c d (index c d a i) = (a, i) :=
  finProdFinEquiv.symm_apply_apply _

/-- The literal original intersection associated to the two indices. -/
abbrev member (k : Fin (d.size * c.size)) : Domain K R :=
  (d.obj (label c d k).1).inter (c.obj (label c d k).2)

/-- Its original actual inclusion into `V`. -/
def memberInclusion (k : Fin (d.size * c.size)) : member c d k ⟶ V :=
  (d.obj (label c d k).1).interLeft (c.obj (label c d k).2) ≫ d.map (label c d k).1

theorem member_subset (k : Fin (d.size * c.size)) :
    (member c d k).locus ⊆ (c.obj (label c d k).2).locus := Set.inter_subset_right

/-- Regard the intersection as an actual full domain over `V.algebra`. -/
abbrev relativeMember (k : Fin (d.size * c.size)) : Domain K V.algebra :=
  V.relative (member c d k) (memberInclusion c d k)

/-- The original intersections cover the whole spectrum of the algebra of `V`. -/
def cover : Domain.FiniteCover (Domain.whole K V.algebra) where
  size := d.size * c.size
  obj := relativeMember c d
  map k := ⟨(relativeMember c d k).baseMap, rfl⟩
  covers x _ := by
    obtain ⟨a, ha⟩ := d.covers (V.spectrumMap x) (V.represents.hasImageIn x)
    obtain ⟨i, hi⟩ := c.covers (V.spectrumMap x) (Set.mem_univ _)
    let k := index c d a i
    refine ⟨k, ?_⟩
    change x ∈ (V.relative (member c d k) (memberInclusion c d k)).locus
    rw [V.relative_locus_eq_preimage]
    change V.spectrumMap x ∈ (member c d k).locus
    exact (show (V.spectrumMap x ∈ (member c d k).locus) from by
      change V.spectrumMap x ∈ (d.obj (label c d k).1).locus ∩ (c.obj (label c d k).2).locus
      simpa only [k, label_index, Set.mem_inter_iff] using And.intro ha hi)

variable (F : LocalAlgebras c)

/-- The original local algebra changed to each actual refinement member. -/
def localAlgebras : LocalAlgebras (cover c d) where
  algebra k := F.baseChange (label c d k).2 (member c d k) (member_subset c d k)
  map k := F.baseMap (label c d k).2 (member c d k) (member_subset c d k)
  finite k := AffinoidPushout.rightMap_isFiniteBanach _ _ (F.finite (label c d k).2)

/-- Extend a relative inclusion to the original ambient spectrum. Its algebra
map remains the original bounded restriction. -/
def extendMemberInclusion (k : Fin (d.size * c.size)) (E : Domain K V.algebra)
    (h : E.locus ⊆ (relativeMember c d k).locus) : V.extend E ⟶ member c d k where
  restriction := restriction (R := V.algebra) (E := E) (D := relativeMember c d k) h
  comp_baseMap := by
    let r := restriction (R := V.algebra) (E := E) (D := relativeMember c d k) h
    have hp := (memberInclusion c d k).comp_baseMap
    have hr := (Domain.inclusionOfSubset E (relativeMember c d k) h).comp_baseMap
    change r.comp (member c d k).baseMap = E.baseMap.comp V.baseMap
    calc
      _ = r.comp ((memberInclusion c d k).restriction.comp V.baseMap) := congrArg r.comp hp.symm
      _ = (r.comp (relativeMember c d k).baseMap).comp V.baseMap :=
        (BoundedAlgHom.comp_assoc _ _ _).symm
      _ = _ := congrArg (fun q => q.comp V.baseMap) hr

private def furtherBaseChangeAlongMap {D E : Domain K R} (i : Fin c.size)
    (h : E.locus ⊆ D.locus) (hi : D.locus ⊆ (c.obj i).locus)
    (r : BoundedAlgHom K D.algebra E.algebra) (hr : restriction h = r) :
    BoundedAlgEquiv K (AffinoidPushout.algebra (F.baseMap i D hi) r)
      (F.baseChange i E (h.trans hi)) :=
  hr ▸ F.furtherBaseChangeEquiv i h hi

private theorem furtherBaseChangeAlongMap_left {D E : Domain K R} (i : Fin c.size)
    (h : E.locus ⊆ D.locus) (hi : D.locus ⊆ (c.obj i).locus)
    (r : BoundedAlgHom K D.algebra E.algebra) (hr : restriction h = r) :
    (furtherBaseChangeAlongMap c F i h hi r hr).toBoundedAlgHom.comp
      (AffinoidPushout.leftMap (F.baseMap i D hi) r) = F.restrict i h hi := by
  subst r
  exact F.furtherBaseChangeEquiv_left i h hi

private theorem furtherBaseChangeAlongMap_right {D E : Domain K R} (i : Fin c.size)
    (h : E.locus ⊆ D.locus) (hi : D.locus ⊆ (c.obj i).locus)
    (r : BoundedAlgHom K D.algebra E.algebra) (hr : restriction h = r) :
    (furtherBaseChangeAlongMap c F i h hi r hr).toBoundedAlgHom.comp
      (AffinoidPushout.rightMap (F.baseMap i D hi) r) = F.baseMap i E (h.trans hi) := by
  subst r
  exact F.furtherBaseChangeEquiv_right i h hi

/-- Refined pushout and direct original pushout have the same bounded algebra
and the same original coefficient map. -/
def baseChangeEquiv (k : Fin (cover c d).size) (E : Domain K V.algebra)
    (h : E.locus ⊆ ((cover c d).obj k).locus) :
    BoundedAlgEquiv K ((localAlgebras c d F).baseChange k E h)
      (F.baseChange (label c d k).2 (V.extend E)
        ((extendMemberInclusion c d k E h).subset.trans (member_subset c d k))) :=
  let p := extendMemberInclusion c d k E h
  furtherBaseChangeAlongMap c F (D := member c d k) (E := V.extend E) (label c d k).2 p.subset
    (member_subset c d k) (restriction (R := V.algebra) (E := E) (D := (cover c d).obj k) h)
    (restriction_eq p p.subset)

@[simp] theorem baseChangeEquiv_left (k : Fin (cover c d).size) (E : Domain K V.algebra)
    (h : E.locus ⊆ ((cover c d).obj k).locus) :
    (baseChangeEquiv c d F k E h).toBoundedAlgHom.comp ((localAlgebras c d F).localMap k E h) =
      F.restrict (label c d k).2 (extendMemberInclusion c d k E h).subset (member_subset c d k) :=
  furtherBaseChangeAlongMap_left c F _ _ _ _ _

@[simp] theorem baseChangeEquiv_right (k : Fin (cover c d).size) (E : Domain K V.algebra)
    (h : E.locus ⊆ ((cover c d).obj k).locus) :
    (baseChangeEquiv c d F k E h).toBoundedAlgHom.comp ((localAlgebras c d F).baseMap k E h) =
      F.baseMap (label c d k).2 (V.extend E)
        ((extendMemberInclusion c d k E h).subset.trans (member_subset c d k)) :=
  furtherBaseChangeAlongMap_right c F _ _ _ _ _

variable (t : PairTransitions F)

local notation "G" => localAlgebras c d F

/-- The refined overlap comparison is conjugation of the actual restricted
original transition by the two direct-base-change comparisons. -/
def overlapEquiv (k l : Fin (cover c d).size) :
    BoundedAlgEquiv K
      ((G).baseChange k ((G).overlap k l) ((G).overlapLeft k l))
      ((G).baseChange l ((G).overlap k l) ((G).overlapRight k l)) :=
  let E := (G).overlap k l
  let hi := (extendMemberInclusion c d k E ((G).overlapLeft k l)).subset.trans (member_subset c d k)
  let hj := (extendMemberInclusion c d l E ((G).overlapRight k l)).subset.trans (member_subset c d l)
  let e := t.transitionEquiv (label c d k).2 (label c d l).2 (V.extend E) hi hj
  (baseChangeEquiv c d F k E ((G).overlapLeft k l)).trans
    (e.trans (baseChangeEquiv c d F l E ((G).overlapRight k l)).symm)

private theorem overlapEquiv_over_base (k l : Fin (cover c d).size) :
    (overlapEquiv c d F t k l).toBoundedAlgHom.comp ((G).baseMap k ((G).overlap k l) ((G).overlapLeft k l)) =
      (G).baseMap l ((G).overlap k l) ((G).overlapRight k l) := by
  let E := (G).overlap k l
  let h := (G).overlapLeft k l
  let h' := (G).overlapRight k l
  let i := (label c d k).2
  let j := (label c d l).2
  let hi := (extendMemberInclusion c d k E h).subset.trans (member_subset c d k)
  let hj := (extendMemberInclusion c d l E h').subset.trans (member_subset c d l)
  let ei := baseChangeEquiv c d F k E h
  let ej := baseChangeEquiv c d F l E h'
  let e := t.transitionEquiv i j (V.extend E) hi hj
  apply BoundedAlgHom.ext
  intro a
  apply ej.toAlgEquiv.injective
  change ej (ej.symm (e (ei ((G).baseMap k E h a)))) = ej ((G).baseMap l E h' a)
  rw [ej.apply_symm_apply]
  calc
    _ = e (F.baseMap i (V.extend E) hi a) := congrArg e
      (congrArg (fun f => f a) (baseChangeEquiv_right c d F k E h))
    _ = t.transition i j (V.extend E) hi hj (F.baseMap i (V.extend E) hi a) :=
      congrArg (fun f => f (F.baseMap i (V.extend E) hi a)) (t.transitionEquiv_eq i j (V.extend E) hi hj)
    _ = F.baseMap j (V.extend E) hj a := congrArg (fun f => f a) (t.transition_baseMap i j (V.extend E) hi hj)
    _ = _ := (congrArg (fun f => f a) (baseChangeEquiv_right c d F l E h')).symm

/-- Ordinary pairwise transitions on the refined cover over `V.algebra`. -/
def transitions : PairTransitions (localAlgebras c d F) where
  equiv := overlapEquiv c d F t
  over_base := overlapEquiv_over_base c d F t

end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.PieceRefinement
