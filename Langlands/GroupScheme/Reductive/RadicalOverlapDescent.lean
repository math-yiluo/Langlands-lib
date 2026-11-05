import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof

/-! # Unipotent radicals with invariant overlap images -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open Descent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {U : GroupScheme (Spec (CommRingCat.of K))}
    {i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G}

/-- A radical over the ground field, with an actual source isomorphism recovering
the specified inclusion after extension of scalars. -/
structure UnipotentRadicalDescent
    (i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G) where
  source : GroupScheme (Spec (CommRingCat.of k))
  inclusion : source ⟶ G
  comparison : (GroupScheme.baseChange (algebraBaseMap k K)).obj source ≅ U
  isRadical : IsUnipotentRadical inclusion
  recovers : (GroupScheme.baseChange (algebraBaseMap k K)).map inclusion =
    comparison.hom ≫ i

/-- An invariant overlap image allows effective descent of the full represented
unipotent radical, including recovery of the actual inclusion. -/
theorem IsUnipotentRadical.exists_descent_of_overlap_range_eq
    (hi : IsUnipotentRadical i)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange (fst (algebraBaseMap k K))).map i ≫
          (canonicalOverlap (algebraBaseMap k K) G).hom) =
      SubgroupFunctor.range
        ((GroupScheme.baseChange (snd (algebraBaseMap k K))).map i)) :
    ∃ (U₀ : GroupScheme (Spec (CommRingCat.of k))) (j : U₀ ⟶ G)
      (e : (GroupScheme.baseChange (algebraBaseMap k K)).obj U₀ ≅ U),
      IsUnipotentRadical j ∧
        (GroupScheme.baseChange (algebraBaseMap k K)).map j = e.hom ≫ i := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Flat (algebraBaseMap k K) := (fieldExtension_fpqc k K).2.1
  let : Surjective (algebraBaseMap k K) := (fieldExtension_fpqc k K).1
  obtain ⟨U₀, j, e, _, hj, he⟩ :=
    hi.isClosedSubgroup.exists_descent_of_overlap_range_eq (algebraBaseMap k K) h
  refine ⟨U₀, j, e, ?_, he⟩
  apply IsUnipotentRadical.of_baseChange (K := K) (hclosed := hj)
  rw [he]
  exact hi.precomp_iso e

/-- Choose the effective descended radical and its recovering source isomorphism
from equality of the two overlap images. -/
def IsUnipotentRadical.descentOfOverlapRangeEq
    (hi : IsUnipotentRadical i)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange (fst (algebraBaseMap k K))).map i ≫
          (canonicalOverlap (algebraBaseMap k K) G).hom) =
      SubgroupFunctor.range
        ((GroupScheme.baseChange (snd (algebraBaseMap k K))).map i)) :
    UnipotentRadicalDescent i := by
  classical
  choose U₀ j e hj he using hi.exists_descent_of_overlap_range_eq h
  exact ⟨U₀, j, e, hj, he⟩

omit [IsAffineHom G.X.hom] in
/-- A descended radical has trivial image when the original group has trivial
unipotent radical. The conclusion retains all relative test schemes. -/
theorem SubgroupFunctor.range_eq_bot_of_radical_descent
    (hG : HasTrivialUnipotentRadical G)
    {U₀ : GroupScheme (Spec (CommRingCat.of k))} {j : U₀ ⟶ G}
    (hj : IsUnipotentRadical j)
    (e : (GroupScheme.baseChange (algebraBaseMap k K)).obj U₀ ≅ U)
    (he : (GroupScheme.baseChange (algebraBaseMap k K)).map j = e.hom ≫ i) :
    SubgroupFunctor.range i = ⊥ := by
  have hbase : SubgroupFunctor.range
      ((GroupScheme.baseChange (algebraBaseMap k K)).map j) = ⊥ := by
    rw [SubgroupFunctor.range_baseChangeHom, hj.range_eq_bot hG,
      SubgroupFunctor.bot_baseChange]
  rw [he, SubgroupFunctor.range_iso_precomp] at hbase
  exact hbase

/-- Overlap invariance of a represented radical suffices for preservation of
triviality of the unipotent radical under the field extension. -/
theorem HasTrivialUnipotentRadical.baseChange_of_radical_overlap_range_eq
    (hG : HasTrivialUnipotentRadical G) (hi : IsUnipotentRadical i)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange (fst (algebraBaseMap k K))).map i ≫
          (canonicalOverlap (algebraBaseMap k K) G).hom) =
      SubgroupFunctor.range
        ((GroupScheme.baseChange (snd (algebraBaseMap k K))).map i)) :
    HasTrivialUnipotentRadical
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) := by
  obtain ⟨U₀, j, e, hj, he⟩ := hi.exists_descent_of_overlap_range_eq h
  exact hi.hasTrivialUnipotentRadical_iff.mpr
    (SubgroupFunctor.range_eq_bot_of_radical_descent hG hj e he)

/-- A pseudo-reductive group remains pseudo-reductive under finite Galois
extension, with no supplied radical or descent datum in the hypotheses. -/
theorem IsPseudoReductive.baseChange_finiteGalois
    [FiniteDimensional k K] [IsGalois k K] (hG : IsPseudoReductive G) :
    IsPseudoReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) := by
  let b := algebraBaseMap k K
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : Smooth ((GroupScheme.baseChange b).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  let : ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  obtain ⟨U, i, hi⟩ := unipotentRadicalExistence K ((GroupScheme.baseChange b).obj G)
  obtain ⟨U₀, j, e, hj, he⟩ := hi.finiteGaloisRadical
  exact ⟨inferInstance, inferInstance, inferInstance,
    hi.hasTrivialUnipotentRadical_iff.mpr
      (SubgroupFunctor.range_eq_bot_of_radical_descent hG.hasTrivialUnipotentRadical hj e he)⟩

end Langlands.GroupScheme
