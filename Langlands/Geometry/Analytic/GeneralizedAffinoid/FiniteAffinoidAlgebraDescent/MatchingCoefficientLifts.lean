import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.CoefficientRelations
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.FiniteBanachBounds
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.FreeSquareZeroCover
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.FreeSquareZeroIdeals
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.IdealResidueGluing
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.MatchingAlgebra

/-! # Controlled matching coefficients from local module generators -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.PairTransitions

open CategoryTheory TrivSqZeroExt

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K}
  {c : Domain.FiniteCover (Domain.whole K R)} {F : LocalAlgebras c}
  (t : PairTransitions F) {n : ℕ} (s : Fin n → t.MatchingAlgebra)

local notation "C" => FreeSquareZero.cover n c
private abbrev generators (i : Fin c.size) (k : Fin n) := t.projection i (s k)

local notation "b" => (generators t s)

/-- The local coefficient relations, as a closed ideal in the degree-one
part of the square-zero algebra of the original cover member. -/
def coefficientIdeal (i : Fin c.size) : Ideal (FreeSquareZero.algebra K (c.obj i).algebra n) :=
  FreeSquareZero.ideal (relations (F.map i) (b i))

private theorem coefficientIdeal_closed (i : Fin c.size) :
    IsClosed (t.coefficientIdeal s i : Set (FreeSquareZero.algebra K (c.obj i).algebra n)) :=
  FreeSquareZero.isClosed_ideal _

private theorem overlapGenerators (i j : Fin c.size) :
    (fun k => t.leftRestriction i j (b i k)) = (fun k => t.rightRestriction i j (b j k)) :=
  funext fun k => (s k).property i j

private theorem overlapCoefficient_left (i j : Fin c.size) (a : Fin n → (c.obj i).algebra) :
    t.leftRestriction i j ((F.map i).coefficientMap (b i) a) =
      (F.baseMap j (F.overlap i j) (F.overlapRight i j)).coefficientMap
        (fun k => t.rightRestriction i j (b j k)) (fun k => restriction (F.overlapLeft i j) (a k)) := by
  have h : (t.leftRestriction i j).comp (F.map i) =
      (F.baseMap j (F.overlap i j) (F.overlapRight i j)).comp (restriction (F.overlapLeft i j)) := by
    change ((t.equiv i j).toBoundedAlgHom.comp
      (F.localMap i (F.overlap i j) (F.overlapLeft i j))).comp (F.map i) = _
    rw [BoundedAlgHom.comp_assoc, F.condition, ← BoundedAlgHom.comp_assoc, t.over_base]
  rw [← t.overlapGenerators s i j]
  exact coefficientMap_natural _ _ _ _ h _ _

private theorem overlapCoefficient_right (i j : Fin c.size) (a : Fin n → (c.obj j).algebra) :
    t.rightRestriction i j ((F.map j).coefficientMap (b j) a) =
      (F.baseMap j (F.overlap i j) (F.overlapRight i j)).coefficientMap
        (fun k => t.rightRestriction i j (b j k)) (fun k => restriction (F.overlapRight i j) (a k)) :=
  coefficientMap_natural _ _ _ _ (F.condition j (F.overlap i j) (F.overlapRight i j)) _ _

private theorem overlapRelations (i j : Fin c.size) :
    relations (F.baseMap i (F.overlap i j) (F.overlapLeft i j))
        (fun k => F.localMap i (F.overlap i j) (F.overlapLeft i j) (b i k)) =
      relations (F.baseMap j (F.overlap i j) (F.overlapRight i j))
        (fun k => F.localMap j (F.overlap i j) (F.overlapRight i j) (b j k)) := by
  ext a
  simp only [mem_relations]
  have h := coefficientMap_natural
    (F.baseMap i (F.overlap i j) (F.overlapLeft i j))
    (F.baseMap j (F.overlap i j) (F.overlapRight i j))
    (BoundedAlgHom.id K (F.overlap i j).algebra) (t.equiv i j).toBoundedAlgHom
    (by rw [BoundedAlgHom.comp_id]; exact t.over_base i j)
    (fun k => F.localMap i (F.overlap i j) (F.overlapLeft i j) (b i k)) a
  change (t.equiv i j) ((F.baseMap i (F.overlap i j) (F.overlapLeft i j)).coefficientMap
      (fun k => F.localMap i (F.overlap i j) (F.overlapLeft i j) (b i k)) a) = _ at h
  change _ = (F.baseMap j (F.overlap i j) (F.overlapRight i j)).coefficientMap
      (fun k => t.leftRestriction i j (b i k)) a at h
  rw [t.overlapGenerators s i j] at h
  change _ = 0 ↔ (F.baseMap j (F.overlap i j) (F.overlapRight i j)).coefficientMap
      (fun k => t.rightRestriction i j (b j k)) a = 0
  rw [← h]
  exact ((t.equiv i j).toAlgEquiv.map_eq_zero_iff).symm

private theorem coefficientIdeal_restrict
    (hs : ∀ i : Fin c.size, Function.Surjective
      ((F.map i).coefficientMap (fun k => t.projection i (s k)))) (i : Fin c.size) {E : Domain K R}
    (p : E ⟶ c.obj i) (h : E.locus ⊆ (c.obj i).locus) :
    (FreeSquareZero.map p.restriction n).closedIdealMap (t.coefficientIdeal s i) =
      FreeSquareZero.ideal (relations (F.baseMap i E h) (fun k => F.localMap i E h (b i k))) := by
  change (FreeSquareZero.map p.restriction n).closedIdealMap
    (FreeSquareZero.ideal (relations (F.map i) (b i))) = _
  rw [← restriction_eq p h, FreeSquareZero.closedIdealMap_ideal]
  exact congrArg (fun S : Submodule E.algebra (Fin n → E.algebra) => FreeSquareZero.ideal S)
    (relations_pushout (F.map i) (b i) (F.finite i) (hs i) (restriction h)).symm


omit [CompleteSpace K] in
private theorem mem_of_equiv_mem_closedIdealMap {A B : PresentedAffinoidAlgebra K}
    (e : BoundedAlgEquiv K A B) (J : Ideal A) (hJ : IsClosed (J : Set A)) (x : A)
    (hx : e x ∈ e.toBoundedAlgHom.closedIdealMap J) : x ∈ J := by
  let N := Ideal.comap e.symm.toBoundedAlgHom.toAlgHom.toRingHom J
  have hN : IsClosed (N : Set B) := hJ.preimage e.symm.toBoundedAlgHom.continuous
  have hle := (e.toBoundedAlgHom.closedIdealMap_le_iff J N hN).2 (by
    intro a ha
    change e.symm (e a) ∈ J
    simpa only [BoundedAlgEquiv.symm_apply_apply] using ha)
  have h := hle hx
  change e.symm (e x) ∈ J at h
  exact (e.symm_apply_apply x) ▸ h

private theorem coefficientIdeal_overlap
    (hs : ∀ i : Fin c.size, Function.Surjective
      ((F.map i).coefficientMap (fun k => t.projection i (s k)))) (i j : Fin c.size) :
    (FreeSquareZero.intersectionEquiv n (c.obj i) (c.obj j)).toBoundedAlgHom.closedIdealMap
      (((FreeSquareZero.domain n (c.obj i)).interLeft (FreeSquareZero.domain n (c.obj j))).restriction.closedIdealMap (t.coefficientIdeal s i)) =
        FreeSquareZero.ideal (relations (F.baseMap j (F.overlap i j) (F.overlapRight i j))
          (fun k => t.rightRestriction i j (b j k))) := by
  let e := FreeSquareZero.intersectionEquiv n (c.obj i) (c.obj j)
  let p := (FreeSquareZero.domain n (c.obj i)).interLeft (FreeSquareZero.domain n (c.obj j))
  have hcomp := BoundedAlgHom.closedIdealMap_comp p.restriction e.toBoundedAlgHom (t.coefficientIdeal s i)
  have hleg := congrArg (fun q : BoundedAlgHom K (FreeSquareZero.algebra K (c.obj i).algebra n)
      (FreeSquareZero.algebra K (F.overlap i j).algebra n) => q.closedIdealMap (t.coefficientIdeal s i))
    (FreeSquareZero.intersectionEquiv_comp_interLeft n (c.obj i) (c.obj j))
  have hkernel := t.coefficientIdeal_restrict s hs i (E := F.overlap i j)
    ((c.obj i).interLeft (c.obj j)) (F.overlapLeft i j)
  have hrelation := congrArg (fun S : Submodule (F.overlap i j).algebra (Fin n → (F.overlap i j).algebra) =>
    FreeSquareZero.ideal S) (t.overlapRelations s i j)
  exact hcomp.trans (hleg.trans (hkernel.trans hrelation))

private theorem coefficientIdeal_compatible
    (hs : ∀ i : Fin c.size, Function.Surjective
      ((F.map i).coefficientMap (fun k => t.projection i (s k)))) : (C).IdealCompatible (t.coefficientIdeal s) := by
  intro i j
  change Fin c.size at i j
  let e := FreeSquareZero.intersectionEquiv n (c.obj i) (c.obj j)
  let I := ((FreeSquareZero.domain n (c.obj i)).interLeft (FreeSquareZero.domain n (c.obj j))).restriction.closedIdealMap (t.coefficientIdeal s i)
  let J := ((FreeSquareZero.domain n (c.obj i)).interRight (FreeSquareZero.domain n (c.obj j))).restriction.closedIdealMap (t.coefficientIdeal s j)
  have hI : IsClosed (I : Set ((FreeSquareZero.domain n (c.obj i)).inter (FreeSquareZero.domain n (c.obj j))).algebra) :=
    BoundedAlgHom.isClosed_closedIdealMap _ _
  have hJ : IsClosed (J : Set ((FreeSquareZero.domain n (c.obj i)).inter (FreeSquareZero.domain n (c.obj j))).algebra) :=
    BoundedAlgHom.isClosed_closedIdealMap _ _
  have hright : e.toBoundedAlgHom.closedIdealMap J =
      FreeSquareZero.ideal (relations (F.baseMap j (F.overlap i j) (F.overlapRight i j))
        (fun k => t.rightRestriction i j (b j k))) := by
    let p := (FreeSquareZero.domain n (c.obj i)).interRight (FreeSquareZero.domain n (c.obj j))
    have hcomp := BoundedAlgHom.closedIdealMap_comp p.restriction e.toBoundedAlgHom (t.coefficientIdeal s j)
    have hleg := congrArg (fun q : BoundedAlgHom K (FreeSquareZero.algebra K (c.obj j).algebra n)
        (FreeSquareZero.algebra K (F.overlap i j).algebra n) => q.closedIdealMap (t.coefficientIdeal s j))
      (FreeSquareZero.intersectionEquiv_comp_interRight n (c.obj i) (c.obj j))
    have hkernel := t.coefficientIdeal_restrict s hs j (E := F.overlap i j)
      ((c.obj i).interRight (c.obj j)) (F.overlapRight i j)
    exact hcomp.trans (hleg.trans hkernel)
  have h := (t.coefficientIdeal_overlap s hs i j).trans hright.symm
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · exact mem_of_equiv_mem_closedIdealMap e J hJ x
      (h ▸ e.toBoundedAlgHom.mem_closedIdealMap hx)
  · exact mem_of_equiv_mem_closedIdealMap e I hI x
      (h.symm ▸ e.toBoundedAlgHom.mem_closedIdealMap hx)

private theorem linearElement_overlap (i j : Fin c.size)
    (a : Fin n → (c.obj i).algebra) (d : Fin n → (c.obj j).algebra) :
    FreeSquareZero.intersectionEquiv n (c.obj i) (c.obj j)
        (((FreeSquareZero.domain n (c.obj i)).interLeft (FreeSquareZero.domain n (c.obj j))).restriction (FreeSquareZero.linearElement a) -
          ((FreeSquareZero.domain n (c.obj i)).interRight (FreeSquareZero.domain n (c.obj j))).restriction (FreeSquareZero.linearElement d)) =
      FreeSquareZero.linearElement (fun k => restriction (F.overlapLeft i j) (a k)) -
        FreeSquareZero.linearElement (fun k => restriction (F.overlapRight i j) (d k)) := by
  let e := FreeSquareZero.intersectionEquiv n (c.obj i) (c.obj j)
  change e.toAlgEquiv (_ - _) = _
  rw [map_sub]
  congr 1
  · have h := congrArg (fun f : BoundedAlgHom K (FreeSquareZero.domain n (c.obj i)).algebra (FreeSquareZero.domain n (F.overlap i j)).algebra =>
        f (FreeSquareZero.linearElement a))
      (FreeSquareZero.intersectionEquiv_comp_interLeft n (c.obj i) (c.obj j))
    refine h.trans ?_
    change FreeSquareZero.map ((c.obj i).interLeft (c.obj j)).restriction n
      (FreeSquareZero.linearElement a) = _
    rw [← F.overlapLeft_restriction i j]
    exact FreeSquareZero.map_linearElement (restriction (F.overlapLeft i j)) a
  · have h := congrArg (fun f : BoundedAlgHom K (FreeSquareZero.domain n (c.obj j)).algebra (FreeSquareZero.domain n (F.overlap i j)).algebra =>
        f (FreeSquareZero.linearElement d))
      (FreeSquareZero.intersectionEquiv_comp_interRight n (c.obj i) (c.obj j))
    refine h.trans ?_
    change FreeSquareZero.map ((c.obj i).interRight (c.obj j)).restriction n
      (FreeSquareZero.linearElement d) = _
    rw [← F.overlapRight_restriction i j]
    exact FreeSquareZero.map_linearElement (restriction (F.overlapRight i j)) d

private theorem coefficientResidues
    (hs : ∀ i : Fin c.size, Function.Surjective
      ((F.map i).coefficientMap (fun k => t.projection i (s k)))) (m : t.MatchingAlgebra) (a : ∀ i : Fin c.size, Fin n → (c.obj i).algebra)
    (ha : ∀ i, (F.map i).coefficientMap (b i) (a i) = t.projection i m) :
    (C).ResidueCompatible (t.coefficientIdeal s) (fun i => FreeSquareZero.linearElement (a i)) := by
  intro i j
  change Fin c.size at i j
  change ((FreeSquareZero.domain n (c.obj i)).interLeft (FreeSquareZero.domain n (c.obj j))).restriction
      (FreeSquareZero.linearElement (a i)) -
    ((FreeSquareZero.domain n (c.obj i)).interRight (FreeSquareZero.domain n (c.obj j))).restriction
      (FreeSquareZero.linearElement (a j)) ∈ _
  apply mem_of_equiv_mem_closedIdealMap (FreeSquareZero.intersectionEquiv n (c.obj i) (c.obj j))
    _ (BoundedAlgHom.isClosed_closedIdealMap _ _)
  change _ ∈ (FreeSquareZero.intersectionEquiv n (c.obj i) (c.obj j)).toBoundedAlgHom.closedIdealMap
    (BoundedAlgHom.closedIdealMap
      ((FreeSquareZero.domain n (c.obj i)).interLeft (FreeSquareZero.domain n (c.obj j))).restriction
      (t.coefficientIdeal s i))
  rw [t.coefficientIdeal_overlap s hs i j, linearElement_overlap (F := F) i j (a i) (a j)]
  apply (FreeSquareZero.mem_ideal
    (relations (F.baseMap j (F.overlap i j) (F.overlapRight i j))
      (fun k => t.rightRestriction i j (b j k))) _).mpr
  let e := FreeSquareZero.coordinateEquiv K (F.overlap i j).algebra n
  change (e.toAlgEquiv (_ - _)).fst = 0 ∧ (e.toAlgEquiv (_ - _)).snd ∈ _
  rw [map_sub]
  change (e (FreeSquareZero.linearElement _) - e (FreeSquareZero.linearElement _)).fst = 0 ∧
    (e (FreeSquareZero.linearElement _) - e (FreeSquareZero.linearElement _)).snd ∈ _
  simp only [e, FreeSquareZero.coordinateEquiv_linearElement, fst_sub, fst_inr, sub_zero,
    snd_sub, snd_inr, mem_relations, map_sub, sub_eq_zero, true_and]
  rw [← t.overlapCoefficient_left s i j, ← t.overlapCoefficient_right s i j, ha i, ha j]
  exact m.property i j


private theorem coefficient_eq_of_residue (i : Fin c.size)
    (x : FreeSquareZero.algebra K R n) (a : Fin n → (c.obj i).algebra)
    (hx : FreeSquareZero.map (c.obj i).baseMap n x - FreeSquareZero.linearElement a ∈
      t.coefficientIdeal s i) :
    (F.map i).coefficientMap (b i)
        (fun k => (c.obj i).baseMap ((FreeSquareZero.coordinateEquiv K R n x).snd k)) =
      (F.map i).coefficientMap (b i) a := by
  let e := FreeSquareZero.coordinateEquiv K (c.obj i).algebra n
  have hm := ((FreeSquareZero.mem_ideal (relations (F.map i) (b i)) _).mp hx).2
  change (e.toAlgEquiv (_ - _)).snd ∈ _ at hm
  rw [map_sub] at hm
  change (e (FreeSquareZero.map (c.obj i).baseMap n x) - e (FreeSquareZero.linearElement a)).snd ∈ _ at hm
  simp only [e, FreeSquareZero.coordinateEquiv_map, FreeSquareZero.coordinateEquiv_linearElement,
    snd_sub, snd_inr, mem_relations, map_sub, sub_eq_zero] at hm
  exact hm

/-- Local module generation by a single matching tuple supplies uniform
norm-controlled global coefficients for that same tuple. -/
theorem exists_matching_coefficient_lifts
    (hs : ∀ i : Fin c.size, Function.Surjective
      ((F.map i).coefficientMap (fun k => t.projection i (s k)))) :
    ∃ M > 0, ∀ m : t.MatchingAlgebra, ∃ a : Fin n → R,
      t.structuralMap.coefficientMap s a = m ∧ ‖a‖ ≤ M * ‖m‖ := by
  classical
  choose L hL hcoef using fun i : Fin c.size => (F.finite i).exists_coefficient_lifts (b i) (hs i)
  choose D hD hnorm using fun i : Fin c.size => (FreeSquareZero.coordinateEquiv K (c.obj i).algebra n).inverse_bounded
  obtain ⟨B, hB, hlift⟩ := (C).exists_residue_lift (t.coefficientIdeal s)
    (t.coefficientIdeal_closed s) (t.coefficientIdeal_compatible s hs)
  obtain ⟨E, hE, hnormE⟩ := (FreeSquareZero.coordinateEquiv K R n).bounded
  let M := (∑ i : Fin c.size, D i * L i) + 1
  have hM : 0 < M := by
    have hsum : 0 ≤ ∑ i : Fin c.size, D i * L i := Finset.sum_nonneg
      (fun i _ => mul_nonneg (hD i).le (hL i).le)
    dsimp [M]
    linarith
  have hMi (i : Fin c.size) : D i * L i ≤ M := by
    have h := Finset.single_le_sum (f := fun j : Fin c.size => D j * L j)
      (fun j _ => mul_nonneg (hD j).le (hL j).le) (Finset.mem_univ i)
    dsimp [M]
    linarith
  refine ⟨E * B * M, mul_pos (mul_pos hE hB) hM, fun m => ?_⟩
  choose v hv hvn using fun i : Fin c.size => hcoef i (t.projection i m)
  let z (i : Fin (C).size) : ((C).obj i).algebra := FreeSquareZero.linearElement (v i)
  obtain ⟨x, hx, hxn⟩ := hlift z (t.coefficientResidues s hs m v hv)
  let e := FreeSquareZero.coordinateEquiv K R n
  let a := (e x).snd
  refine ⟨a, ?_, ?_⟩
  · apply t.matching_ext
    intro i
    calc
      t.projection i (t.structuralMap.coefficientMap s a) =
          (F.map i).coefficientMap (b i) (fun k => (c.obj i).baseMap (a k)) := by
        simp only [BoundedAlgHom.coefficientMap_apply]
        change (t.projection i).toAlgHom (∑ k, t.structuralMap (a k) * s k) = _
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [map_mul]
        have h := (t.projection_structuralMap i).trans (F.structuralMap_eq i)
        exact congrArg (fun f : BoundedAlgHom K R (F.algebra i) => f (a k) * b i k) h
      _ = (F.map i).coefficientMap (b i) (v i) := t.coefficient_eq_of_residue s i x (v i) (hx i)
      _ = _ := hv i
  · have hzn : ‖z‖ ≤ M * ‖m‖ := by
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM.le (norm_nonneg m))).2
      intro i
      change Fin c.size at i
      have hbound : ‖z i‖ ≤ D i * ‖v i‖ := by
        have h := hnorm i (inr (v i))
        change ‖z i‖ ≤ D i * ‖(inr (v i) : FreeSquareZero.Coordinates (c.obj i).algebra n)‖ at h
        rw [FreeSquareZero.norm_inr] at h
        exact h
      calc
        ‖z i‖ ≤ D i * ‖v i‖ := hbound
        _ ≤ D i * (L i * ‖t.projection i m‖) := mul_le_mul_of_nonneg_left (hvn i) (hD i).le
        _ = (D i * L i) * ‖t.projection i m‖ := (mul_assoc _ _ _).symm
        _ ≤ M * ‖m‖ := mul_le_mul (hMi i) (norm_le_pi_norm m.val i) (norm_nonneg _) hM.le
    calc
      ‖a‖ ≤ ‖e x‖ := FreeSquareZero.norm_snd_le _
      _ ≤ E * ‖x‖ := hnormE x
      _ ≤ E * (B * ‖z‖) := mul_le_mul_of_nonneg_left hxn hE.le
      _ = (E * B) * ‖z‖ := (mul_assoc _ _ _).symm
      _ ≤ (E * B) * (M * ‖m‖) := mul_le_mul_of_nonneg_left hzn (mul_pos hE hB).le
      _ = (E * B * M) * ‖m‖ := (mul_assoc _ _ _).symm

/-- The original structural map to the matching algebra is finite Banach. -/
theorem structuralMap_isFiniteBanach_of_generators
    (hs : ∀ i : Fin c.size, Function.Surjective
      ((F.map i).coefficientMap (fun k => t.projection i (s k)))) :
    t.structuralMap.IsFiniteBanach := by
  obtain ⟨M, hM, hlift⟩ := t.exists_matching_coefficient_lifts s hs
  exact ⟨n, s, M, hM, hlift⟩

end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.PairTransitions
