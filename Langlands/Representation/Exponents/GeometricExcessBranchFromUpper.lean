import Langlands.Representation.Exponents.WeylBranchMultiplicityExtraction
import Langlands.Representation.Exponents.WeylBranchPieceLiftingFromUpper
import Langlands.Representation.CuspidalSupport.ProperInductionProof
import Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
import Langlands.Representation.Parabolic.FlattenedOppositeJacquetComparisonProof
import Langlands.Representation.Filtration.MultiplicityTransportProof

/-!
# Strict multiplicity excess selects a noncoarse whole opposite piece

From the upper geometric lemma at the reversed fine target, the opposite
Jacquet module of a normalized induction is glued from actual geometric
pieces. The identity piece is the inner opposite Jacquet module; strict
excess of the ambient over the inner composition-series multiplicity puts the
cuspidal constituent in a different piece; BZ77 2.4(d) forces that piece to be
whole-target; the whole-target piece is a transported inner opposite Jacquet
module along a noncoarse minimal representative.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric CuspidalSupport CategoryTheory
open RelativeJacquetMultiplicity WeylBranchPieces ProductLeviDualOpposite
open OppositeCuspidalJacquetFiltration Geometric.RefinedOppositePieceTransport

universe uF uV uW

namespace GeometricExcessBranch

section Combinatorics

variable {n : ℕ}

/-- The value of a standard coordinate, computed along an equal block label. -/
theorem index_val_of_eq (B : BlockShape n) {i j : Fin B.length} (h : j = i)
    (a : Fin (B.size j)) :
    ((B.index j a : Fin n) : ℕ) =
      (∑ k : Fin i, B.size (Fin.castLE i.2.le k)) + a := by
  subst h
  exact LeviAdmissibility.index_val B j a

/-- Reversing the block order twice recovers the original shape. -/
theorem reverse_reverse (B : BlockShape n) : B.reverse.reverse = B := by
  obtain ⟨l, s, hp, hs⟩ := B
  have hsize : (fun i : Fin l => s i.rev.rev) = s := funext fun i => by rw [Fin.rev_rev]
  simp only [BlockShape.reverse, BlockShape.mk.injEq, heq_eq_eq, true_and]
  exact hsize

/-- A doubly reversed block label gives the same standard coordinate. -/
theorem index_rev_rev (B : BlockShape n) (i : Fin B.length) (a : Fin (B.size i.rev.rev)) :
    B.index i.rev.rev a = B.reverse.reverse.index i a := by
  apply Fin.ext
  rw [index_val_of_eq B (Fin.rev_rev i) a, index_val_of_eq B.reverse.reverse rfl a]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (congrArg B.size (Fin.rev_rev _)).symm

/-- The reversal permutation of the reversed shape is the inverse reversal. -/
theorem reverse_reversePermutation (B : BlockShape n) :
    B.reverse.reversePermutation = B.reversePermutation⁻¹ := by
  apply Equiv.ext
  intro y
  rw [Equiv.Perm.inv_def]
  apply B.reversePermutation.injective
  rw [Equiv.apply_symm_apply]
  obtain ⟨⟨i, a⟩, rfl⟩ := B.reverse.reverse.indexEquiv.surjective y
  change B.reversePermutation (B.reverse.reversePermutation (B.reverse.reverse.index i a)) =
    B.reverse.reverse.index i a
  erw [B.reverse.reversePermutation_index i a, B.reversePermutation_index i.rev a]
  exact index_rev_rev B i a

/-- Blockwise permutations multiply blockwise. -/
theorem blockPermOf_mul (B : BlockShape n) (σ τ : ∀ i, Equiv.Perm (Fin (B.size i))) :
    blockPermOf B σ * blockPermOf B τ = blockPermOf B (fun i => σ i * τ i) := by
  apply Equiv.ext
  intro y
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective y
  change blockPermOf B σ (blockPermOf B τ (B.index i a)) =
    blockPermOf B (fun i => σ i * τ i) (B.index i a)
  simp only [blockPermOf_index, Equiv.Perm.mul_apply]

/-- The blockwise identity is the identity. -/
theorem blockPermOf_one (B : BlockShape n) : blockPermOf B (fun _ => 1) = 1 := by
  apply Equiv.ext
  intro y
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective y
  change blockPermOf B (fun _ => 1) (B.index i a) = B.index i a
  simp only [blockPermOf_index, Equiv.Perm.one_apply]

/-- Inner reversal followed by inner reversal of the reversed refinement is
the identity. -/
theorem innerReverse_mul_innerReverse_reverse (B : BlockShape n)
    (P : BlockRefinement B) :
    innerReversePermutation B P * innerReversePermutation B (reverseRefinement B P) = 1 := by
  unfold innerReversePermutation
  rw [blockPermOf_mul]
  have h : ∀ i, (P i).reversePermutation * (reverseRefinement B P i).reversePermutation = 1 := by
    intro i
    change (P i).reversePermutation * (P i).reverse.reversePermutation = 1
    rw [reverse_reversePermutation, mul_inv_cancel]
  simp only [h]
  exact blockPermOf_one B

/-- A minimal representative lying in the source block Weyl group is the
identity. -/
theorem eq_one_of_minimal_mem_blockWeyl {B C : BlockShape n} {x : Equiv.Perm (Fin n)}
    (hx : IsMinimalRepresentative B C x) (hW : x ∈ blockWeyl B)
    (h1 : IsMinimalRepresentative B C 1) : x = 1 := by
  have h := weylDoubleCoset_injective B C (a₁ := ⟨x, hx⟩) (a₂ := ⟨1, h1⟩)
    (DoubleCoset.eq.mpr ⟨1, Subgroup.one_mem _, x⁻¹, Subgroup.inv_mem _ hW, by group⟩)
  exact congrArg Subtype.val h

/-- The identity is a minimal representative from a coarse shape to any of
its flattened refinements. -/
theorem isMinimalRepresentative_one_flatten (B : BlockShape n) (S : BlockRefinement B) :
    IsMinimalRepresentative B (B.flatten S) 1 :=
  ⟨fun i => index_strictMono B i, fun j => index_strictMono (B.flatten S) j⟩

variable {F : Type uF} [Field F]

/-- The embedded refined Levi is the flattened standard Levi. -/
theorem map_leviEmbedding_refinedLevi (B : BlockShape n) (S : BlockRefinement B) :
    (refinedLevi F B S).map (B.leviEmbedding F) = (B.flatten S).leviSubgroup F := by
  ext g
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact (leviEmbedding_mem_flattenedLevi_iff B S m).mpr hm
  · intro hg
    obtain ⟨m, rfl⟩ := flattenedLeviSubgroup_le B S hg
    exact ⟨m, (leviEmbedding_mem_flattenedLevi_iff B S m).mp hg, rfl⟩

/-- If the target refinement of a geometric-lemma piece is whole, the source
refinement's flattened Levi is conjugated onto the whole target. -/
theorem conjugatesLevi_of_target_full {B C : BlockShape n} (w : Equiv.Perm (Fin n))
    (P : BlockRefinement B) (Q : BlockRefinement C)
    (hP : IsIntersectionRefinement (F := F) B C w P)
    (hQ : IsIntersectionRefinement (F := F) C B w⁻¹ Q)
    (hfull : refinedParabolic F C Q = ⊤) :
    ConjugatesLevi (F := F) (B.flatten P) C w := by
  have hP' : IsIntersectionRefinement (F := F) B C w⁻¹⁻¹ P := by
    rwa [inv_inv]
  have h := conjugatedLevi_eq_refinement_of_source_full C B w⁻¹ Q P hQ hP' hfull
  have hc : ConjugatesLevi (F := F) C (B.flatten P) w⁻¹ :=
    h.trans (map_leviEmbedding_refinedLevi B P)
  simpa only [inv_inv] using conjugatesLevi_inv hc

/-- Conjugation by the reversal permutation is inverse block relabelling. -/
theorem leviConjugation_reverse (C : BlockShape n) :
    leviConjugation C.reverse C C.reversePermutation (conjugatesLevi_reverse (F := F) C) =
      (leviReverseEquiv (R := F) C).symm := by
  apply MulEquiv.ext
  intro m
  apply C.leviEmbedding_injective F
  rw [leviConjugation_embedding, ← reverseMatrix_mul_leviEmbedding C
    ((leviReverseEquiv (R := F) C).symm m), MulEquiv.apply_symm_apply]
  rfl

/-- A representation of a standard Levi, restricted to the Levi of the
reversed shape along inverse block relabelling. -/
def reversedLeviRepresentation (C : BlockShape n) {V : Type uV}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (C.Levi F) V) :
    Representation ℂ (C.reverse.Levi F) V :=
  ρ.comp (leviReverseEquiv (R := F) C).symm.toMonoidHom

/-- Quasicuspidality passes to the reversed block labels. -/
theorem isLeviQuasicuspidal_reverse (C : BlockShape n) {V : Type uV}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (C.Levi F) V)
    (h : IsLeviQuasicuspidal C ρ) :
    IsLeviQuasicuspidal C.reverse (reversedLeviRepresentation C ρ) := by
  have hmin1 : IsMinimalRepresentative C C 1 :=
    ⟨fun i => index_strictMono C i, fun j => index_strictMono C j⟩
  have hmin : IsMinimalRepresentative C C.reverse C.reversePermutation⁻¹ := by
    simpa only [mul_one] using
      isMinimalRepresentative_reverse_inv_mul hmin1 (conjugatesLevi_one (F := F) C)
  have ht := isLeviQuasicuspidal_transport C C.reverse _ hmin
    (conjugatesLevi_inv (conjugatesLevi_reverse (F := F) C)) ρ h
  rw [transport_inv (conjugatesLevi_reverse C), leviConjugation_reverse] at ht
  exact ht

end Combinatorics

section Exclusion

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}

/-- BZ77 2.4(d) in subquotient form: an irreducible quasicuspidal
representation is not a subquotient of a proper normalized refined induction. -/
theorem not_isSubquotient_properInduced (hn : 0 < n) (C : BlockShape n)
    (R : BlockRefinement C) (hR : refinedParabolic F.Carrier C R ≠ ⊤) :
    letI := T.topology
    ∀ (X : SmoothRep.{0, uF, uW} ℂ (refinedLevi F.Carrier C R))
      {W : Type uV} [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ (C.Levi F.Carrier) W), σ.IsIrreducible →
      IsLeviQuasicuspidal C σ →
      ¬ IsSubquotient ((T.normalizedRefinedInductionFunctor C R).obj X).representation σ := by
  let := T.topology
  intro X W _ _ σ hσ hσq hsub
  obtain ⟨U, q, hq⟩ := hsub
  let Y := (T.normalizedRefinedInductionFunctor C R).obj X
  let Us := SmoothRep.subrepresentation Y U
  let K : Subrepresentation Us.representation :=
    { toSubmodule := LinearMap.ker q.toLinearMap
      apply_mem_toSubmodule := fun g v hv => by
        change q (U.toRepresentation g v) = 0
        rw [Representation.IntertwiningMap.isIntertwining U.toRepresentation σ q g v]
        change σ g (q v) = 0
        rw [show q v = 0 from hv, map_zero] }
  let D := SmoothRep.quotient Us K
  have hD : SmoothRep.IsSubquotient D Y := ⟨U, K, ⟨Iso.refl _⟩⟩
  let e : D.representation.Equiv σ :=
    Representation.Equiv.mk (q.toLinearMap.quotKerEquivOfSurjective hq) (fun g => by
      apply Submodule.linearMap_qext
      ext v
      exact Representation.IntertwiningMap.isIntertwining U.toRepresentation σ q g v)
  have hDq : IsLeviQuasicuspidal C D.representation :=
    (isLeviQuasicuspidal_iff_of_equiv C e).mpr hσq
  have hzero : Subsingleton D :=
    padicProperRefinedInduction.{uF, uW} p F T n hn C R hR X D hD hDq
  obtain ⟨a, b, hab⟩ := QuasicuspidalEmbedding.nontrivial_of_isIrreducible σ hσ
  apply hab
  rw [← e.apply_symm_apply a, ← e.apply_symm_apply b]
  congr 1
  exact Subsingleton.elim _ _

end Exclusion

/-- Equal permutation coordinates give the same actual geometric piece. -/
theorem geometricPieceFunctor_congr {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n) {y w : Equiv.Perm (Fin n)}
    (h : y = w) (S : BlockRefinement B) (R : BlockRefinement C)
    (hSy : sourceLevi F.Carrier B C y = refinedLevi F.Carrier B S)
    (hRy : sourceLevi F.Carrier C B y⁻¹ = refinedLevi F.Carrier C R)
    (hSw : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
    (hRw : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R) :
    geometricPieceFunctor.{uF, uW} T B C y S R hSy hRy =
      geometricPieceFunctor.{uF, uW} T B C w S R hSw hRw := by
  subst h
  rfl

end GeometricExcessBranch

open GeometricExcessBranch

set_option maxHeartbeats 1600000 in
/-- Strict Jordan–Hölder excess selects a noncoarse whole opposite piece,
once the upper geometric lemma has been proved. -/
theorem glGeometricExcessBranch_of_upper
    (hupper : PadicGeometricLemmaTheorem.{uF, uW}) :
    GLGeometricExcessBranchStatement.{uF, uV, uW} := by
  intro p _ F T
  let := T.topology
  intro n hn B S V hV ρ hρi hρc τ m_in m_amb hin hamb hlt
  let A : SmoothRep.{0, uF, uW} ℂ (B.Levi F.Carrier) := SmoothRep.of V.ρ hV
  obtain ⟨P, Q, hP, hQ, m, e, hglued⟩ := hupper p F T n hn B (B.flatten S).reverse
  let piece (w : MinimalRepresentatives B (B.flatten S).reverse) :=
    geometricPieceFunctor.{uF, uW} T B (B.flatten S).reverse w.val (P w) (Q w)
      (hP w).2.1 (hQ w).2.1
  have hglued' : IsGluedFrom (jacquetInductionFunctor T B (B.flatten S).reverse)
      (fun i => piece (e i)) := hglued
  let L := leviReverseEquiv (R := F.Carrier) (B.flatten S)
  let E := flattenedLeviEquiv F.Carrier B S
  let τ' : Rep.{uV} ℂ ((B.flatten S).reverse.Levi F.Carrier) :=
    Rep.of (reversedLeviRepresentation (B.flatten S) ρ.ρ)
  let eτ' : Representation.Equiv (τ'.ρ.comp L.toMonoidHom) ρ.ρ :=
    FiniteTensorFiltration.compSymmComp ρ.ρ L.symm
  let eτ : Representation.Equiv (τ.ρ.comp E.toMonoidHom) ρ.ρ :=
    FiniteTensorFiltration.compSymmComp ρ.ρ E.symm
  -- The identity piece.
  have h1 : ConjugatesLevi (F := F.Carrier) (B.flatten S) (B.flatten S) 1 :=
    conjugatesLevi_one _
  have hmin1 := isMinimalRepresentative_one_flatten B S
  let w0 := reversedPieceMinimalRepresentative B S hmin1 h1
  have hb : HasJordanHolderMultiplicity ((piece w0).obj A) τ' m_in := by
    rw [groupEquivJordanHolderMultiplicityTransport ℂ _ _ L]
    have E0 := chosenRefinementReversedWholeLeviGeometricPieceEquiv T B S (B.flatten S) 1 h1
      (P w0) (Q w0) (hP w0).2.1 (hQ w0).2.1 A
    rw [transport_one] at E0
    have hin' := (groupEquivJordanHolderMultiplicityTransport ℂ _ _ E _ _ m_in).mp hin
    exact (equivJordanHolderMultiplicityTransport ℂ _ _ _ _ _ E0.symm
      (eτ.trans eτ'.symm) m_in).mp hin'
  -- The ambient multiplicity.
  have hM : HasJordanHolderMultiplicity
      ((jacquetInductionFunctor T B (B.flatten S).reverse).obj A) τ' m_amb := by
    rw [groupEquivJordanHolderMultiplicityTransport ℂ _ _ L]
    obtain ⟨Ef, -⟩ := Parabolic.flattenedOppositeJacquetComparison.{uF, uF, max uF uW}.2
      p F T n B S (CuspidalJacquetMultiplicity.induced T B V)
    let eAmb := oppositeJacquetReverseEquiv T (B.flatten S)
      (CuspidalJacquetMultiplicity.induced T B V)
    have hamb' := (groupEquivJordanHolderMultiplicityTransport ℂ _ _ E _ _ m_amb).mp hamb
    exact (equivJordanHolderMultiplicityTransport ℂ _ _ _ _ _ (Ef.trans eAmb.symm)
      (eτ.trans eτ'.symm) m_amb).mp hamb'
  -- Strict excess selects a different piece.
  obtain ⟨i, hi, hsub⟩ := IsGluedFrom.exists_isSubquotient_piece_of_multiplicity_excess
    hglued' A (e.symm w0) (by rw [Equiv.apply_symm_apply]; exact hb) hM hlt
  let w := e i
  have hw0 : w ≠ w0 := by
    intro h
    apply hi
    rw [← h, Equiv.symm_apply_apply]
  change IsSubquotient ((piece w).obj A).ρ τ'.ρ at hsub
  -- Cuspidal exclusion forces a whole target.
  have hτ'irr : τ'.ρ.IsIrreducible :=
    (isIrreducible_comp_mulEquiv_iff ρ.ρ L.symm).mpr hρi
  have hτ'q : IsLeviQuasicuspidal (B.flatten S).reverse τ'.ρ :=
    isLeviQuasicuspidal_reverse (B.flatten S) ρ.ρ hρc.2
  have hfull : refinedParabolic F.Carrier (B.flatten S).reverse (Q w) = ⊤ := by
    by_contra hne
    exact not_isSubquotient_properInduced T hn _ (Q w) hne _ τ'.ρ hτ'irr hτ'q hsub
  have hwc : ConjugatesLevi (F := F.Carrier) (B.flatten (P w)) (B.flatten S).reverse w.val :=
    conjugatesLevi_of_target_full w.val (P w) (Q w) (hP w) (hQ w) hfull
  -- The noncoarse representative and refinement.
  let S' := reverseRefinement B (P w)
  let x := reversedPiecePermutation B (P w) (B.flatten S).reverse w.val
  have hxmin : IsMinimalRepresentative B (B.flatten S) x := by
    have h := isMinimalRepresentative_reversedPiece B (P w) w.property hwc
    rwa [reverse_reverse] at h
  have hxc : ConjugatesLevi (F := F.Carrier) (B.flatten S') (B.flatten S) x := by
    have h := conjugatesLevi_reversedPiece B (P w) F.Carrier (B.flatten S).reverse w.val hwc
    rwa [reverse_reverse] at h
  have hxw : reversedPiecePermutation B S' (B.flatten S) x = w.val := by
    simp only [reversedPiecePermutation, x, S']
    rw [reverse_reversePermutation, inv_inv, mul_assoc, inv_mul_cancel_left, mul_assoc,
      innerReverse_mul_innerReverse_reverse, mul_one]
  have hS' : sourceLevi F.Carrier B (B.flatten S).reverse
      (reversedPiecePermutation B S' (B.flatten S) x) = refinedLevi F.Carrier B (P w) := by
    rw [hxw]
    exact (hP w).2.1
  have hR' : sourceLevi F.Carrier (B.flatten S).reverse B
      (reversedPiecePermutation B S' (B.flatten S) x)⁻¹ =
        refinedLevi F.Carrier (B.flatten S).reverse (Q w) := by
    rw [hxw]
    exact (hQ w).2.1
  have hpiece := geometricPieceFunctor_congr T B (B.flatten S).reverse hxw (P w) (Q w)
    hS' hR' (hP w).2.1 (hQ w).2.1
  have hsub' : IsSubquotient
      (((geometricPieceFunctor.{uF, uW} T B (B.flatten S).reverse
        (reversedPiecePermutation B S' (B.flatten S) x) (P w) (Q w) hS' hR').obj A).ρ)
      τ'.ρ := by
    rw [hpiece]
    exact hsub
  let Ew := chosenRefinementReversedWholeLeviGeometricPieceEquiv T B S' (B.flatten S) x hxc
    (P w) (Q w) hS' hR' A
  have hfinal := IsSubquotient.of_equiv_left Ew.symm
    ((hsub'.comp L.toMonoidHom).of_equiv_right eτ')
  refine ⟨x, S', hxc, hxmin, ?_, hfinal⟩
  -- The representative is not coarse.
  intro hxW
  have hx1 : x = 1 := eq_one_of_minimal_mem_blockWeyl hxmin hxW hmin1
  have hS'S : S' = S := by
    have h1' := sourceLevi_eq_refined_of_flattened_conjugates B (B.flatten S) S' x hxc
    have h2' := sourceLevi_eq_refined_of_flattened_conjugates B (B.flatten S) S 1 h1
    rw [hx1] at h1'
    exact blockRefinement_eq_of_refinedLevi_eq B (h1'.symm.trans h2')
  apply hw0
  apply Subtype.ext
  rw [← hxw]
  change reversedPiecePermutation B S' (B.flatten S) x =
    reversedPiecePermutation B S (B.flatten S) 1
  rw [hx1, hS'S]

end Langlands
