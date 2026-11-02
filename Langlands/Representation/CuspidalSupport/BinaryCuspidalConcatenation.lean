import Langlands.Algebra.MultisetOfFn
import Langlands.Representation.Parabolic.FlattenedProductInduction
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Classification.SupercuspidalSupport

/-! Consecutive concatenation of two actual cuspidal families of positive
total ranks, with their supplied representatives and multiset multiplicities. -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.PadicField.TopologicalData.BinaryCuspidalConcatenation

open GeneralLinear Geometric CategoryTheory

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {T : F.TopologicalData} {k l a b : ℕ}

def length (k l : ℕ) : Fin 2 → ℕ :=
  Fin.cases k (fun _ => l)

def family (ρ : Fin k → CuspidalDatum.{uV, uF} T)
    (τ : Fin l → CuspidalDatum.{uV, uF} T) :
    ∀ i : Fin 2, Fin (length k l i) → CuspidalDatum.{uV, uF} T :=
  Fin.cases ρ (fun _ => τ)

variable (ρ : Fin k → CuspidalDatum.{uV, uF} T)
variable (τ : Fin l → CuspidalDatum.{uV, uF} T)
variable (ha : 0 < a) (hb : 0 < b)
variable (hρ : ∑ j, (ρ j).rank = a) (hτ : ∑ j, (τ j).rank = b)

include hρ hτ in
theorem family_rank_sum (i : Fin 2) :
    ∑ j, (family ρ τ i j).rank = (BlockShape.binary a b ha hb).size i := by
  fin_cases i
  · exact hρ
  · exact hτ

def refinement : BlockRefinement (BlockShape.binary a b ha hb) :=
  fun i => T.cuspidalShape (family ρ τ i) (family_rank_sum ρ τ ha hb hρ hτ i)

theorem flattened_length :
    ((BlockShape.binary a b ha hb).flatten (refinement ρ τ ha hb hρ hτ)).length = k + l := by
  change (∑ i : Fin 2, length k l i) = k + l
  rw [Fin.sum_univ_two]
  rfl

def flattenedFamily :
    Fin ((BlockShape.binary a b ha hb).flatten (refinement ρ τ ha hb hρ hτ)).length →
      CuspidalDatum.{uV, uF} T :=
  fun q => family ρ τ
    (((BlockShape.binary a b ha hb).flattenBlockEquiv
      (refinement ρ τ ha hb hρ hτ)).symm q).1
    (((BlockShape.binary a b ha hb).flattenBlockEquiv
      (refinement ρ τ ha hb hρ hτ)).symm q).2

theorem flattenedFamily_rank_sum :
    ∑ q, (flattenedFamily ρ τ ha hb hρ hτ q).rank = a + b :=
  ((BlockShape.binary a b ha hb).flatten (refinement ρ τ ha hb hρ hτ)).sum_eq

theorem flattenedFamily_shape :
    T.cuspidalShape (flattenedFamily ρ τ ha hb hρ hτ)
      (flattenedFamily_rank_sum ρ τ ha hb hρ hτ) =
    (BlockShape.binary a b ha hb).flatten (refinement ρ τ ha hb hρ hτ) := rfl

def representatives
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (C : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (τ i).rank)) :
    letI := T.topology
    ∀ i j, SupercuspidalRep.{uF, uV}
      (F := F.Carrier) (n := (family ρ τ i j).rank) :=
  letI := T.topology
  Fin.cases A (fun _ => C)

def flattenedRepresentatives
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (C : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (τ i).rank)) :
    letI := T.topology
    ∀ q, SupercuspidalRep.{uF, uV} (F := F.Carrier)
      (n := (flattenedFamily ρ τ ha hb hρ hτ q).rank) :=
  letI := T.topology
  fun q => representatives ρ τ A C
    (((BlockShape.binary a b ha hb).flattenBlockEquiv
      (refinement ρ τ ha hb hρ hτ)).symm q).1
    (((BlockShape.binary a b ha hb).flattenBlockEquiv
      (refinement ρ τ ha hb hρ hτ)).symm q).2

theorem flattenedRepresentatives_represents
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (C : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (τ i).rank))
    (hA : ∀ i, (ρ i).IsRepresentedBy (A i))
    (hC : ∀ i, (τ i).IsRepresentedBy (C i)) :
    ∀ q, (flattenedFamily ρ τ ha hb hρ hτ q).IsRepresentedBy
      (flattenedRepresentatives ρ τ ha hb hρ hτ A C q) := by
  let := T.topology
  have h : ∀ i j, (family ρ τ i j).IsRepresentedBy (representatives ρ τ A C i j) := by
    intro i
    fin_cases i
    · exact hA
    · exact hC
  exact fun q => h _ _

theorem flattenedFamily_multiset :
    (List.ofFn (flattenedFamily ρ τ ha hb hρ hτ) : Multiset (CuspidalDatum T)) =
      (List.ofFn ρ : Multiset (CuspidalDatum T)) +
        (List.ofFn τ : Multiset (CuspidalDatum T)) := by
  classical
  rw [Classification.SegmentProductCuspidalEmbedding.ofFn_multiset_eq_sum,
    Classification.SegmentProductCuspidalEmbedding.ofFn_multiset_eq_sum,
    Classification.SegmentProductCuspidalEmbedding.ofFn_multiset_eq_sum]
  let B := BlockShape.binary a b ha hb
  let S := refinement ρ τ ha hb hρ hτ
  calc
    ∑ q, ({flattenedFamily ρ τ ha hb hρ hτ q} : Multiset (CuspidalDatum T)) =
        ∑ q : (i : Fin B.length) × Fin (S i).length,
          ({family ρ τ q.1 q.2} : Multiset (CuspidalDatum T)) :=
      Fintype.sum_equiv (B.flattenBlockEquiv S).symm _ _ fun _ => rfl
    _ = ∑ i : Fin B.length, ∑ j : Fin (S i).length,
        ({family ρ τ i j} : Multiset (CuspidalDatum.{uV, uF} T)) :=
      Fintype.sum_sigma' (fun i j =>
        ({family ρ τ i j} : Multiset (CuspidalDatum.{uV, uF} T)))
    _ = _ := by
      change (∑ i : Fin 2, ∑ j : Fin (length k l i),
        ({family ρ τ i j} : Multiset (CuspidalDatum.{uV, uF} T))) = _
      rw [Fin.sum_univ_two]
      rfl

private def mkNormalizedProductIso {n : ℕ} (B : BlockShape n)
    (D : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (Y : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (E : letI := T.topology
      (T.normalizedProductInduced B (fun i => (D i).representation)).Equiv Y.representation) :
    letI := T.topology
    (T.normalizedProductInductionFunctor B).obj D ≅ Y :=
  letI := T.topology
  SmoothRep.mkIso E

private def flattenedIso {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (D : letI := T.topology
      ∀ i j, SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((S i).size j) F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor (B.flatten S)).obj
      (Parabolic.flattenedSmoothFamily F T B S D) ≅
    (T.normalizedProductInductionFunctor B).obj
      (fun i => (T.normalizedProductInductionFunctor (S i)).obj (D i)) :=
  letI := T.topology
  mkNormalizedProductIso (B.flatten S)
    (Parabolic.flattenedSmoothFamily F T B S D) _
    (Parabolic.flattenedProductInducedEquiv F T B S D)

private def inductionIsoOfShapeFamilyEq {n : ℕ} {B C : BlockShape n}
    (D : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (E : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (C.size i) F.Carrier))
    (h : B = C) (hDE : HEq D E) :
    letI := T.topology
    (T.normalizedProductInductionFunctor B).obj D ≅
      (T.normalizedProductInductionFunctor C).obj E := by
  subst C
  cases hDE
  exact Iso.refl _

/-- The induction of the concatenated supplied family is the actual binary
product of the two original cuspidal inductions. -/
def productIso
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (C : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (τ i).rank)) :
    letI := T.topology
    T.cuspidalProductInduced (flattenedFamily ρ τ ha hb hρ hτ)
      (flattenedFamily_rank_sum ρ τ ha hb hρ hτ)
      (flattenedRepresentatives ρ τ ha hb hρ hτ A C) ≅
      (T.binaryNormalizedProductFunctor a b).obj
        (T.cuspidalProductInduced ρ hρ A, T.cuspidalProductInduced τ hτ C) := by
  letI := T.topology
  let B := BlockShape.binary a b ha hb
  let S := refinement ρ τ ha hb hρ hτ
  let D := fun i j => (representatives ρ τ A C i j).obj
  let Z := fun i => (T.normalizedProductInductionFunctor (S i)).obj (D i)
  have hZ : Z = (T.binaryPairFamilyFunctor ha hb).obj
      (T.cuspidalProductInduced ρ hρ A, T.cuspidalProductInduced τ hτ C) := by
    funext i
    fin_cases i <;> rfl
  let eZ : (T.normalizedProductInductionFunctor B).obj Z ≅
      (T.binaryPositiveProductFunctor ha hb).obj
        (T.cuspidalProductInduced ρ hρ A, T.cuspidalProductInduced τ hτ C) :=
    (T.normalizedProductInductionFunctor B).mapIso (eqToIso hZ)
  have hCflat :
      (fun q => (flattenedRepresentatives ρ τ ha hb hρ hτ A C q).obj) =
      Parabolic.flattenedSmoothFamily F T B S D := rfl
  let eX := inductionIsoOfShapeFamilyEq (T := T)
    (B := T.cuspidalShape (flattenedFamily ρ τ ha hb hρ hτ)
      (flattenedFamily_rank_sum ρ τ ha hb hρ hτ))
    (C := B.flatten S)
    (fun q => (flattenedRepresentatives ρ τ ha hb hρ hτ A C q).obj)
    (Parabolic.flattenedSmoothFamily F T B S D)
    (flattenedFamily_shape ρ τ ha hb hρ hτ) (heq_of_eq hCflat)
  exact eX ≪≫ flattenedIso (T := T) B S D ≪≫ eZ ≪≫
    ((T.binaryNormalizedProductPositiveIso ha hb).app
      (T.cuspidalProductInduced ρ hρ A, T.cuspidalProductInduced τ hτ C)).symm

/-- The underlying actual equivariant linear equivalence. -/
def productEquiv
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (C : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (τ i).rank)) :
    letI := T.topology
    (T.cuspidalProductInduced (flattenedFamily ρ τ ha hb hρ hτ)
      (flattenedFamily_rank_sum ρ τ ha hb hρ hτ)
      (flattenedRepresentatives ρ τ ha hb hρ hτ A C)).representation.Equiv
      ((T.binaryNormalizedProductFunctor a b).obj
        (T.cuspidalProductInduced ρ hρ A, T.cuspidalProductInduced τ hτ C)).representation :=
  letI := T.topology
  SmoothRep.equivOfIso (productIso ρ τ ha hb hρ hτ A C)

end Langlands.PadicField.TopologicalData.BinaryCuspidalConcatenation
