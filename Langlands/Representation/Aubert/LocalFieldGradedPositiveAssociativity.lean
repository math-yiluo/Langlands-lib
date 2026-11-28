import Langlands.Representation.Aubert.LocalFieldGradedGrothendieck
import Langlands.AllFieldBZ.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.AllFieldBZ.Representation.Parabolic.ThreeBlockRegroupingAssembly
import Langlands.Representation.Classification.TwoSupercuspidalBinaryProductBridge

/-! Actual three-factor associativity of normalized GL products in positive ranks. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

open CategoryTheory

namespace Langlands.Aubert.LocalFieldGraded

open AllFieldBZ.LocalFieldPackage.TopologicalData
open Classification (twoBlockFactors)
open GeneralLinear Parabolic Shahidi

universe uF uV

variable {K : AllFieldBZ.LocalFieldPackage.{uF}} (T : K.TopologicalData)

private def productFamilyEquiv {n : ℕ} (D : BlockShape n)
    {σ τ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (D.size i) K.Carrier)}
    (h : σ = τ) :
    letI := T.topology
    ((normalizedProductInductionFunctor T D).obj σ).representation.Equiv
      ((normalizedProductInductionFunctor T D).obj τ).representation :=
  letI := T.topology
  SmoothRep.equivOfIso
    (eqToIso (congrArg (normalizedProductInductionFunctor T D).obj h))

/-- Equal upper-block shapes and transported factor families give equal
normalized product objects. -/
theorem productShape_eq {n : ℕ} {D E : BlockShape n} (h : D = E)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (D.size i) K.Carrier))
    (τ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (E.size i) K.Carrier))
    (hστ : HEq σ τ) :
    letI := T.topology
    (normalizedProductInductionFunctor T D).obj σ =
      (normalizedProductInductionFunctor T E).obj τ := by
  subst E
  cases hστ
  rfl

private def pairProductEquiv {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a K.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b K.Carrier)) :
    letI := T.topology
    ((binaryNormalizedProductFunctor T a b).obj (A, B)).representation.Equiv
      (normalizedProductInduced T (twoBlocks a b ha hb)
        (pairFamily A.representation B.representation)) := by
  let := T.topology
  have hD := Classification.BinaryProductBridge.binary_eq_twoBlocks ha hb
  let σ := (binaryPairFamilyFunctor T ha hb).obj (A, B)
  let τ := twoBlockFactors ha hb A B
  have hστ : HEq σ τ := by
    apply Function.hfunext rfl
    intro i j hij
    cases hij
    fin_cases i <;> rfl
  have hobj := productShape_eq T hD σ τ hστ
  exact ((SmoothRep.equivOfIso ((binaryNormalizedProductPositiveIso T ha hb).app (A, B))).trans
    (SmoothRep.equivOfIso (eqToIso hobj))).trans
    ((normalizedProductInductionObjEquiv T _ τ).trans
      (normalizedProductInducedEquiv T (twoBlocks a b ha hb) fun i =>
        match i with
        | 0 => Representation.Equiv.refl _
        | 1 => Representation.Equiv.refl _))

private def regroupingEquiv {n : ℕ} (B D : BlockShape n)
    (S : Geometric.BlockRefinement D)
    (e : ((j : Fin D.length) × Fin (S j).length) ≃ Fin B.length)
    (hs : ∀ a, (S a.1).size a.2 = B.size (e a))
    (hc : ∀ j k (x : Fin ((S j).size k)),
      D.index j ((S j).index k x) = B.index (e ⟨j,k⟩) (Fin.cast (hs ⟨j,k⟩) x))
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) K.Carrier))
    {W : Fin D.length → Type uV} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (τ : ∀ j, Representation ℂ (GeneralLinear (D.size j) K.Carrier) (W j))
    (δ : letI := T.topology
      ∀ j, Representation.Equiv
        (((normalizedProductInductionFunctor T (S j)).obj
          (fun k => (hs ⟨j,k⟩).symm ▸ σ (e ⟨j,k⟩))).representation) (τ j)) :
    letI := T.topology
    ((normalizedProductInductionFunctor T B).obj σ).representation.Equiv
      (normalizedProductInduced T D τ) :=
  letI := T.topology
  (SmoothRep.equivOfIso (Classical.choice
    (AllFieldBZ.Parabolic.orderedProductRegrouping.{uF, uV} K T n B D S e hs hc σ))).trans
      (normalizedProductInducedEquiv T D δ)

private def pairFamilyEquiv {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a K.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear b K.Carrier)) :
    letI := T.topology
    ((normalizedProductInductionFunctor T (twoBlocks a b ha hb)).obj
      (twoBlockFactors ha hb A B)).representation.Equiv
        (normalizedProductInduced T (twoBlocks a b ha hb)
          (pairFamily A.representation B.representation)) :=
  letI := T.topology
  (normalizedProductInductionObjEquiv T _ _).trans
    (normalizedProductInducedEquiv T (twoBlocks a b ha hb) fun i =>
      match i with
      | 0 => Representation.Equiv.refl _
      | 1 => Representation.Equiv.refl _)

section ThreeFactors

variable {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
variable (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a K.Carrier))
variable (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b K.Carrier))
variable (C : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear c K.Carrier))

private def regroupRightPair :
    letI := T.topology
    ((normalizedProductInductionFunctor T (threeBlocks a b c ha hb hc)).obj
      (threeBlockSmoothFamily A B C)).representation.Equiv
      (normalizedProductInduced T (twoBlocks a (b + c) ha (Nat.add_pos_left hb c))
        (pairFamily A.representation
          (normalizedProductInduced T (twoBlocks b c hb hc)
            (pairFamily B.representation C.representation)))) :=
  letI := T.topology
  regroupingEquiv T (threeBlocks a b c ha hb hc)
    (twoBlocks a (b + c) ha (Nat.add_pos_left hb c))
    (leftRefinement a b c ha hb hc) (leftLabelEquiv a b c ha hb hc)
    (leftLabelEquiv_size a b c ha hb hc) (leftLabelEquiv_index a b c ha hb hc)
    (threeBlockSmoothFamily A B C) _ (fun j =>
      match j with
      | 0 => (productFamilyEquiv T _ (by rfl)).trans
          ((normalizedProductInductionObjEquiv T _ _).trans
            (singleBlockTransportedProductEquiv T (leftRefinement a b c ha hb hc 0) rfl A))
      | 1 => (productFamilyEquiv T _
            (by funext k; fin_cases k <;> rfl)).trans (pairFamilyEquiv T hb hc B C))

private def regroupLeftPair :
    letI := T.topology
    ((normalizedProductInductionFunctor T (threeBlocksRight a b c ha hb hc)).obj
      (threeBlockSmoothFamily A B C)).representation.Equiv
      (normalizedProductInduced T (twoBlocks (a + b) c (Nat.add_pos_left ha b) hc)
        (pairFamily
          (normalizedProductInduced T (twoBlocks a b ha hb)
            (pairFamily A.representation B.representation))
          C.representation)) :=
  letI := T.topology
  regroupingEquiv T (threeBlocksRight a b c ha hb hc)
    (twoBlocks (a + b) c (Nat.add_pos_left ha b) hc)
    (rightRefinement a b c ha hb hc) (rightLabelEquiv a b c ha hb hc)
    (rightLabelEquiv_size a b c ha hb hc) (rightLabelEquiv_index a b c ha hb hc)
    (threeBlockSmoothFamily A B C) _ (fun j =>
      match j with
      | 0 => (productFamilyEquiv T _
            (by funext k; fin_cases k <;> rfl)).trans (pairFamilyEquiv T ha hb A B)
      | 1 => (productFamilyEquiv T _ (by rfl)).trans
          ((normalizedProductInductionObjEquiv T _ _).trans
            (singleBlockTransportedProductEquiv T (rightRefinement a b c ha hb hc 1) rfl C)))

/-- Transporting the total rank commutes with actual normalized product induction. -/
def inducedRankCast {m n : ℕ} (e : m = n) (D : BlockShape n)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (D.size i) K.Carrier)) :
    letI := T.topology
    Representation.Equiv
      (((normalizedProductInductionFunctor T D).obj σ).representation.comp
        (reindex (R := K.Carrier) (finCongr e)).toMonoidHom)
      ((normalizedProductInductionFunctor T (D.rankCast e.symm)).obj σ).representation := by
  let := T.topology
  subst n
  exact Representation.Equiv.refl _

/-- The two bracketings of three positive-rank actual binary products are
equivalent after the entry-preserving rank cast. -/
def positiveAssociativityEquiv :
    letI := T.topology
    ((binaryNormalizedProductFunctor T (a + b) c).obj
        ((binaryNormalizedProductFunctor T a b).obj (A, B), C)).representation.Equiv
      (((binaryNormalizedProductFunctor T a (b + c)).obj
        (A, (binaryNormalizedProductFunctor T b c).obj (B, C))).representation.comp
        (reindex (R := K.Carrier) (finCongr (Nat.add_assoc a b c))).toMonoidHom) :=
  letI := T.topology
  let R := reindex (R := K.Carrier) (finCongr (Nat.add_assoc a b c))
  let AB := (binaryNormalizedProductFunctor T a b).obj (A, B)
  let BC := (binaryNormalizedProductFunctor T b c).obj (B, C)
  let eL : ((binaryNormalizedProductFunctor T (a + b) c).obj (AB, C)).representation.Equiv
      (normalizedProductInduced T (twoBlocks (a + b) c (Nat.add_pos_left ha b) hc)
        (pairFamily
          (normalizedProductInduced T (twoBlocks a b ha hb)
            (pairFamily A.representation B.representation)) C.representation)) :=
    (pairProductEquiv T (Nat.add_pos_left ha b) hc AB C).trans
    (normalizedProductInducedEquiv T (twoBlocks (a + b) c (Nat.add_pos_left ha b) hc)
      fun i => match i with
      | 0 => pairProductEquiv T ha hb A B
      | 1 => Representation.Equiv.refl _)
  let eR : ((binaryNormalizedProductFunctor T a (b + c)).obj (A, BC)).representation.Equiv
      (normalizedProductInduced T (twoBlocks a (b + c) ha (Nat.add_pos_left hb c))
        (pairFamily A.representation
          (normalizedProductInduced T (twoBlocks b c hb hc)
            (pairFamily B.representation C.representation)))) :=
    (pairProductEquiv T ha (Nat.add_pos_left hb c) A BC).trans
    (normalizedProductInducedEquiv T (twoBlocks a (b + c) ha (Nat.add_pos_left hb c))
      fun i => match i with
      | 0 => Representation.Equiv.refl _
      | 1 => pairProductEquiv T hb hc B C)
  let E := inducedRankCast.{uF, max uF uV} T (Nat.add_assoc a b c) (threeBlocks a b c ha hb hc)
    (threeBlockSmoothFamily A B C)
  let left := regroupLeftPair.{uF, uV} T ha hb hc A B C
  let right := regroupRightPair.{uF, uV} T ha hb hc A B C
  let L := equivTrans eL (equivSymm left)
  let Q := equivPrecomp (equivTrans right (equivSymm eR)) R.toMonoidHom
  equivTrans L (equivTrans (equivSymm E) Q)

end ThreeFactors

end Langlands.Aubert.LocalFieldGraded
