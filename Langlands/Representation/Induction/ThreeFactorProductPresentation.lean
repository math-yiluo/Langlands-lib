import Langlands.Representation.Induction.RightProductExactness
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly
import Langlands.Representation.Classification.TwoSupercuspidalBinaryProductBridge

/-! Actual presentations of a right product by a literal three-block product. -/

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Parabolic

open GeneralLinear Classification Shahidi

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual right-product map of any surjection is surjective. -/
theorem rightProductMap_surjective {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ {P Q : SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier)}
      (q : P.representation.IntertwiningMap Q.representation)
      (C : SmoothRep.{0,uF,uV} ℂ (GeneralLinear b F.Carrier)),
      Function.Surjective q → Function.Surjective (rightProductMap F T ha hb q C) := by
  let := T.topology
  intro P Q q C hq
  let i := SmoothRep.hom (SmoothRep.subtype P q.ker)
  have hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap := by
    exact Submodule.range_subtype _
  exact (rightProductMap_shortExact F T ha hb i q C
    (SmoothRep.subtype_injective P q.ker) hq hex).2.2

/-- The actual right-product map of an injection is injective. -/
theorem rightProductMap_injective {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ {P Q : SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier)}
      (i : P.representation.IntertwiningMap Q.representation)
      (C : SmoothRep.{0,uF,uV} ℂ (GeneralLinear b F.Carrier)),
      Function.Injective i → Function.Injective (rightProductMap F T ha hb i C) := by
  let := T.topology
  intro P Q i C hi
  exact T.normalizedParabolicInducedMap_injective _ _
    (rightTensorMap_injective F T ha hb i C hi)

/-- Regroup a literal right-bracketed three-block induction and apply a
supplied map on its first two factors. -/
def threeRightProductEquiv {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear b F.Carrier))
      (C : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear c F.Carrier)),
      ((T.normalizedProductInductionFunctor (threeBlocksRight a b c ha hb hc)).obj
        (threeBlockSmoothFamily A B C)).representation.Equiv
      ((T.normalizedProductInductionFunctor
        (twoBlocks (a+b) c (Nat.add_pos_left ha b) hc)).obj
        (twoBlockFactors (Nat.add_pos_left ha b) hc
          ((T.normalizedProductInductionFunctor (twoBlocks a b ha hb)).obj
            (twoBlockFactors ha hb A B)) C)).representation := by
  let := T.topology
  intro A B C
  let P := (T.normalizedProductInductionFunctor (twoBlocks a b ha hb)).obj
    (twoBlockFactors ha hb A B)
  let eP : P.representation.Equiv
      (T.normalizedProductInduced (twoBlocks a b ha hb)
        (pairFamily A.representation B.representation)) :=
    T.normalizedProductInducedEquiv (twoBlocks a b ha hb)
      (Fin.cases (Representation.Equiv.refl _)
        (Fin.cases (Representation.Equiv.refl _) finZeroElim))
  let eOuter :
      (T.normalizedProductInduced (twoBlocks (a+b) c (Nat.add_pos_left ha b) hc)
        (pairFamily
          (T.normalizedProductInduced (twoBlocks a b ha hb)
            (pairFamily A.representation B.representation)) C.representation)).Equiv
      ((T.normalizedProductInductionFunctor
        (twoBlocks (a+b) c (Nat.add_pos_left ha b) hc)).obj
        (twoBlockFactors (Nat.add_pos_left ha b) hc P C)).representation :=
    T.normalizedProductInducedEquiv (twoBlocks (a+b) c (Nat.add_pos_left ha b) hc)
      (Fin.cases eP.symm (Fin.cases (Representation.Equiv.refl _) finZeroElim))
  exact (rightRegroupingEquiv.{uF,uV} T (orderedProductRegrouping F T)
    a b c ha hb hc A B C).trans eOuter

/-- The binary product of a supplied quotient with the third factor is an
actual quotient of the literal three-block induction at total rank `(a+b)+c`. -/
theorem binaryRightProduct_isQuotient_threeBlocksRight {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear b F.Carrier))
      (C : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear c F.Carrier))
      (Q : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (a+b) F.Carrier)),
      SmoothRep.IsQuotient Q
        ((T.normalizedProductInductionFunctor (twoBlocks a b ha hb)).obj
          (twoBlockFactors ha hb A B)) →
      SmoothRep.IsQuotient ((T.binaryNormalizedProductFunctor (a+b) c).obj (Q,C))
        ((T.normalizedProductInductionFunctor (threeBlocksRight a b c ha hb hc)).obj
          (threeBlockSmoothFamily A B C)) := by
  let := T.topology
  intro A B C Q hQ
  obtain ⟨q, hq⟩ := hQ
  rw [BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks
    F T (Nat.add_pos_left ha b) hc]
  let P := (T.normalizedProductInductionFunctor (twoBlocks a b ha hb)).obj
    (twoBlockFactors ha hb A B)
  let R := (T.normalizedProductInductionFunctor
    (twoBlocks (a+b) c (Nat.add_pos_left ha b) hc)).obj
    (twoBlockFactors (Nat.add_pos_left ha b) hc P C)
  let Y := (T.normalizedProductInductionFunctor
    (twoBlocks (a+b) c (Nat.add_pos_left ha b) hc)).obj
    (twoBlockFactors (Nat.add_pos_left ha b) hc Q C)
  let e := threeRightProductEquiv F T ha hb hc A B C
  let f : R ⟶ Y := SmoothRep.ofHom
    (rightProductMap F T (Nat.add_pos_left ha b) hc (A := P) (A' := Q) (SmoothRep.hom q) C)
  refine ⟨(SmoothRep.mkIso e).hom ≫ f, ?_⟩
  exact (rightProductMap_surjective F T (Nat.add_pos_left ha b) hc
    (P := P) (Q := Q) (SmoothRep.hom q) C hq).comp e.surjective

end Langlands.Parabolic
