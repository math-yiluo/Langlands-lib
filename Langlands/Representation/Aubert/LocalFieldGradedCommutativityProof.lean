import Langlands.Representation.Aubert.LocalFieldGradedCommutativityStatement
import Langlands.Representation.Aubert.LocalFieldReversedProductConstituents
import Langlands.Representation.Aubert.GradedInductionCommutativityProof
import Langlands.Representation.Smooth.FiniteLengthGrothendieckTransport

/-! # Commutativity of the graded normalized GL product over a local field

Interchanging the two factors of an actual binary normalized product does not change its
class in the exact Grothendieck group, after the rank transport along `a + b = b + a`.
At positive ranks the irreducible case follows from the constituent matching
`sameFactors_reverseProduct`; when one rank is zero the two products are compared by the
tensor commutor. Bilinearity and the irreducible basis of the exact Grothendieck groups then
give commutativity on the whole graded direct sum.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Aubert.LocalFieldGraded

open GeneralLinear SmoothRep SmoothRep.FiniteLengthGrothendieckGroup
open AllFieldBZ.LocalFieldPackage.TopologicalData

universe uF uV

variable {K : AllFieldBZ.LocalFieldPackage.{uF}} (T : K.TopologicalData)
variable (h : LocalFieldBinaryProductExactLengthStatement.{uF, uV})

/-! ### Rank transport -/

/-- Two finite-length representations identified after the entry-preserving reindexing
along a rank equality have the same class in the graded sum. -/
private theorem inclusion_eq_of_reindexEquiv {a b : ℕ} (e : a = b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a K.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b K.Carrier))
      (hA : A.HasFiniteLength) (hB : B.HasFiniteLength),
      A.representation.Equiv (B.representation.comp
        (GeneralLinear.reindex (R := K.Carrier) (finCongr e)).toMonoidHom) →
      inclusion T a (ofRepresentation A hA) = inclusion T b (ofRepresentation B hB) := by
  let := T.topology
  subst b
  intro A B hA hB E
  apply congrArg (inclusion T a)
  apply ofRepresentation_eq_of_equiv hA hB
  refine E.trans (Representation.Equiv.mk (LinearEquiv.refl ℂ B) fun g => ?_)
  ext v
  change B.representation (GeneralLinear.reindex (R := K.Carrier) (finCongr rfl) g) v =
    B.representation g v
  rw [GeneralLinear.reindex_finCongr_rfl]
  rfl

private theorem reindex_trans {a b c : ℕ} (e : a = b) (e' : b = c)
    (g : GeneralLinear a K.Carrier) :
    GeneralLinear.reindex (R := K.Carrier) (finCongr e')
        (GeneralLinear.reindex (R := K.Carrier) (finCongr e) g) =
      GeneralLinear.reindex (R := K.Carrier) (finCongr (e.trans e')) g := by
  subst e
  subst e'
  simp only [GeneralLinear.reindex_finCongr_rfl, MulEquiv.refl_apply]

/-! ### A rank-zero factor -/

/-- With a rank-zero first factor, the tensor commutor identifies the binary product with
the binary product in the other order, after rank transport. -/
private def zeroLeftProductEquiv (b : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 K.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b K.Carrier)),
      ((binaryNormalizedProductFunctor T 0 b).obj (A, B)).representation.Equiv
        (((binaryNormalizedProductFunctor T b 0).obj (B, A)).representation.comp
          (GeneralLinear.reindex (R := K.Carrier) (finCongr (Nat.add_comm 0 b))).toMonoidHom) := by
  letI := T.topology
  intro A B
  let e : (BinaryTensor.rankZeroLeft (R := K.Carrier) rfl A B.representation).Equiv
      ((BinaryTensor.rankZeroRight (R := K.Carrier) rfl B.representation A).comp
        (GeneralLinear.reindex (R := K.Carrier) (finCongr (Nat.add_comm 0 b))).toMonoidHom) :=
    Representation.Equiv.mk (TensorProduct.comm ℂ A B) fun g =>
      TensorProduct.ext' fun v w => by
        change (TensorProduct.comm ℂ A B)
            (v ⊗ₜ B.representation
              (GeneralLinear.reindex (R := K.Carrier) (finCongr (Nat.zero_add b)) g) w) =
          B.representation
              (GeneralLinear.reindex (R := K.Carrier) (finCongr (Nat.add_zero b))
                (GeneralLinear.reindex (R := K.Carrier) (finCongr (Nat.add_comm 0 b)) g)) w ⊗ₜ v
        rw [TensorProduct.comm_tmul, reindex_trans]
  exact (binaryLeftZeroTensorEquiv T rfl (A, B)).trans
    (e.trans (BinaryTensor.compEquiv (binaryRightZeroTensorEquiv T rfl (B, A)).symm _))

/-- Commutativity on arbitrary finite-length classes when the first rank is zero. -/
private theorem zeroLeft_classes (b : ℕ) :
    letI := T.topology
    ∀ (A : FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear 0 K.Carrier))
      (B : FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear b K.Carrier)),
      multiplication T h (inclusion T 0 (ofObject A)) (inclusion T b (ofObject B)) =
        multiplication T h (inclusion T b (ofObject B)) (inclusion T 0 (ofObject A)) := by
  let := T.topology
  intro A B
  rw [multiplication_homogeneous, multiplication_homogeneous,
    binaryProduct_objects, binaryProduct_objects]
  exact inclusion_eq_of_reindexEquiv T (Nat.add_comm 0 b) _ _ _ _
    (zeroLeftProductEquiv T b A.val B.val)

/-! ### Positive ranks -/

private theorem productObj_eq_of_shape {n : ℕ} {D E : BlockShape n} (hDE : D = E)
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

/-- Transporting the total rank commutes with normalized product induction. -/
private def productRankCastEquiv {m n : ℕ} (e : m = n) (D : BlockShape n)
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

private theorem reverse_binary {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (BlockShape.binary a b ha hb).reverse =
      (BlockShape.binary b a hb ha).rankCast (Nat.add_comm b a) := by
  change BlockShape.mk 2 (fun i : Fin 2 => Fin.cases
    (motive := fun _ : Fin 2 => ℕ) a (fun _ => b) i.rev) _ _ =
    BlockShape.mk 2 (Fin.cases b (fun _ => a)) _ _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- At positive ranks, the binary products of two irreducible factors in the two orders have
the same Jordan–Hölder factors after the rank transport. -/
private theorem sameFactors_binary {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a K.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b K.Carrier)),
      A.IsIrreducible → B.IsIrreducible →
      HaveSameJordanHolderFactors ((binaryNormalizedProductFunctor T a b).obj (A, B)).obj
        (SmoothRep.pullback (reindexContinuous (R := K.Carrier) (finCongr (Nat.add_comm a b)))
          ((binaryNormalizedProductFunctor T b a).obj (B, A))).obj := by
  let := T.topology
  intro A B hA hB
  let AB := BlockShape.binary a b ha hb
  let BA := BlockShape.binary b a hb ha
  let σ := (binaryPairFamilyFunctor T ha hb).obj (A, B)
  let τ := (binaryPairFamilyFunctor T hb ha).obj (B, A)
  have hσ (i : Fin AB.length) : (σ i).IsIrreducible := by
    fin_cases i
    · exact hA
    · exact hB
  have hf : HEq (fun i : Fin AB.reverse.length => σ i.rev)
      (fun i : Fin (BA.rankCast (Nat.add_comm b a)).length => τ i) := by
    refine Function.hfunext rfl fun i j hij => ?_
    obtain rfl := eq_of_heq hij
    fin_cases i <;> rfl
  have hr := productObj_eq_of_shape T (reverse_binary ha hb) _ _ hf
  let e₁ := SmoothRep.equivOfIso ((binaryNormalizedProductPositiveIso T ha hb).app (A, B))
  let e₂ := SmoothRep.equivOfIso (eqToIso hr)
  let e₃ := productRankCastEquiv T (Nat.add_comm a b) BA τ
  let e₄ := SmoothRep.equivOfIso ((binaryNormalizedProductPositiveIso T hb ha).app (B, A))
  let E := Parabolic.equivTrans e₂ (Parabolic.equivTrans (Parabolic.equivSymm e₃)
    (Parabolic.equivPrecomp (Parabolic.equivSymm e₄)
      (reindex (R := K.Carrier) (finCongr (Nat.add_comm a b))).toMonoidHom))
  exact haveSameJordanHolderFactors_transport
    (sameFactors_reverseProduct T (Nat.add_pos_left ha b) AB σ hσ) (Parabolic.equivSymm e₁) E

/-- Commutativity on irreducible classes at positive ranks. -/
private theorem positive_classes {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a K.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b K.Carrier))
      (hA : A.IsIrreducible) (hB : B.IsIrreducible),
      multiplication T h
          (inclusion T a (ofRepresentation A (hasFiniteLength_of_isIrreducible hA)))
          (inclusion T b (ofRepresentation B (hasFiniteLength_of_isIrreducible hB))) =
        multiplication T h
          (inclusion T b (ofRepresentation B (hasFiniteLength_of_isIrreducible hB)))
          (inclusion T a (ofRepresentation A (hasFiniteLength_of_isIrreducible hA))) := by
  let := T.topology
  intro A B hA hB
  let LA := hasFiniteLength_of_isIrreducible hA
  let LB := hasFiniteLength_of_isIrreducible hB
  let P := (binaryNormalizedProductFunctor T a b).obj (A, B)
  let Q := (binaryNormalizedProductFunctor T b a).obj (B, A)
  let e := reindexContinuous (R := K.Carrier) (finCongr (Nat.add_comm a b))
  have hP : P.HasFiniteLength := (h K.Carrier T a b).1 A B LA LB
  have hQ : Q.HasFiniteLength := (h K.Carrier T b a).1 B A LB LA
  have hcast : (SmoothRep.pullback e Q).HasFiniteLength :=
    pullbackFunctor_preservesFiniteLength e Q hQ
  have hm := sameFactors_binary.{uF, uV} T ha hb A B hA hB
  have heq := ofRepresentation_eq_of_haveSameJordanHolderFactors hP hcast hm
  rw [multiplication_homogeneous, multiplication_homogeneous]
  change inclusion T (a + b) (binaryProduct T h a b (ofObject ⟨A, LA⟩) (ofObject ⟨B, LB⟩)) =
    inclusion T (b + a) (binaryProduct T h b a (ofObject ⟨B, LB⟩) (ofObject ⟨A, LA⟩))
  rw [binaryProduct_objects, binaryProduct_objects]
  exact (congrArg (inclusion T (a + b)) heq).trans
    (inclusion_eq_of_reindexEquiv T (Nat.add_comm a b) _ _ hcast hQ
      (Representation.Equiv.refl _))

/-! ### The whole graded sum -/

/-- Commutativity on homogeneous irreducible classes in every pair of ranks. -/
private theorem irreducible_classes (a b : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a K.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b K.Carrier))
      (hA : A.IsIrreducible) (hB : B.IsIrreducible),
      multiplication T h
          (inclusion T a (ofRepresentation A (hasFiniteLength_of_isIrreducible hA)))
          (inclusion T b (ofRepresentation B (hasFiniteLength_of_isIrreducible hB))) =
        multiplication T h
          (inclusion T b (ofRepresentation B (hasFiniteLength_of_isIrreducible hB)))
          (inclusion T a (ofRepresentation A (hasFiniteLength_of_isIrreducible hA))) := by
  let := T.topology
  intro A B hA hB
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact zeroLeft_classes T h b ⟨A, hasFiniteLength_of_isIrreducible hA⟩
      ⟨B, hasFiniteLength_of_isIrreducible hB⟩
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · exact (zeroLeft_classes T h a ⟨B, hasFiniteLength_of_isIrreducible hB⟩
      ⟨A, hasFiniteLength_of_isIrreducible hA⟩).symm
  exact positive_classes T h ha hb A B hA hB

/-- The graded normalized product is commutative on the whole graded exact Grothendieck
group, including the rank-zero summand. -/
theorem multiplication_comm (x y : GradedGrothendieckGroup.{uF, uV} T) :
    multiplication T h x y = multiplication T h y x := by
  let := T.topology
  let m := multiplication T h
  have hm : m = m.flip := by
    apply DirectSum.linearMap_ext
    intro a
    refine hom_ext_irreducible ℂ (GeneralLinear a K.Carrier)
      (M := GradedGrothendieckGroup.{uF, uV} T →ₗ[ℤ] GradedGrothendieckGroup.{uF, uV} T)
      (l₁ := m.comp (inclusion T a)) (l₂ := m.flip.comp (inclusion T a)) ?_
    intro A hA
    let xA := inclusion T a (ofRepresentation A (hasFiniteLength_of_isIrreducible hA))
    apply DirectSum.linearMap_ext
    intro b
    exact hom_ext_irreducible ℂ (GeneralLinear b K.Carrier)
      (M := GradedGrothendieckGroup.{uF, uV} T)
      (l₁ := (m xA).comp (inclusion T b)) (l₂ := (m.flip xA).comp (inclusion T b))
      (fun B hB => irreducible_classes T h a b A B hA hB)
  exact LinearMap.congr_fun (LinearMap.congr_fun hm x) y

/-- Commutativity of the graded normalized GL product over every nonarchimedean local
field. -/
theorem localFieldGradedCommutativity : LocalFieldGradedCommutativityStatement.{uF, uV} := by
  intro K T h
  exact multiplication_comm T h

end Langlands.Aubert.LocalFieldGraded
