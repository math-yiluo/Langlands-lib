import Langlands.Representation.Aubert.GradedInductionUnitProof
import Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof
import Langlands.Representation.Smooth.JordanHolderGrothendieck

/-! Commutativity of the actual graded normalized-induction product. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Aubert

universe uF uV uK uG uW uM

open SmoothRep.FiniteLengthGrothendieckGroup

/-- Maps out of exact finite-length K0 are determined by irreducible classes. -/
theorem hom_ext_irreducible
    (k : Type uK) [Field k] (G : Type uG) [Group G] [TopologicalSpace G]
    {M : Type uM} [AddCommMonoid M] [Module ℤ M]
    {l₁ l₂ : SmoothRep.FiniteLengthGrothendieckGroup.{uK, uG, uW} k G →ₗ[ℤ] M}
    (h : ∀ (A : SmoothRep.{uK, uG, uW} k G) (hA : A.IsIrreducible),
      l₁ (ofRepresentation A (SmoothRep.hasFiniteLength_of_isIrreducible hA)) =
        l₂ (ofRepresentation A (SmoothRep.hasFiniteLength_of_isIrreducible hA))) :
    l₁ = l₂ := by
  have he : l₁.comp (SmoothRep.realizeIrreducibles k G) =
      l₂.comp (SmoothRep.realizeIrreducibles k G) := by
    apply Finsupp.lhom_ext
    intro c z
    obtain ⟨A, hA, rfl⟩ := SmoothRep.IrreducibleIsoClass.exists_eq c
    have hz : Finsupp.single (SmoothRep.irreducibleIsoClass A hA) z =
        z • VirtualRepresentation.generator (SmoothRep.irreducibleIsoClass A hA) := by
      simp [VirtualRepresentation.generator]
    simp only [hz, LinearMap.map_smul, LinearMap.comp_apply]
    rw [SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass A hA
      (SmoothRep.hasFiniteLength_of_isIrreducible hA), h A hA]
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := (SmoothRep.irreducibleGrothendieckStatement k G).2 x
  exact LinearMap.congr_fun he v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Rank transport does not change the homogeneous class in the graded sum. -/
theorem gradedInclusion_rankCast {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (hA : A.HasFiniteLength),
      gradedInclusion F T b (ofRepresentation ((Derivative.generalLinearRankCast T h).obj A)
        (Derivative.ProductDerivativesFiniteLength.hasFiniteLength_rankCast T h A hA)) =
      gradedInclusion F T a (ofRepresentation A hA) := by
  subst h
  intros
  rfl

namespace GradedCommutativityProof

open GeneralLinear

private def productFunctor_obj_congr {n : ℕ} {B C : BlockShape n} (h : B = C)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (A' : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (C.size i) F.Carrier))
    (hA : HEq A A') :
    letI := T.topology
    (T.normalizedProductInductionFunctor B).obj A ≅
      (T.normalizedProductInductionFunctor C).obj A' := by
  letI := T.topology
  subst h
  obtain rfl := eq_of_heq hA
  exact Iso.refl _

private def rankCastProductIso {m n : ℕ} (h : m = n) (B : BlockShape m)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (Derivative.generalLinearRankCast T h).obj
        ((T.normalizedProductInductionFunctor B).obj A) ≅
      (T.normalizedProductInductionFunctor (B.rankCast h)).obj A := by
  subst h
  exact Iso.refl _

private theorem swap_binary {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (BlockShape.binary b a hb ha).rankCast (Nat.add_comm b a) =
      (BlockShape.binary a b ha hb).permute
        ((BlockShape.binary a b ha hb).adjacentSwap 0 (by change 1 < 2; omega)) := by
  change BlockShape.mk 2 (Fin.cases b (fun _ => a)) _ _ =
    BlockShape.mk 2
      (fun i => Fin.cases (motive := fun _ : Fin 2 => ℕ) a (fun _ => b)
        (Equiv.swap (0 : Fin 2) 1 i)) _ _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Constituent matching for positive irreducible factors, with the actual
binary shapes and the reversed-sum rank cast. -/
theorem positive_irreducible_classes
    (hx : BinaryProductExactnessStatement.{uF, uV} F T)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
      (hA : A.IsIrreducible) (hB : B.IsIrreducible),
      gradedMultiplication F T hx
          (gradedInclusion F T a (ofRepresentation A
            (SmoothRep.hasFiniteLength_of_isIrreducible hA)))
          (gradedInclusion F T b (ofRepresentation B
            (SmoothRep.hasFiniteLength_of_isIrreducible hB))) =
        gradedMultiplication F T hx
          (gradedInclusion F T b (ofRepresentation B
            (SmoothRep.hasFiniteLength_of_isIrreducible hB)))
          (gradedInclusion F T a (ofRepresentation A
            (SmoothRep.hasFiniteLength_of_isIrreducible hA))) := by
  let := T.topology
  intro A B hA hB
  let BA := BlockShape.binary a b ha hb
  let BB := BlockShape.binary b a hb ha
  let fab := (T.binaryPairFamilyFunctor ha hb).obj (A, B)
  let fba := (T.binaryPairFamilyFunctor hb ha).obj (B, A)
  let σ := BA.adjacentSwap 0 (by change 1 < 2; omega)
  have hirr : ∀ i, (fab i).IsIrreducible := by
    intro i
    fin_cases i
    · exact hA
    · exact hB
  have hfam : HEq (fun i : Fin (BA.permute σ).length => fab (σ i))
      (fun i : Fin (BB.rankCast (Nat.add_comm b a)).length => fba i) := by
    refine Function.hfunext rfl fun i i' hi => ?_
    obtain rfl := eq_of_heq hi
    fin_cases i <;> exact HEq.rfl
  let e := (productFunctor_obj_congr F T (swap_binary ha hb).symm _ _ hfam) ≪≫
    (rankCastProductIso F T (Nat.add_comm b a) BB fba).symm
  have hm := Classification.twoFactorProductConstituentCommutativity F T
    (a + b) BA rfl fab hirr
  have hm' := haveSameJordanHolderFactors_transport
    (C := ((T.normalizedProductInductionFunctor BA).obj fab).obj)
    hm (Representation.Equiv.refl _) (SmoothRep.equivOfIso e)
  let LA := SmoothRep.hasFiniteLength_of_isIrreducible hA
  let LB := SmoothRep.hasFiniteLength_of_isIrreducible hB
  let P := (T.binaryNormalizedProductFunctor a b).obj (A, B)
  let Q := (T.binaryNormalizedProductFunctor b a).obj (B, A)
  have hP := binaryProduct_preservesFiniteLength F T a b A B LA LB
  have hQ := binaryProduct_preservesFiniteLength F T b a B A LB LA
  have hcast := Derivative.ProductDerivativesFiniteLength.hasFiniteLength_rankCast T
    (Nat.add_comm b a) Q hQ
  have hm'' : HaveSameJordanHolderFactors P.obj
      ((Derivative.generalLinearRankCast T (Nat.add_comm b a)).obj Q).obj := by
    simpa only [P, Q, T.binaryNormalizedProductFunctor_of_pos ha hb,
      T.binaryNormalizedProductFunctor_of_pos hb ha,
      PadicField.TopologicalData.binaryPositiveProductFunctor, Functor.comp_obj,
      BA, BB, fab, fba] using hm'
  have hc := ofRepresentation_eq_of_haveSameJordanHolderFactors hP hcast hm''
  rw [gradedMultiplication_homogeneous, gradedMultiplication_homogeneous]
  change gradedInclusion F T (a + b) (binaryProductK0 F T hx a b (ofObject ⟨A, LA⟩)
      (ofObject ⟨B, LB⟩)) =
    gradedInclusion F T (b + a) (binaryProductK0 F T hx b a (ofObject ⟨B, LB⟩)
      (ofObject ⟨A, LA⟩))
  rw [binaryProductK0_classes, binaryProductK0_classes]
  exact (congrArg (gradedInclusion F T (a + b)) hc).trans
    (gradedInclusion_rankCast F T (Nat.add_comm b a) Q hQ)

private theorem reindex_trans {a b c : ℕ} (h : a = b) (k : b = c)
    (g : GeneralLinear a F.Carrier) :
    GeneralLinear.reindex (R := F.Carrier) (finCongr k)
        (GeneralLinear.reindex (R := F.Carrier) (finCongr h) g) =
      GeneralLinear.reindex (R := F.Carrier) (finCongr (h.trans k)) g := by
  subst h
  subst k
  simp only [GeneralLinear.reindex_finCongr_rfl, MulEquiv.refl_apply]

/-- The tensor commutor compares arbitrary zero-rank factors, including
arbitrary objects on both sides at rank (0,0). -/
def zeroLeftProductEquiv (b : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)),
      ((T.binaryNormalizedProductFunctor 0 b).obj (A, B)).representation.Equiv
        (((T.binaryNormalizedProductFunctor b 0).obj (B, A)).representation.comp
          (GeneralLinear.reindex (R := F.Carrier) (finCongr (Nat.add_comm 0 b))).toMonoidHom) := by
  letI := T.topology
  intro A B
  let e : (BinaryTensor.rankZeroLeft (R := F.Carrier) rfl A B.representation).Equiv
      ((BinaryTensor.rankZeroRight (R := F.Carrier) rfl B.representation A).comp
        (GeneralLinear.reindex (R := F.Carrier) (finCongr (Nat.add_comm 0 b))).toMonoidHom) :=
    Representation.Equiv.mk (TensorProduct.comm ℂ A B) fun g =>
      TensorProduct.ext' fun v w => by
        change (TensorProduct.comm ℂ A B)
            (v ⊗ₜ B.representation
              (GeneralLinear.reindex (R := F.Carrier) (finCongr (Nat.zero_add b)) g) w) =
          B.representation
              (GeneralLinear.reindex (R := F.Carrier) (finCongr (Nat.add_zero b))
                (GeneralLinear.reindex (R := F.Carrier) (finCongr (Nat.add_comm 0 b)) g)) w ⊗ₜ v
        rw [TensorProduct.comm_tmul, reindex_trans F]
  exact (T.binaryLeftZeroTensorEquiv rfl (A, B)).trans
    (e.trans (BinaryTensor.compEquiv (T.binaryRightZeroTensorEquiv rfl (B, A)).symm _))

/-- Commutativity on arbitrary actual classes when the first rank is zero. -/
theorem zeroLeft_object_classes
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) (b : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier))
      (B : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)),
      gradedMultiplication F T hx
          (gradedInclusion F T 0 (ofObject A)) (gradedInclusion F T b (ofObject B)) =
        gradedMultiplication F T hx
          (gradedInclusion F T b (ofObject B)) (gradedInclusion F T 0 (ofObject A)) := by
  let := T.topology
  intro A B
  rw [gradedMultiplication_homogeneous, gradedMultiplication_homogeneous,
    binaryProductK0_classes, binaryProductK0_classes]
  exact gradedInclusion_eq_of_rank_equiv F T (Nat.add_comm 0 b) _ _ _ _
    (zeroLeftProductEquiv F T b A.val B.val)

/-- Commutativity on homogeneous irreducible classes in every pair of ranks. -/
theorem irreducible_classes
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) (a b : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
      (hA : A.IsIrreducible) (hB : B.IsIrreducible),
      gradedMultiplication F T hx
          (gradedInclusion F T a (ofRepresentation A
            (SmoothRep.hasFiniteLength_of_isIrreducible hA)))
          (gradedInclusion F T b (ofRepresentation B
            (SmoothRep.hasFiniteLength_of_isIrreducible hB))) =
        gradedMultiplication F T hx
          (gradedInclusion F T b (ofRepresentation B
            (SmoothRep.hasFiniteLength_of_isIrreducible hB)))
          (gradedInclusion F T a (ofRepresentation A
            (SmoothRep.hasFiniteLength_of_isIrreducible hA))) := by
  let := T.topology
  intro A B hA hB
  by_cases ha : a = 0
  · subst a
    exact zeroLeft_object_classes F T hx b
      ⟨A, SmoothRep.hasFiniteLength_of_isIrreducible hA⟩
      ⟨B, SmoothRep.hasFiniteLength_of_isIrreducible hB⟩
  by_cases hb : b = 0
  · subst b
    exact (zeroLeft_object_classes F T hx a
      ⟨B, SmoothRep.hasFiniteLength_of_isIrreducible hB⟩
      ⟨A, SmoothRep.hasFiniteLength_of_isIrreducible hA⟩).symm
  exact positive_irreducible_classes F T hx
    (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) A B hA hB

end GradedCommutativityProof

/-- Commutativity of the actual all-ranks product on the full graded exact K0. -/
theorem gradedMultiplication_comm
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) :
    letI := T.topology
    ∀ x y, gradedMultiplication F T hx x y = gradedMultiplication F T hx y x := by
  let := T.topology
  have h : gradedMultiplication F T hx = (gradedMultiplication F T hx).flip := by
    apply DirectSum.linearMap_ext
    intro a
    refine hom_ext_irreducible ℂ (GeneralLinear a F.Carrier)
      (M := GradedGrothendieckGroup.{uF, uV} F T →ₗ[ℤ]
        GradedGrothendieckGroup.{uF, uV} F T)
      (l₁ := (gradedMultiplication F T hx).comp (gradedInclusion F T a))
      (l₂ := (gradedMultiplication F T hx).flip.comp (gradedInclusion F T a)) ?_
    intro A hA
    apply DirectSum.linearMap_ext
    intro b
    exact hom_ext_irreducible ℂ (GeneralLinear b F.Carrier)
      (M := GradedGrothendieckGroup.{uF, uV} F T)
      (l₁ := (gradedMultiplication F T hx
        (gradedInclusion F T a (ofRepresentation A
          (SmoothRep.hasFiniteLength_of_isIrreducible hA)))).comp (gradedInclusion F T b))
      (l₂ := ((gradedMultiplication F T hx).flip
        (gradedInclusion F T a (ofRepresentation A
          (SmoothRep.hasFiniteLength_of_isIrreducible hA)))).comp (gradedInclusion F T b))
      (fun B hB => GradedCommutativityProof.irreducible_classes F T hx a b A B hA hB)
  intro x y
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

end Langlands.Aubert
