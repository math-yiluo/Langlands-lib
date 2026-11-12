import Langlands.Representation.Aubert.ZelevinskyComparison
import Langlands.Representation.Aubert.ProductLeviTensorPrerequisitesProof
import Langlands.Representation.Aubert.InductionCommutationProof
import Langlands.Representation.Parabolic.RefinedJacquetTensor
import Langlands.Representation.Parabolic.RefinedInductionTensorProof
import Langlands.Representation.Aubert.SupportGrading
import Langlands.Representation.Aubert.GradedInductionAssociativityProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof

/-!
# Homogeneous multiplicativity of the support-adjusted GL Aubert operator

The proof factors each positive binary product-Levi refinement term through the
actual external tensor functors, then applies induction commutation. Actual
supercuspidal supports determine the sign of every irreducible constituent.
The rank-zero cases use the actual GL₀ unit and its exact-K0 spanning property.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Aubert

open GeneralLinear Geometric Parabolic SmoothRep
open SmoothRep.FiniteLengthGrothendieckGroup
open SmoothRep.IrreducibleGrothendieckProof SmoothRep.IrreducibleOperator
open VirtualRepresentation

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private def refinedInductionJacquetTensorEquiv {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (T.normalizedRefinedInductionFunctor B S).obj
      ((T.normalizedRefinedJacquetFunctor B S).obj (FiniteTensor.externalSmoothObject A)) ≅
      FiniteTensor.externalSmoothObject (fun i =>
        (T.normalizedParabolicInductionFunctor (S i)).obj
          ((T.normalizedJacquetFunctor (S i)).obj (A i))) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  let D : RefinedInductionTensor.Factors F T B S :=
    fun i => (T.normalizedJacquetFunctor (S i)).obj (A i)
  let e := RefinedJacquetTensor.jacquetEquiv T B S (fun i => (A i).obj)
  let e' : (T.normalizedRefinedInduced B S
      (T.normalizedRefinedJacquet B S (FiniteTensor.external fun i => (A i).representation))).Equiv
      (RefinedInductionTensor.refinedRepresentation F T B S D) :=
    Induction.smoothInducedEquiv (refinedParabolic F.Carrier B S)
      (twistEquiv (T.refinedParabolicHalfModulus B S)
        (Representation.Equiv.mk e.toLinearEquiv
          (fun q => e.isIntertwining' (refinedLeviProjection F.Carrier B S q))))
  exact SmoothRep.mkIso
    (e'.trans (refinedInductionTensor.{uF, max uF uV} p F T n B S D).some.val)

private theorem refinedInductionJacquetClass {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)) (hA : A.HasFiniteLength)
      (hOut : ((T.normalizedRefinedInductionFunctor B S).obj
        ((T.normalizedRefinedJacquetFunctor B S).obj A)).HasFiniteLength),
    normalizedRefinedInductionK0 F T B S
      (normalizedRefinedJacquetK0 F T B S (ofRepresentation A hA)) =
      ofRepresentation ((T.normalizedRefinedInductionFunctor B S).obj
        ((T.normalizedRefinedJacquetFunctor B S).obj A)) hOut := by
  let := T.topology
  intro A hA hOut
  have hJ := (normalizedRefinedFiniteLengthExactness F T).2.1 _ B S A hA
  exact (congrArg (normalizedRefinedInductionK0 F T B S)
    (normalizedRefinedJacquetK0_finiteLengthClass F T B S A hA hJ)).trans
    (normalizedRefinedInductionK0_finiteLengthClass F T B S _ hJ hOut)

private theorem refinedInductionJacquetClass_iso {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B) :
    letI := T.topology
    ∀ (A V : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier))
      (hA : A.HasFiniteLength) (hV : V.HasFiniteLength)
      (_e : (T.normalizedRefinedInductionFunctor B S).obj
        ((T.normalizedRefinedJacquetFunctor B S).obj A) ≅ V),
    normalizedRefinedInductionK0 F T B S
      (normalizedRefinedJacquetK0 F T B S (ofRepresentation A hA)) =
      ofRepresentation V hV := by
  let := T.topology
  intro A V hA hV e
  have hI := refinedInductionJacquet_hasFiniteLength F T B A hA S
  exact (refinedInductionJacquetClass F T B S A hA hI).trans
    (ofObject_eq_of_iso (A := ⟨_, hI⟩) (B := ⟨V, hV⟩) e)

private theorem refinedInductionJacquetTensorClass {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    ∀ (hA : (FiniteTensor.externalSmoothObject A).HasFiniteLength)
      (hOut : (FiniteTensor.externalSmoothObject (fun i =>
        (T.normalizedParabolicInductionFunctor (S i)).obj
          ((T.normalizedJacquetFunctor (S i)).obj (A i)))).HasFiniteLength),
    normalizedRefinedInductionK0 F T B S
      (normalizedRefinedJacquetK0 F T B S
        (ofRepresentation (FiniteTensor.externalSmoothObject A) hA)) =
      ofRepresentation (FiniteTensor.externalSmoothObject (fun i =>
        (T.normalizedParabolicInductionFunctor (S i)).obj
          ((T.normalizedJacquetFunctor (S i)).obj (A i)))) hOut := by
  let := T.topology
  intro hA hOut
  exact refinedInductionJacquetClass_iso.{uF, uV} F T B S
    (FiniteTensor.externalSmoothObject A)
    (FiniteTensor.externalSmoothObject (fun i =>
      (T.normalizedParabolicInductionFunctor (S i)).obj
        ((T.normalizedJacquetFunctor (S i)).obj (A i))))
    hA hOut (refinedInductionJacquetTensorEquiv.{uF, uV} F T B S A)

private theorem binaryRefinedTerm {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (S : BlockRefinement (BlockShape.binary a b ha hb))
    (A : letI := T.topology; FiniteLengthObject.{0, uF, max uF uV} ℂ
      (GeneralLinear a F.Carrier))
    (C : letI := T.topology; FiniteLengthObject.{0, uF, max uF uV} ℂ
      (GeneralLinear b F.Carrier)) :
    letI := T.topology
    let B := BlockShape.binary a b ha hb
    let hp := productLeviTensorPrerequisites.{uF, uV} F T ha hb
    normalizedRefinedInductionK0 F T B S
      (normalizedRefinedJacquetK0 F T B S
        (productLeviTensorMap F T ha hb hp (ofObject A ⊗ₜ[ℤ] ofObject C))) =
      productLeviTensorMap F T ha hb hp
        (normalizedInductionK0 F T (S (0 : Fin 2))
          (normalizedJacquetK0 F T (S (0 : Fin 2)) (ofObject A)) ⊗ₜ[ℤ]
          normalizedInductionK0 F T (S (1 : Fin 2))
            (normalizedJacquetK0 F T (S (1 : Fin 2)) (ofObject C))) := by
  let := T.topology
  let B := BlockShape.binary a b ha hb
  let hp := productLeviTensorPrerequisites.{uF, uV} F T ha hb
  let X := (T.binaryPairFamilyFunctor ha hb).obj (A.val, C.val)
  let L := FiniteTensor.externalSmoothObject X
  have hL : L.HasFiniteLength := hp.1 A.val C.val A.property C.property
  let J i := (T.normalizedJacquetFunctor (S i)).obj (X i)
  have hJ i : (J i).HasFiniteLength :=
    normalizedJacquetK0_hasFiniteLength F T (S i) (X i) (by
      fin_cases i
      · exact A.property
      · exact C.property)
  let I i := (T.normalizedParabolicInductionFunctor (S i)).obj (J i)
  have hI i : (I i).HasFiniteLength :=
    normalizedInductionK0_hasFiniteLength F T (S i) (J i) (hJ i)
  let V := (binaryProductLeviTensorFunctor F T ha hb).obj (I (0 : Fin 2), I (1 : Fin 2))
  have hV : V.HasFiniteLength := hp.1 _ _ (hI (0 : Fin 2)) (hI (1 : Fin 2))
  have hfamily : I = (T.binaryPairFamilyFunctor ha hb).obj (I (0 : Fin 2), I (1 : Fin 2)) := by
    funext i
    fin_cases i <;> rfl
  have hO : (FiniteTensor.externalSmoothObject I).HasFiniteLength :=
    (congrArg (fun Z => (FiniteTensor.externalSmoothObject Z).HasFiniteLength) hfamily).mpr hV
  have hleft : normalizedRefinedInductionK0 F T B S
      (normalizedRefinedJacquetK0 F T B S
        (productLeviTensorMap F T ha hb hp (ofObject A ⊗ₜ[ℤ] ofObject C))) =
      ofRepresentation (FiniteTensor.externalSmoothObject I) hO :=
    (congrArg (fun z => normalizedRefinedInductionK0 F T B S
        (normalizedRefinedJacquetK0 F T B S z))
      (productLeviTensorMap_classes F T ha hb hp A C)).trans
      (refinedInductionJacquetTensorClass.{uF, uV} F T B S X hL hO)
  have hzero : normalizedInductionK0 F T (S (0 : Fin 2))
      (normalizedJacquetK0 F T (S (0 : Fin 2)) (ofObject A)) =
      ofObject (⟨I (0 : Fin 2), hI (0 : Fin 2)⟩ : FiniteLengthObject ℂ (GeneralLinear a F.Carrier)) :=
    (congrArg (normalizedInductionK0 F T (S (0 : Fin 2)))
      (normalizedJacquetK0_finiteLengthClass F T (S (0 : Fin 2)) A.val A.property
        (hJ (0 : Fin 2)))).trans
      (normalizedInductionK0_finiteLengthClass F T (S (0 : Fin 2)) (J (0 : Fin 2))
        (hJ (0 : Fin 2)) (hI (0 : Fin 2)))
  have hone : normalizedInductionK0 F T (S (1 : Fin 2))
      (normalizedJacquetK0 F T (S (1 : Fin 2)) (ofObject C)) =
      ofObject (⟨I (1 : Fin 2), hI (1 : Fin 2)⟩ : FiniteLengthObject ℂ (GeneralLinear b F.Carrier)) :=
    (congrArg (normalizedInductionK0 F T (S (1 : Fin 2)))
      (normalizedJacquetK0_finiteLengthClass F T (S (1 : Fin 2)) C.val C.property
        (hJ (1 : Fin 2)))).trans
      (normalizedInductionK0_finiteLengthClass F T (S (1 : Fin 2)) (J (1 : Fin 2))
        (hJ (1 : Fin 2)) (hI (1 : Fin 2)))
  have hright := (congrArg (productLeviTensorMap F T ha hb hp)
      (congrArg₂ (fun z w => z ⊗ₜ[ℤ] w) hzero hone)).trans
    (productLeviTensorMap_classes F T ha hb hp ⟨I (0 : Fin 2), hI (0 : Fin 2)⟩
      ⟨I (1 : Fin 2), hI (1 : Fin 2)⟩)
  exact hleft.trans ((ofObject_eq_of_iso
    (A := ⟨FiniteTensor.externalSmoothObject I, hO⟩) (B := ⟨V, hV⟩)
    (eqToIso (congrArg FiniteTensor.externalSmoothObject hfamily))).trans hright.symm)

private theorem binaryAlternatingTensor {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (x : letI := T.topology; GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} a F.Carrier)
    (y : letI := T.topology; GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} b F.Carrier) :
    letI := T.topology
    let B := BlockShape.binary a b ha hb
    let hp := productLeviTensorPrerequisites.{uF, uV} F T ha hb
    alternatingOperatorOnLevi F T B (productLeviTensorMap F T ha hb hp (x ⊗ₜ[ℤ] y)) =
      productLeviTensorMap F T ha hb hp
        (alternatingOperator F T a x ⊗ₜ[ℤ] alternatingOperator F T b y) := by
  let := T.topology
  classical
  let B := BlockShape.binary a b ha hb
  let hp := productLeviTensorPrerequisites.{uF, uV} F T ha hb
  let f := productLeviTensorMap F T ha hb hp
  have hterm (S : BlockRefinement B) (x) (y) :
      normalizedRefinedInductionK0 F T B S
        (normalizedRefinedJacquetK0 F T B S (f (x ⊗ₜ[ℤ] y))) =
      f (normalizedInductionK0 F T (S (0 : Fin 2))
          (normalizedJacquetK0 F T (S (0 : Fin 2)) x) ⊗ₜ[ℤ]
        normalizedInductionK0 F T (S (1 : Fin 2))
          (normalizedJacquetK0 F T (S (1 : Fin 2)) y)) := by
    have he : ((normalizedRefinedInductionK0 F T B S).comp
          (normalizedRefinedJacquetK0 F T B S)).comp f =
        f.comp (TensorProduct.map
          ((normalizedInductionK0 F T (S (0 : Fin 2))).comp
            (normalizedJacquetK0 F T (S (0 : Fin 2))))
          ((normalizedInductionK0 F T (S (1 : Fin 2))).comp
            (normalizedJacquetK0 F T (S (1 : Fin 2))))) := by
      apply TensorProduct.ext
      apply bilinear_ext
      exact binaryRefinedTerm F T ha hb S
    exact LinearMap.congr_fun he (x ⊗ₜ[ℤ] y)
  let : ∀ i : Fin B.length, Fintype (BlockShape (B.size i)) :=
    fun _ => Fintype.ofFinite _
  let : Fintype (BlockShape a) := Fintype.ofFinite _
  let : Fintype (BlockShape b) := Fintype.ofFinite _
  let : Fintype (BlockRefinement B) :=
    inferInstanceAs (Fintype (∀ i : Fin 2, BlockShape (B.size i)))
  let g (q : BlockShape a × BlockShape b) :=
    (((-1 : ℤ) ^ (a - q.1.length)) * ((-1 : ℤ) ^ (b - q.2.length))) •
      f (normalizedInductionK0 F T q.1 (normalizedJacquetK0 F T q.1 x) ⊗ₜ[ℤ]
        normalizedInductionK0 F T q.2 (normalizedJacquetK0 F T q.2 y))
  have hdouble : f (alternatingOperator F T a x ⊗ₜ[ℤ] alternatingOperator F T b y) =
      ∑ q : BlockShape a × BlockShape b, g q := by
    rw [alternatingOperator_apply, alternatingOperator_apply, Fintype.sum_prod_type]
    simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
      TensorProduct.smul_tmul_smul, map_smul, g]
    rw [Finset.sum_comm]
  dsimp only
  rw [alternatingOperatorOnLevi_apply, hdouble]
  apply Fintype.sum_equiv (piFinTwoEquiv fun i => BlockShape (B.size i))
  intro S
  rw [hterm]
  change ((-1 : ℤ) ^ refinementSignExponent B S) • _ =
    (((-1 : ℤ) ^ (a - (S (0 : Fin 2)).length)) *
      ((-1 : ℤ) ^ (b - (S (1 : Fin 2)).length))) • _
  congr 1
  change (-1 : ℤ) ^ (∑ i : Fin 2, (B.size i - (S i).length)) = _
  rw [Fin.sum_univ_two, pow_add]
  rfl

private theorem alternatingOperator_binaryProduct_positive
    (hx : BinaryProductExactnessStatement.{uF, uV} F T)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (x : letI := T.topology; GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} a F.Carrier)
    (y : letI := T.topology; GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} b F.Carrier) :
    letI := T.topology
    alternatingOperator F T (a + b) (binaryProductK0 F T hx a b x y) =
      binaryProductK0 F T hx a b (alternatingOperator F T a x) (alternatingOperator F T b y) := by
  let := T.topology
  let B := BlockShape.binary a b ha hb
  let hp := productLeviTensorPrerequisites.{uF, uV} F T ha hb
  let f := productLeviTensorMap F T ha hb hp
  have hP x y : normalizedInductionK0 F T B (f (x ⊗ₜ[ℤ] y)) =
      binaryProductK0 F T hx a b x y :=
    LinearMap.congr_fun (productLeviInductionTensorMap_eq F T ha hb hp hx) (x ⊗ₜ[ℤ] y)
  calc
    _ = alternatingOperator F T (a + b) (normalizedInductionK0 F T B (f (x ⊗ₜ[ℤ] y))) :=
      congrArg (alternatingOperator F T (a + b)) (hP x y).symm
    _ = normalizedInductionK0 F T B (alternatingOperatorOnLevi F T B (f (x ⊗ₜ[ℤ] y))) :=
      LinearMap.congr_fun (inductionCommutation.{uF, uV} F T (a + b) B) (f (x ⊗ₜ[ℤ] y))
    _ = normalizedInductionK0 F T B
        (f (alternatingOperator F T a x ⊗ₜ[ℤ] alternatingOperator F T b y)) :=
      congrArg (normalizedInductionK0 F T B) (binaryAlternatingTensor.{uF, uV} F T ha hb x y)
    _ = _ := hP _ _

private theorem supportSign_card {n : ℕ}
    (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology; π.IsIrreducible)
    (s : Multiset (PadicField.TopologicalData.CuspidalDatum.{max uF uV, uF} T))
    (hs : T.IsSupercuspidalSupport π s) :
    letI := T.topology
    s.card ≤ n ∧ supportSign F T n (irreducibleIsoClass π hπ) = (-1 : ℤ) ^ (n - s.card) := by
  let := T.topology
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs0 := SupportGrading.eq_zero_of_isSupercuspidalSupport_rankZero hs
    subst s
    exact ⟨by simp, by simp [supportSign_rankZero]⟩
  · obtain ⟨k, ρ, hρs, hρ, A, _, _, hsub⟩ := hs
    let B := T.cuspidalShape ρ hρ
    let σ := FiniteTensor.externalSmoothObject (fun i => (A i).obj)
    have hσ := CuspidalSupport.glCuspidalTensor.{max uF uV, uF} p F T n hn B A
    have hcard : s.card = k := by rw [← hρs]; simp
    refine ⟨?_, ?_⟩
    · rw [hcard]
      exact B.length_le
    · rw [hcard]
      exact supportSign_of_support.{uF, uV} F T B σ hσ.1 hσ.2.2 π hπ hsub

private theorem adjustedOperator_of_constituentSign {n : ℕ}
    (M : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hM : letI := T.topology; M.HasFiniteLength) (s : ℤ)
    (hs : letI := T.topology
      ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
        (hπ : π.IsIrreducible), IsSubquotient π M →
          supportSign F T n (irreducibleIsoClass π hπ) = s) :
    letI := T.topology
    adjustedOperator F T n (GeneralLinear.finiteLengthClass n F.Carrier M hM) =
      s • alternatingOperator F T n (GeneralLinear.finiteLengthClass n F.Carrier M hM) := by
  let := T.topology
  let v := compositionFactors ⟨M, hM⟩
  have hreal : realizeIrreducibles ℂ (GeneralLinear n F.Carrier) v =
      GeneralLinear.finiteLengthClass n F.Carrier M hM := by
    change realizeIrreducibles ℂ (GeneralLinear n F.Carrier) (compositionFactors ⟨M, hM⟩) = _
    rw [← factorMap_ofRepresentation M hM]
    exact LinearMap.congr_fun realize_comp_factorMap _
  change adjustedOperator F T n _ = (s • alternatingOperator F T n) _
  rw [← hreal, ← Finsupp.sum_single v]
  simp only [map_finsuppSum]
  apply Finsupp.sum_congr
  intro c hc
  induction c using SmoothRep.IrreducibleIsoClass.inductionOn with
  | h π hπ =>
    have hsub := (mem_support_compositionFactors_iff_isSubquotient ⟨M, hM⟩ π hπ).mp hc
    have hsingle : Finsupp.single (irreducibleIsoClass π hπ) (v (irreducibleIsoClass π hπ)) =
        v (irreducibleIsoClass π hπ) • generator (irreducibleIsoClass π hπ) := by
      simp [generator]
    simp only [hsingle, map_zsmul,
      realizeIrreducibles_generator_irreducibleIsoClass π hπ
        (hasFiniteLength_of_isIrreducible hπ),
      LinearMap.smul_apply]
    have hadj := adjustedOperator_irreducible F T n π hπ
    rw [hs π hπ hsub] at hadj
    exact congrArg (v (irreducibleIsoClass π hπ) • ·) hadj

private theorem adjustedOperator_binaryProduct_positive
    (hx : BinaryProductExactnessStatement.{uF, uV} F T)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (x : letI := T.topology; GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} a F.Carrier)
    (y : letI := T.topology; GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} b F.Carrier) :
    letI := T.topology
    adjustedOperator F T (a + b) (binaryProductK0 F T hx a b x y) =
      binaryProductK0 F T hx a b (adjustedOperator F T a x) (adjustedOperator F T b y) := by
  let := T.topology
  induction x using SupportGrading.induction_irreducible (T := T) generalizing y with
  | h0 => simp
  | hadd x x' ih ih' => rw [LinearMap.map_add₂, map_add, ih, ih', map_add, LinearMap.map_add₂]
  | hneg x ih => rw [LinearMap.map_neg₂, map_neg, ih, map_neg, LinearMap.map_neg₂]
  | hirr X hX =>
    induction y using SupportGrading.induction_irreducible (T := T) with
    | h0 => simp
    | hadd y y' ih ih' => rw [map_add, map_add, ih, ih', map_add, map_add]
    | hneg y ih => rw [map_neg, map_neg, ih, map_neg, map_neg]
    | hirr Y hY =>
      have hXL := hasFiniteLength_of_isIrreducible hX
      have hYL := hasFiniteLength_of_isIrreducible hY
      let P := (T.binaryNormalizedProductFunctor.{uF, max uF uV} a b).obj (X, Y)
      have hPL : P.HasFiniteLength := binaryProduct_preservesFiniteLength F T a b X Y hXL hYL
      have hP : binaryProductK0 F T hx a b (GeneralLinear.finiteLengthClass a F.Carrier X hXL)
          (GeneralLinear.finiteLengthClass b F.Carrier Y hYL) =
          GeneralLinear.finiteLengthClass (a + b) F.Carrier P hPL :=
        binaryProductK0_classes F T hx a b ⟨X, hXL⟩ ⟨Y, hYL⟩
      have hsX := SupportGrading.isSupercuspidalSupport_supercuspidalSupport' X hX
      have hsY := SupportGrading.isSupercuspidalSupport_supercuspidalSupport' Y hY
      have hcX := supportSign_card.{uF, uV} F T X hX _ hsX
      have hcY := supportSign_card.{uF, uV} F T Y hY _ hsY
      let sX := supportSign F T a (irreducibleIsoClass X hX)
      let sY := supportSign F T b (irreducibleIsoClass Y hY)
      have hsign (D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + b) F.Carrier))
          (hD : D.IsIrreducible) (hsub : IsSubquotient D P) :
          supportSign F T (a + b) (irreducibleIsoClass D hD) = sX * sY := by
        have hsD := T.binaryProductConstituentSupport hsX hsY hD hsub
        have hcD := supportSign_card.{uF, uV} F T D hD _ hsD
        dsimp only [sX, sY]
        rw [hcD.2, Multiset.card_add, hcX.2, hcY.2, ← pow_add]
        congr 1
        omega
      calc
        _ = adjustedOperator F T (a + b) (GeneralLinear.finiteLengthClass (a + b) F.Carrier P hPL) :=
          congrArg (adjustedOperator F T (a + b)) hP
        _ = (sX * sY) • alternatingOperator F T (a + b)
            (GeneralLinear.finiteLengthClass (a + b) F.Carrier P hPL) :=
          adjustedOperator_of_constituentSign.{uF, uV} F T P hPL (sX * sY) hsign
        _ = (sX * sY) • alternatingOperator F T (a + b)
            (binaryProductK0 F T hx a b (GeneralLinear.finiteLengthClass a F.Carrier X hXL)
              (GeneralLinear.finiteLengthClass b F.Carrier Y hYL)) :=
          congrArg (fun z => (sX * sY) • alternatingOperator F T (a + b) z) hP.symm
        _ = (sX * sY) • binaryProductK0 F T hx a b
            (alternatingOperator F T a (GeneralLinear.finiteLengthClass a F.Carrier X hXL))
            (alternatingOperator F T b (GeneralLinear.finiteLengthClass b F.Carrier Y hYL)) :=
          congrArg ((sX * sY) • ·)
            (alternatingOperator_binaryProduct_positive.{uF, uV} F T hx ha hb _ _)
        _ = _ := by
          simp only [sX, sY, adjustedOperator_irreducible, map_smul,
            LinearMap.smul_apply, smul_smul, mul_comm]

private theorem adjustedOperator_graded_rankZero_left
    (hx : BinaryProductExactnessStatement.{uF, uV} F T)
    (x : letI := T.topology; GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} 0 F.Carrier)
    (y : letI := T.topology; GradedGrothendieckGroup.{uF, uV} F T) :
    letI := T.topology
    gradedAdjustedOperator F T (gradedMultiplication F T hx (gradedInclusion F T 0 x) y) =
      gradedMultiplication F T hx (gradedInclusion F T 0 x) (gradedAdjustedOperator F T y) := by
  let := T.topology
  refine GradedAssociativityProof.rankZero_induction F T x ?_ ?_ ?_ ?_
  · simp
  · intro x x' h h'
    simp only [map_add, LinearMap.add_apply, h, h']
  · intro k x h
    simp only [map_zsmul, LinearMap.map_smul₂]
    rw [map_smul, h]
  · rw [← GradedAssociativityProof.gradedUnit_eq F T, gradedMultiplication_unit_left F T hx,
      gradedMultiplication_unit_left F T hx]

private theorem adjustedOperator_graded_rankZero_right
    (hx : BinaryProductExactnessStatement.{uF, uV} F T)
    (x : letI := T.topology; GradedGrothendieckGroup.{uF, uV} F T)
    (y : letI := T.topology; GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} 0 F.Carrier) :
    letI := T.topology
    gradedAdjustedOperator F T (gradedMultiplication F T hx x (gradedInclusion F T 0 y)) =
      gradedMultiplication F T hx (gradedAdjustedOperator F T x) (gradedInclusion F T 0 y) := by
  let := T.topology
  refine GradedAssociativityProof.rankZero_induction F T y ?_ ?_ ?_ ?_
  · simp
  · intro y y' h h'
    simp only [map_add, h, h']
  · intro k y h
    simp only [map_zsmul, h]
  · rw [← GradedAssociativityProof.gradedUnit_eq F T, gradedMultiplication_unit_right F T hx,
      gradedMultiplication_unit_right F T hx]

/-- Homogeneous normalized induction multiplication commutes with the actual
support-adjusted Aubert operator, for all ranks and all exact classes. -/
theorem adjustedHomogeneousMultiplicativity
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) :
    AdjustedHomogeneousMultiplicativityStatement.{uF, uV} F T hx := by
  let := T.topology
  intro a b x y
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · apply (show Function.Injective (gradedInclusion.{uF, uV} F T (0 + b)) from
      DirectSum.of_injective _)
    have h := adjustedOperator_graded_rankZero_left.{uF, uV} F T hx x (gradedInclusion F T b y)
    simpa only [gradedMultiplication_homogeneous, gradedAdjustedOperator_homogeneous,
      adjustedOperator_rankZero, LinearMap.id_apply] using h
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · apply (show Function.Injective (gradedInclusion.{uF, uV} F T (a + 0)) from
        DirectSum.of_injective _)
      have h := adjustedOperator_graded_rankZero_right.{uF, uV} F T hx (gradedInclusion F T a x) y
      simpa only [gradedMultiplication_homogeneous, gradedAdjustedOperator_homogeneous,
        adjustedOperator_rankZero, LinearMap.id_apply] using h
    · exact adjustedOperator_binaryProduct_positive.{uF, uV} F T hx ha hb x y

end Langlands.Aubert
