import Langlands.Representation.Aubert.SegmentGrothendieck
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof
import Langlands.Representation.Derivative.GeneralLinearDerivativeFiniteLengthProof
import Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof
import Langlands.Representation.Filtration.GrothendieckProof
import Langlands.Representation.Classification.SegmentSocleDerivativesProof
import Langlands.Representation.Aubert.GradedInductionAssociativityProof
import Langlands.Representation.Smooth.IrreducibleGrothendieckProof

/-!
# The Bernstein–Zelevinsky derivative on the actual graded exact K0

For a nontrivial unitary additive character `ψ`, every actual derivative
`π ↦ π^(k)` of `GL_n` is exact and preserves finite length, so it induces an
integer-linear map of exact K0 groups. Their sum over all orders is the total
derivative of the graded exact K0. The actual Leibniz filtration makes it
multiplicative for the actual induction product, and it fixes the actual
rank-zero unit. On a segment socle it has exactly two terms.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped BigOperators

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

open SmoothRep.FiniteLengthGrothendieckGroup

/-- The actual derivative of every order preserves finite length. -/
theorem generalLinearDerivative_preservesFiniteLength (n k : ℕ) (hk : k ≤ n) :
    letI := T.topology
    SmoothRep.PreservesFiniteLength
      (Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk) :=
  fun A hA => Derivative.generalLinearDerivativeFiniteLength.{uF, max uF uV} F T ψ n k hk A hA

/-- The actual derivative of every order preserves short exact sequences. -/
theorem generalLinearDerivative_preservesShortExact (n k : ℕ) (hk : k ≤ n) :
    letI := T.topology
    SmoothRep.PreservesFiniteLengthShortExact
      (Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk) := by
  let := T.topology
  intro A B C f g _ _ _ h
  obtain ⟨h₁, h₂, h₃⟩ := Derivative.generalLinearDerivativeExactness.{uF, max uF uV} F T ψ
    n k hk A B C f g h.1 h.2.1 h.2.2
  exact ⟨h₁, h₃, h₂⟩

/-- The order-`k` derivative on homogeneous exact K0. -/
def derivativeK0 (n k : ℕ) (hk : k ≤ n) :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} (n - k) F.Carrier :=
  letI := T.topology
  map (Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk)
    (generalLinearDerivative_preservesFiniteLength.{uF, uV} F T ψ n k hk)
    (generalLinearDerivative_preservesShortExact.{uF, uV} F T ψ n k hk)

theorem derivativeK0_ofObject (n k : ℕ) (hk : k ≤ n) :
    letI := T.topology
    ∀ A : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
      derivativeK0 F T ψ n k hk (ofObject A) =
        ofRepresentation ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk).obj
          A.val) (generalLinearDerivative_preservesFiniteLength.{uF, uV} F T ψ n k hk A.val
            A.property) := by
  let := T.topology
  intro A
  exact map_ofObject _ _ _ A

theorem derivativeK0_ofRepresentation (n k : ℕ) (hk : k ≤ n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (hA : A.HasFiniteLength),
      derivativeK0 F T ψ n k hk (ofRepresentation A hA) =
        ofRepresentation ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk).obj A)
          (generalLinearDerivative_preservesFiniteLength.{uF, uV} F T ψ n k hk A hA) := by
  let := T.topology
  intro A hA
  exact derivativeK0_ofObject F T ψ n k hk ⟨A, hA⟩

/-- The zeroth derivative is the identity of exact K0. -/
theorem derivativeK0_zero (n : ℕ) (h : 0 ≤ n) :
    letI := T.topology
    derivativeK0.{uF, uV} F T ψ n 0 h = LinearMap.id := by
  let := T.topology
  apply hom_ext_object
  intro A
  rw [derivativeK0_ofObject]
  rfl

/-- The order-`k` part of the total derivative of a rank-`n` class, placed in
rank `n - k`; it is zero when `k > n`. -/
def derivativeComponent (n k : ℕ) :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
      GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  if hk : k ≤ n then (gradedInclusion F T (n - k)).comp (derivativeK0 F T ψ n k hk) else 0

theorem derivativeComponent_of_le {n k : ℕ} (hk : k ≤ n) :
    letI := T.topology
    ∀ x, derivativeComponent.{uF, uV} F T ψ n k x =
      gradedInclusion F T (n - k) (derivativeK0 F T ψ n k hk x) := by
  let := T.topology
  intro x
  simp only [derivativeComponent, hk, ↓reduceDIte, LinearMap.comp_apply]

theorem derivativeComponent_of_lt {n k : ℕ} (hk : n < k) :
    letI := T.topology
    derivativeComponent.{uF, uV} F T ψ n k = 0 := by
  let := T.topology
  simp only [derivativeComponent, Nat.not_le.mpr hk, ↓reduceDIte]

/-- The total Bernstein–Zelevinsky derivative of the graded exact K0: the sum of
the derivatives of all orders `0 ≤ k ≤ n` on rank `n`. -/
def gradedDerivative :
    letI := T.topology
    GradedGrothendieckGroup.{uF, uV} F T →ₗ[ℤ] GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  DirectSum.toModule ℤ ℕ _ fun n => ∑ k ∈ Finset.range (n + 1), derivativeComponent F T ψ n k

theorem gradedDerivative_homogeneous (n : ℕ) :
    letI := T.topology
    ∀ x, gradedDerivative.{uF, uV} F T ψ (gradedInclusion F T n x) =
      ∑ k ∈ Finset.range (n + 1), derivativeComponent F T ψ n k x := by
  let := T.topology
  intro x
  simp only [gradedDerivative, gradedInclusion, DirectSum.toModule_lof, LinearMap.sum_apply]

/-- The total derivative of an actual finite-length representation of `GL_n` is the
sum of the classes of its derivatives of all orders `k ≤ n`, placed in rank `n - k`. -/
theorem gradedDerivative_ofRepresentation (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (hA : A.HasFiniteLength),
      gradedDerivative F T ψ (gradedInclusion F T n (ofRepresentation A hA)) =
        ∑ k : Fin (n + 1), gradedInclusion F T (n - k)
          (ofRepresentation ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k
              (Nat.lt_succ_iff.mp k.isLt)).obj A)
            (generalLinearDerivative_preservesFiniteLength.{uF, uV} F T ψ n k
              (Nat.lt_succ_iff.mp k.isLt) A hA)) := by
  let := T.topology
  intro A hA
  rw [gradedDerivative_homogeneous, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [derivativeComponent_of_le F T ψ (Nat.lt_succ_iff.mp k.isLt), derivativeK0_ofRepresentation]

/-- Derivative rank transport does not change homogeneous graded classes, for any
finite-length proof of the transported object. -/
theorem gradedInclusion_generalLinearRankCast {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (hA : A.HasFiniteLength)
      (hA' : ((Derivative.generalLinearRankCast.{uF, max uF uV} T h).obj A).HasFiniteLength),
      gradedInclusion F T b
          (ofRepresentation ((Derivative.generalLinearRankCast.{uF, max uF uV} T h).obj A) hA') =
        gradedInclusion F T a (ofRepresentation A hA) := by
  let := T.topology
  subst h
  intro A hA hA'
  rfl

/-- Classification rank transport does not change homogeneous graded classes. -/
theorem gradedInclusion_castRank {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (hA : A.HasFiniteLength) (hA' : (T.castRank h A).HasFiniteLength),
      gradedInclusion F T b (ofRepresentation (T.castRank h A) hA') =
        gradedInclusion F T a (ofRepresentation A hA) := by
  let := T.topology
  subst h
  intro A hA hA'
  rfl

/-- One Leibniz grade: derivative of each factor, product and rank cast. -/
def leibnizPieceFunctor (a b d : ℕ) (x : Derivative.LeibnizIndex a b d) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((a + b) - d) F.Carrier) :=
  letI := T.topology
  (Derivative.generalLinearDerivative.{uF, max uF uV} T ψ a x.val.1
      (Derivative.leibnizIndices_left_le x.property)).prod
      (Derivative.generalLinearDerivative.{uF, max uF uV} T ψ b x.val.2
        (Derivative.leibnizIndices_right_le x.property)) ⋙
    T.binaryNormalizedProductFunctor.{uF, max uF uV} (a - x.val.1) (b - x.val.2) ⋙
    Derivative.generalLinearRankCast.{uF, max uF uV} T
      (Derivative.leibnizIndices_rank x.property)

/-- The class of one Leibniz piece is the product of the two derivative components. -/
theorem leibnizPiece_class (hx : BinaryProductExactnessStatement.{uF, uV} F T) (a b d : ℕ)
    (x : Derivative.LeibnizIndex a b d) :
    letI := T.topology
    ∀ (A : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
      (h : ((leibnizPieceFunctor F T ψ a b d x).obj (A.val, B.val)).HasFiniteLength),
      gradedInclusion F T ((a + b) - d)
          (ofRepresentation ((leibnizPieceFunctor F T ψ a b d x).obj (A.val, B.val)) h) =
        gradedMultiplication F T hx (derivativeComponent F T ψ a x.val.1 (ofObject A))
          (derivativeComponent F T ψ b x.val.2 (ofObject B)) := by
  let := T.topology
  intro A B h
  obtain ⟨⟨i, j⟩, hij⟩ := x
  have hi : i ≤ a := Derivative.leibnizIndices_left_le hij
  have hj : j ≤ b := Derivative.leibnizIndices_right_le hij
  rw [derivativeComponent_of_le F T ψ hi, derivativeComponent_of_le F T ψ hj,
    derivativeK0_ofObject, derivativeK0_ofObject, gradedMultiplication_homogeneous]
  have hA := generalLinearDerivative_preservesFiniteLength.{uF, uV} F T ψ a i hi A.val A.property
  have hB := generalLinearDerivative_preservesFiniteLength.{uF, uV} F T ψ b j hj B.val B.property
  exact (gradedInclusion_generalLinearRankCast F T (Derivative.leibnizIndices_rank hij) _ _ h).trans
    (congrArg (gradedInclusion F T _)
      (binaryProductK0_classes F T hx (a - i) (b - j) ⟨_, hA⟩ ⟨_, hB⟩).symm)

/-- The K0 Leibniz formula for one derivative order of an actual product. -/
theorem derivativeComponent_binaryProduct
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) (a b d : ℕ) (hd : d ≤ a + b) :
    letI := T.topology
    ∀ (A : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)),
      derivativeComponent F T ψ (a + b) d (binaryProductK0 F T hx a b (ofObject A) (ofObject B)) =
        ∑ x ∈ Derivative.leibnizIndices a b d,
          gradedMultiplication F T hx (derivativeComponent F T ψ a x.1 (ofObject A))
            (derivativeComponent F T ψ b x.2 (ofObject B)) := by
  let := T.topology
  intro A B
  rw [binaryProductK0_classes, derivativeComponent_of_le F T ψ hd]
  obtain ⟨e, hglue⟩ :=
    Derivative.generalLinearDerivativeLeibnizFiltration.{uF, max uF uV} F T ψ a b d hd
  have hP := SmoothRep.filtrationGrothendieckStatement ℂ (GeneralLinear ((a + b) - d) F.Carrier)
    _ (T.binaryNormalizedProductFunctor.{uF, max uF uV} a b ⋙
      Derivative.generalLinearDerivative.{uF, max uF uV} T ψ (a + b) d hd)
    _ (fun i => leibnizPieceFunctor F T ψ a b d (e.symm i)) hglue (A.val, B.val)
    (generalLinearDerivative_preservesFiniteLength.{uF, uV} F T ψ (a + b) d hd _
      (binaryProduct_preservesFiniteLength F T a b _ _ A.property B.property))
  obtain ⟨hP, hsum⟩ := hP
  have hl : derivativeK0 F T ψ (a + b) d hd
      (ofRepresentation ((T.binaryNormalizedProductFunctor.{uF, max uF uV} a b).obj
        (A.val, B.val)) (binaryProduct_preservesFiniteLength F T a b _ _ A.property
          B.property)) =
      ofRepresentation ((T.binaryNormalizedProductFunctor.{uF, max uF uV} a b ⋙
        Derivative.generalLinearDerivative.{uF, max uF uV} T ψ (a + b) d hd).obj
          (A.val, B.val))
        (generalLinearDerivative_preservesFiniteLength.{uF, uV} F T ψ (a + b) d hd _
          (binaryProduct_preservesFiniteLength F T a b _ _ A.property B.property)) :=
    derivativeK0_ofObject F T ψ (a + b) d hd ⟨_, _⟩
  rw [hl, hsum, map_sum, ← Finset.sum_coe_sort (Derivative.leibnizIndices a b d)]
  exact Fintype.sum_equiv e.symm _ _
    (fun i => leibnizPiece_class F T ψ hx a b d (e.symm i) A B (hP i))

/-- Summing the Leibniz index sets over all orders gives the full rectangle. -/
theorem sum_range_leibnizIndices {M : Type*} [AddCommMonoid M] (a b : ℕ) (f : ℕ × ℕ → M) :
    ∑ d ∈ Finset.range (a + b + 1), ∑ x ∈ Derivative.leibnizIndices a b d, f x =
      ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), f (i, j) := by
  rw [← Finset.sum_product, ← Finset.sum_fiberwise_of_maps_to
    (g := fun x : ℕ × ℕ => x.1 + x.2) (t := Finset.range (a + b + 1))]
  · refine Finset.sum_congr rfl fun d _ => Finset.sum_congr ?_ fun _ _ => rfl
    ext ⟨i, j⟩
    simp only [Derivative.mem_leibnizIndices, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range]
    omega
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h ⊢
    omega

/-- The total derivative is multiplicative on homogeneous classes. -/
theorem gradedDerivative_mul_homogeneous
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) (a b : ℕ) :
    letI := T.topology
    ∀ x y, gradedDerivative F T ψ
        (gradedMultiplication F T hx (gradedInclusion F T a x) (gradedInclusion F T b y)) =
      gradedMultiplication F T hx (gradedDerivative F T ψ (gradedInclusion F T a x))
        (gradedDerivative F T ψ (gradedInclusion F T b y)) := by
  let := T.topology
  intro x y
  refine GradedAssociativityProof.induction_on x ?_ ?_ ?_ ?_
  · simp only [map_zero, LinearMap.zero_apply]
  · intro x x' h h'
    simp only [map_add, LinearMap.add_apply, h, h']
  · intro k x h
    simp only [map_zsmul, LinearMap.map_smul₂]
    rw [map_smul, h]
  intro A
  refine GradedAssociativityProof.induction_on y ?_ ?_ ?_ ?_
  · simp only [map_zero]
  · intro y y' h h'
    simp only [map_add, h, h']
  · intro k y h
    simp only [map_zsmul, h]
  intro B
  rw [gradedMultiplication_homogeneous, gradedDerivative_homogeneous,
    gradedDerivative_homogeneous, gradedDerivative_homogeneous]
  rw [Finset.sum_congr rfl fun d hd => derivativeComponent_binaryProduct F T ψ hx a b d
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)) A B]
  rw [sum_range_leibnizIndices]
  simp only [map_sum, LinearMap.sum_apply]
  exact Finset.sum_comm

/-- The total derivative is multiplicative for the actual induction product. -/
theorem gradedDerivative_mul (hx : BinaryProductExactnessStatement.{uF, uV} F T) :
    letI := T.topology
    ∀ x y, gradedDerivative F T ψ (gradedMultiplication F T hx x y) =
      gradedMultiplication F T hx (gradedDerivative F T ψ x) (gradedDerivative F T ψ y) := by
  let := T.topology
  intro x y
  refine GradedAssociativityProof.graded_induction F T x ?_ ?_ ?_
  · simp only [map_zero, LinearMap.zero_apply]
  · intro x x' h h'
    simp only [map_add, LinearMap.add_apply, h, h']
  intro a x
  refine GradedAssociativityProof.graded_induction F T y ?_ ?_ ?_
  · simp only [map_zero]
  · intro y y' h h'
    simp only [map_add, h, h']
  intro b y
  exact gradedDerivative_mul_homogeneous F T ψ hx a b x y

/-- The total derivative fixes the actual rank-zero unit. -/
theorem gradedDerivative_unit :
    letI := T.topology
    gradedDerivative.{uF, uV} F T ψ (gradedUnit F T) = gradedUnit F T := by
  let := T.topology
  rw [gradedUnit, gradedDerivative_homogeneous, Finset.sum_range_one,
    derivativeComponent_of_le F T ψ le_rfl, derivativeK0_zero]
  rfl

/-- Once the induction ring laws hold, the total derivative is a ring endomorphism
of the actual graded exact K0. -/
def gradedDerivativeRingHom (hx : BinaryProductExactnessStatement.{uF, uV} F T)
    (hl : GradedInductionRingLawsStatement F T hx) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    GradedGrothendieckGroup.{uF, uV} F T →+* GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  { toFun := gradedDerivative F T ψ
    map_one' := gradedDerivative_unit F T ψ
    map_mul' := gradedDerivative_mul F T ψ hx
    map_zero' := map_zero _
    map_add' := map_add _ }

theorem gradedDerivativeRingHom_apply (hx : BinaryProductExactnessStatement.{uF, uV} F T)
    (hl : GradedInductionRingLawsStatement F T hx) :
    letI := T.topology
    ∀ x, gradedDerivativeRingHom F T ψ hx hl x = gradedDerivative F T ψ x := fun _ => rfl

/-- A line of `GL_0`, placed in rank zero, is the actual graded unit. -/
theorem gradedInclusion_eq_gradedUnit {m : ℕ} (hm : m = 0) :
    letI := T.topology
    ∀ (V : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
      (hV : V.HasFiniteLength), Module.finrank ℂ V = 1 →
      gradedInclusion F T m (ofRepresentation V hV) = gradedUnit.{uF, uV} F T := by
  let := T.topology
  subst hm
  intro V hV h1
  have : Subsingleton (GeneralLinear 0 F.Carrier) := GeneralLinear.subsingleton_of_rank_eq_zero rfl
  have : FiniteDimensional ℂ (T.binaryProductUnit.{uF, max uF uV}) := by
    change FiniteDimensional ℂ (ULift.{max uF uV} ℂ)
    infer_instance
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_pos (by omega)
  let e : T.binaryProductUnit.{uF, max uF uV} ≃ₗ[ℂ] V :=
    LinearEquiv.ofFinrankEq _ _ ((T.finrank_binaryProductUnit.{uF, max uF uV}).trans h1.symm)
  let e' : (T.binaryProductUnit.{uF, max uF uV}).representation.Equiv V.representation :=
    Representation.Equiv.mk e fun g => by
      rw [Subsingleton.elim g 1, map_one, map_one]
      rfl
  rw [gradedUnit]
  exact congrArg (gradedInclusion F T 0)
    (ofRepresentation_eq_of_equiv hV (binaryProductUnit_hasFiniteLength F T) e'.symm)

/-- Positive derivatives of a segment socle of order other than the cuspidal rank
have zero class. -/
theorem derivativeComponent_segmentSocle_eq_zero (Δ : T.Segment.{max uF uV, uF}) (k : ℕ)
    (hk : k ≤ Δ.degree) (hpos : 0 < k) (hne : k ≠ Δ.rank) :
    letI := T.topology
    derivativeComponent F T ψ Δ.degree k (segmentSocleClass F T Δ) = 0 := by
  let := T.topology
  have hs := (Classification.segmentSocleDerivatives.{uF, max uF uV} F T ψ Δ
    (segmentSocleObject F T Δ) (segmentSocleObject_spec F T Δ)).1 k hk hpos hne
  rw [segmentSocleClass, GeneralLinear.finiteLengthClass, derivativeComponent_of_le F T ψ hk,
    derivativeK0_ofRepresentation,
    SmoothRep.IrreducibleGrothendieckProof.ofRepresentation_eq_zero_of_subsingleton, map_zero]

/-- The total derivative of a segment socle of length one: `Z(ρ) ↦ Z(ρ) + 1`. -/
theorem gradedDerivative_segmentSocle_of_length_eq_one (Δ : T.Segment.{max uF uV, uF})
    (h : Δ.length = 1) :
    letI := T.topology
    gradedDerivative F T ψ (gradedSegmentSocle F T Δ) =
      gradedSegmentSocle F T Δ + gradedUnit.{uF, uV} F T := by
  let := T.topology
  have hr : Δ.rank ≤ Δ.degree := by
    rw [show Δ.degree = Δ.length * Δ.rank from rfl, h, one_mul]
  rw [gradedSegmentSocle, gradedDerivative_homogeneous,
    Finset.sum_eq_add_of_mem 0 Δ.rank (by simp) (by simpa [Nat.lt_succ_iff] using hr)
      (Nat.ne_of_lt Δ.rank_pos) (fun c hc hne => derivativeComponent_segmentSocle_eq_zero
        F T ψ Δ c (Nat.lt_succ_iff.mp (Finset.mem_range.mp hc))
        (Nat.pos_of_ne_zero hne.1) hne.2)]
  congr 1
  · rw [derivativeComponent_of_le F T ψ (Nat.zero_le _), derivativeK0_zero]
    rfl
  · rw [derivativeComponent_of_le F T ψ hr, segmentSocleClass, GeneralLinear.finiteLengthClass,
      derivativeK0_ofRepresentation]
    refine gradedInclusion_eq_gradedUnit F T
      (by rw [show Δ.degree = Δ.length * Δ.rank from rfl, h, one_mul, Nat.sub_self]) _ _ ?_
    exact (Classification.segmentSocleDerivatives.{uF, max uF uV} F T ψ Δ
      (segmentSocleObject F T Δ) (segmentSocleObject_spec F T Δ)).2.1 hr h

/-- The total derivative of a segment socle of length at least two:
`Z([ρ, ν^(m-1) ρ]) ↦ Z([ρ, ν^(m-1) ρ]) + Z([ρ, ν^(m-2) ρ])`. -/
theorem gradedDerivative_segmentSocle_of_two_le (Δ : T.Segment.{max uF uV, uF})
    (h : 2 ≤ Δ.length) :
    letI := T.topology
    gradedDerivative F T ψ (gradedSegmentSocle F T Δ) =
      gradedSegmentSocle F T Δ +
        gradedSegmentSocle F T ⟨Δ.base, Δ.length - 1, by omega⟩ := by
  let := T.topology
  have hr : Δ.rank ≤ Δ.degree := Nat.le_mul_of_pos_left _ Δ.length_pos
  have hdeg : Δ.degree - Δ.rank = (Δ.length - 1) * Δ.rank := by
    rw [show Δ.degree = Δ.length * Δ.rank from rfl, Nat.sub_one_mul]
  rw [gradedSegmentSocle, gradedDerivative_homogeneous,
    Finset.sum_eq_add_of_mem 0 Δ.rank (by simp) (by simpa [Nat.lt_succ_iff] using hr)
      (Nat.ne_of_lt Δ.rank_pos) (fun c hc hne => derivativeComponent_segmentSocle_eq_zero
        F T ψ Δ c (Nat.lt_succ_iff.mp (Finset.mem_range.mp hc))
        (Nat.pos_of_ne_zero hne.1) hne.2)]
  congr 1
  · rw [derivativeComponent_of_le F T ψ (Nat.zero_le _), derivativeK0_zero]
    rfl
  · rw [derivativeComponent_of_le F T ψ hr, segmentSocleClass, GeneralLinear.finiteLengthClass,
      derivativeK0_ofRepresentation]
    have hsoc := (Classification.segmentSocleDerivatives.{uF, max uF uV} F T ψ Δ
      (segmentSocleObject F T Δ) (segmentSocleObject_spec F T Δ)).2.2 hr h hdeg
    have hfl := generalLinearDerivative_preservesFiniteLength.{uF, uV} F T ψ Δ.degree Δ.rank hr
      (segmentSocleObject F T Δ) (segmentSocleObject_hasFiniteLength F T Δ)
    have hfl' : (T.castRank hdeg ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ
        Δ.degree Δ.rank hr).obj (segmentSocleObject F T Δ))).HasFiniteLength := by
      obtain ⟨_, _, hirr⟩ := hsoc
      exact SmoothRep.hasFiniteLength_of_isIrreducible hirr.1
    rw [gradedSegmentSocle, segmentSocleClass_of_object F T _ _ hfl' hsoc,
      GeneralLinear.finiteLengthClass]
    exact (gradedInclusion_castRank F T hdeg _ hfl hfl').symm

end Langlands.Aubert
