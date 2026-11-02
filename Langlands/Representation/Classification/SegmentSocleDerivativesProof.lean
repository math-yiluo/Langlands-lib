import Langlands.Representation.Classification.SegmentSocleDerivativesStatement
import Langlands.Representation.Classification.SegmentSocleJacquetProof
import Langlands.Representation.Classification.SupercuspidalDerivativesProof
import Langlands.Representation.Classification.TwoSupercuspidalPartialDerivatives
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof
import Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof
import Langlands.Representation.Derivative.ZeroRankTensor
import Langlands.Representation.Derivative.LevelCalculus
import Langlands.Representation.Parabolic.NaturalFirstAdjointness
import Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftProof
import Langlands.Representation.Classification.TwoSupercuspidalProductStructureProof
import Langlands.Representation.Classification.TwoSupercuspidalDerivativeBridge
import Langlands.Representation.Derivative.OrderedCuspidalProductTwistOne
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Derivatives of segment socles (Zelevinsky 1980, Theorem 3.5)

The derivatives of a segment socle `⟨Δ⟩`, from the two-block Jacquet formula of
Proposition 3.4, the Jacquet description of derivatives in Proposition 3.7, and the
vanishing of the top derivative of a socle of a segment of length at least two
(Lemma 3.9).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Classification

open GeneralLinear Derivative

universe uF uV uW

namespace SegmentSocleDerivativesProof

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-! ## Rank and order transports -/

section Casts

variable (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

theorem subsingleton_rankCast_iff {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier),
      Subsingleton ((generalLinearRankCast T h).obj X) ↔ Subsingleton X := by
  subst h
  intro X
  exact Iff.rfl

theorem subsingleton_derivative_order_iff {N k k' : ℕ} (hk : k ≤ N) (hk' : k' ≤ N)
    (h : k = k') :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uW} ℂ (GeneralLinear N F.Carrier),
      Subsingleton ((generalLinearDerivative T ψ N k hk).obj X) ↔
        Subsingleton ((generalLinearDerivative T ψ N k' hk').obj X) := by
  subst h
  intro X
  exact Iff.rfl

theorem subsingleton_topDerivative_iff (b : ℕ) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uW} ℂ (GeneralLinear b F.Carrier),
      Subsingleton ((topDerivative T ψ b).obj X) ↔
        Subsingleton ((generalLinearDerivative T ψ b b le_rfl).obj X) := by
  intro X
  exact subsingleton_rankCast_iff T (Nat.sub_self b) _

/-- A tensor product with a zero factor is zero. -/
theorem tensor_subsingleton {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [Subsingleton W] : Subsingleton (V ⊗[ℂ] W) := by
  have h : ∀ z : V ⊗[ℂ] W, z = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul v w => rw [Subsingleton.elim w 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => by rw [h x, h y]⟩

end Casts

/-! ## Derivatives from two-block Jacquet modules (Ze80 3.7) -/

section TwoBlock

variable (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- A zero two-block Jacquet module along `(a, b)` gives a zero derivative of order `b`. -/
theorem subsingleton_derivative_of_jacquet {N a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : a + b = N) (hbN : b ≤ N) :
    letI := T.topology
    ∀ π : SmoothRep.{0, uF, uW} ℂ (GeneralLinear N F.Carrier),
      Subsingleton ((T.normalizedJacquetFunctor (BlockShape.ofPair a b ha hb h)).obj π) →
        Subsingleton ((generalLinearDerivative T ψ N b hbN).obj π) := by
  subst h
  let _ := T.topology
  intro π hJ
  obtain ⟨cJ⟩ := partialDerivativeJacquetComparison F T ψ a b ha hb
  have hP : Subsingleton ((partialDerivative T ψ a b).obj
      ((positiveTwoBlockNormalizedJacquet T a b ha hb).obj π)) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨u, rfl⟩ := partialDerivativeMk_surjective T ψ a b _ x
    obtain ⟨v, rfl⟩ := partialDerivativeMk_surjective T ψ a b _ y
    have huv : u = v := @Subsingleton.elim _ hJ u v
    rw [huv]
  have h1 := (LevelCalculus.subsingleton_iff_of_iso (cJ.app π)).mpr hP
  exact (subsingleton_rankCast_iff T (Nat.add_sub_cancel a b) _).mp h1

/-- Ze80 3.7(b) and 3.7(a): an external tensor product `A ⊗ B` as two-block Jacquet
module along `(a, b)` gives the derivative of order `b` as `A ⊗ B^(b)`. -/
theorem nonempty_derivative_equiv {N a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = N)
    (hbN : b ≤ N) (hcast : N - b = a) :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, uW} ℂ (GeneralLinear N F.Carrier))
      (A : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0, uF, uW} ℂ (GeneralLinear b F.Carrier)),
      Nonempty ((T.normalizedJacquetFunctor (BlockShape.ofPair a b ha hb h)).obj π ≅
        FiniteTensor.externalFunctor.obj (twoBlockFactors ha hb A B)) →
      Nonempty (((generalLinearRankCast T hcast).obj
          ((generalLinearDerivative T ψ N b hbN).obj π)).representation.Equiv
        ((firstFactorTopDerivative T ψ a b).obj (A, B)).representation) := by
  subst h
  let _ := T.topology
  intro π A B ⟨e⟩
  obtain ⟨eT⟩ := TwoSupercuspidalPartialDerivatives.nonempty_twoBlockTensor_equiv T ha hb A B
  let eJ := SmoothRep.equivOfIso e
  let eP : ((positiveTwoBlockNormalizedJacquet T a b ha hb).obj π).representation.Equiv
      ((Mirabolic.continuousPullbackFunctor (R := ℂ)
          (Shahidi.twoBlockLeviContinuousEquiv ha hb F.Carrier).symm.toMonoidHom
          (Shahidi.twoBlockLeviContinuousEquiv ha hb F.Carrier).symm.continuous).obj
        (FiniteTensor.externalSmoothObject (twoBlockFactors ha hb A B))).representation :=
    Representation.Equiv.mk eJ.toLinearEquiv
      (fun g => eJ.isIntertwining'
        ((Shahidi.twoBlockLeviContinuousEquiv ha hb F.Carrier).symm g))
  obtain ⟨eD⟩ := TwoSupercuspidalPartialDerivatives.nonempty_partialDerivative_equiv
    T ψ a b _ _ ⟨eP.trans eT⟩
  obtain ⟨cJ⟩ := partialDerivativeJacquetComparison F T ψ a b ha hb
  obtain ⟨cT⟩ := partialDerivativeTensor F T ψ a b
  exact ⟨((SmoothRep.equivOfIso (cJ.app π)).trans eD).trans
    (SmoothRep.equivOfIso (cT.app (A, B)))⟩

/-- If the second factor has zero top derivative, the derivative is zero. -/
theorem subsingleton_derivative_of_jacquet_tensor {N a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : a + b = N) (hbN : b ≤ N) :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, uW} ℂ (GeneralLinear N F.Carrier))
      (A : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0, uF, uW} ℂ (GeneralLinear b F.Carrier)),
      Nonempty ((T.normalizedJacquetFunctor (BlockShape.ofPair a b ha hb h)).obj π ≅
        FiniteTensor.externalFunctor.obj (twoBlockFactors ha hb A B)) →
      Subsingleton ((generalLinearDerivative T ψ b b le_rfl).obj B) →
        Subsingleton ((generalLinearDerivative T ψ N b hbN).obj π) := by
  let _ := T.topology
  intro π A B hJ hB
  have hcast : N - b = a := by omega
  obtain ⟨e⟩ := nonempty_derivative_equiv T ψ ha hb h hbN hcast π A B hJ
  have hD : Subsingleton ((topDerivative T ψ b).obj B) :=
    (subsingleton_topDerivative_iff T ψ b B).mpr hB
  have hX : Subsingleton ((firstFactorTopDerivative T ψ a b).obj (A, B)) :=
    tensor_subsingleton (V := A) (W := (topDerivative T ψ b).obj B)
  have hY : Subsingleton ((generalLinearRankCast T hcast).obj
      ((generalLinearDerivative T ψ N b hbN).obj π)) :=
    ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩
  exact (subsingleton_rankCast_iff T hcast _).mp hY

/-- If the second factor has a one-dimensional top derivative, the derivative is the
first factor. -/
theorem nonempty_derivative_equiv_first {N a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : a + b = N) (hbN : b ≤ N) (hcast : N - b = a) :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, uW} ℂ (GeneralLinear N F.Carrier))
      (A : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0, uF, uW} ℂ (GeneralLinear b F.Carrier)),
      Nonempty ((T.normalizedJacquetFunctor (BlockShape.ofPair a b ha hb h)).obj π ≅
        FiniteTensor.externalFunctor.obj (twoBlockFactors ha hb A B)) →
      Module.finrank ℂ ((topDerivative T ψ b).obj B) = 1 →
        Nonempty (((generalLinearRankCast T hcast).obj
          ((generalLinearDerivative T ψ N b hbN).obj π)).representation.Equiv
            A.representation) := by
  let _ := T.topology
  intro π A B hJ hB
  obtain ⟨e⟩ := nonempty_derivative_equiv T ψ ha hb h hbN hcast π A B hJ
  obtain ⟨eF⟩ := TwoSupercuspidalPartialDerivatives.nonempty_firstFactor_equiv
    A.representation ((topDerivative T ψ b).obj B) hB
  exact ⟨e.trans eF⟩

end TwoBlock


/-! ## The top derivative of a binary product (BZ77 4.14(c), top grade) -/

section TopProduct

/-- The only graded piece of a length-one filtration is linearly equivalent to the source. -/
theorem nonempty_graded_equiv_of_length_one {C : Type*} [Category C] {G : Type*} [Monoid G]
    {Φ : C ⥤ Rep.{uW} ℂ G} {n : ℕ} (s : RepFunctorFiltration Φ n) (hn : n = 1) (i : Fin n)
    (X : C) : Nonempty ((s.graded i).obj X ≃ₗ[ℂ] Φ.obj X) := by
  subst hn
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have h0 : ((s.step (0 : Fin 1).castSucc).obj X).toSubmodule = ⊥ := by
    rw [show (s.step (0 : Fin 1).castSucc).obj X = ⊥ from s.zero X]
    rfl
  have h1 : ((s.step (0 : Fin 1).succ).obj X).toSubmodule = ⊤ := by
    rw [show (s.step (0 : Fin 1).succ).obj X = ⊤ from s.top X]
    rfl
  have hp : ((s.step (0 : Fin 1).castSucc).obj X).toSubmodule.comap
      ((s.step (0 : Fin 1).succ).obj X).toSubmodule.subtype = ⊥ := by
    rw [h0, Submodule.comap_bot, Submodule.ker_subtype]
  exact ⟨(Submodule.quotEquivOfEqBot _ hp).trans
    ((LinearEquiv.ofEq _ _ h1).trans Submodule.topEquiv)⟩

variable (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- A binary product whose second factor has rank zero is the tensor product of its
factors. -/
theorem nonempty_binaryProduct_rank_zero_equiv {a c : ℕ} (hc : c = 0) :
    letI := T.topology
    ∀ (X : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier))
      (Y : SmoothRep.{0, uF, uW} ℂ (GeneralLinear c F.Carrier)),
      Nonempty (((T.binaryNormalizedProductFunctor a c).obj (X, Y)) ≃ₗ[ℂ] (X ⊗[ℂ] Y)) := by
  subst hc
  let _ := T.topology
  intro X Y
  exact ⟨(ZeroRankTensor.binaryRightZeroEquiv T a (X, Y)).toLinearEquiv.trans
      (TensorProduct.congr (LinearEquiv.refl ℂ X) ULift.moduleEquiv)⟩

/-- The top derivative of a binary product vanishes when the top derivative of its
second factor vanishes: the top-order Leibniz filtration has the single grade
`D^(a) × P^(b)`. -/
theorem subsingleton_top_binaryProduct (a b : ℕ) :
    letI := T.topology
    ∀ (D : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier))
      (P : SmoothRep.{0, uF, uW} ℂ (GeneralLinear b F.Carrier)),
      Subsingleton ((generalLinearDerivative T ψ b b le_rfl).obj P) →
      Subsingleton ((generalLinearDerivative T ψ (a + b) (a + b) le_rfl).obj
          ((T.binaryNormalizedProductFunctor a b).obj (D, P))) := by
  let _ := T.topology
  intro D P hP
  obtain ⟨e, s, hs⟩ := GeneralLinearDerivativeLeibnizFiltrationStatement.filtration T
    (generalLinearDerivativeLeibnizFiltration.{uF, uW} F T) ψ a b (a + b) le_rfl
  have hcard : (leibnizIndices a b (a + b)).card = 1 := by
    rw [leibnizIndices_top, Finset.card_singleton]
  have hpiece : ∀ y : LeibnizIndex a b (a + b),
      Subsingleton ((leibnizPiece T ψ a b (a + b) y).obj (D, P)) := by
    intro y
    have hy := mem_leibnizIndices.mp y.property
    have h1 : y.val.2 = b := by omega
    have h2 : b - y.val.2 = 0 := by omega
    rw [leibnizPiece_obj]
    refine (subsingleton_rankCast_iff T _ _).mpr ?_
    obtain ⟨f⟩ := nonempty_binaryProduct_rank_zero_equiv T h2
      ((generalLinearDerivative T ψ a y.val.1 (leibnizIndices_left_le y.property)).obj D)
      ((generalLinearDerivative T ψ b y.val.2 (leibnizIndices_right_le y.property)).obj P)
    have : Subsingleton ((generalLinearDerivative T ψ b y.val.2
        (leibnizIndices_right_le y.property)).obj P) :=
      (subsingleton_derivative_order_iff T ψ _ _ h1 P).mpr hP
    have := tensor_subsingleton
      (V := (generalLinearDerivative T ψ a y.val.1 (leibnizIndices_left_le y.property)).obj D)
      (W := (generalLinearDerivative T ψ b y.val.2 (leibnizIndices_right_le y.property)).obj P)
    exact f.toEquiv.subsingleton
  let i : Fin (leibnizIndices a b (a + b)).card := e ⟨(a, b), by simp⟩
  obtain ⟨φ⟩ := hs i
  obtain ⟨g⟩ := nonempty_graded_equiv_of_length_one s hcard i (D, P)
  have := hpiece (e.symm i)
  have : Subsingleton ((s.graded i).obj (D, P)) :=
    (Representation.equivOfIso (φ.app (D, P))).toLinearEquiv.toEquiv.subsingleton
  exact g.symm.toEquiv.subsingleton

end TopProduct

/-! ## Embedding by Frobenius reciprocity -/

section Embedding

/-- A finite indexed tensor product of nonzero complex vector spaces is nonzero. -/
theorem nontrivial_piTensorProduct {κ : Type*} [Finite κ] {E : κ → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] (hE : ∀ i, Nontrivial (E i)) :
    Nontrivial (PiTensorProduct ℂ E) := by
  let b := fun i => Module.Basis.ofVectorSpace ℂ (E i)
  let q := fun i => Classical.choice (b i).index_nonempty
  exact ⟨⟨Basis.piTensorProduct b q, 0, (Basis.piTensorProduct b).ne_zero q⟩⟩

theorem nontrivial_of_isIrreducible {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : Representation.IsIrreducible ρ) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  apply h.bot_ne_top
  ext v
  simp [Subsingleton.elim v 0]

variable (T : F.TopologicalData)


/-- Frobenius reciprocity: an irreducible `π` with a nonzero Levi representation `σ`
equivalent to its Jacquet module along `B` embeds in the normalized induction of `σ`. -/
theorem exists_injective_of_jacquet_equiv {n : ℕ} (B : BlockShape n) {X : Type*}
    [AddCommGroup X] [Module ℂ X] [Nontrivial X]
    (σ : Representation ℂ (B.Levi F.Carrier) X) :
    letI := T.topology
    ∀ π : SmoothRep.{0, uF, uW} ℂ (GeneralLinear n F.Carrier),
      π.IsIrreducible → (T.normalizedJacquet B π.representation).Equiv σ →
      ∃ f : π.representation.IntertwiningMap (T.normalizedParabolicInduced B σ),
        Function.Injective f := by
  let _ := T.topology
  intro π hπ e
  let A : (T.normalizedJacquet B π.representation).IntertwiningMap σ := e.toIntertwiningMap
  let f := (Parabolic.FirstAdjointness.equiv T B π.isSmooth).symm A
  refine ⟨f, ?_⟩
  have := hπ
  rcases Representation.IsIrreducible.injective_or_eq_zero f with hf | hf
  · exact hf
  · exfalso
    have hA : A = 0 := by
      have h1 := congrArg (Parabolic.FirstAdjointness.equiv T B π.isSmooth) hf
      rw [map_zero, LinearEquiv.apply_symm_apply] at h1
      exact h1
    obtain ⟨y, hy⟩ := exists_ne (0 : X)
    apply hy
    rw [← e.apply_symm_apply y]
    change A (e.symm y) = 0
    rw [hA]
    rfl

/-- Frobenius reciprocity: an irreducible representation whose Jacquet module along `B`
is isomorphic to a nonzero `⊗ σ_i` embeds in the normalized product of the `σ_i`. -/
theorem exists_injective_of_jacquet_iso {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, uW} ℂ (GeneralLinear n F.Carrier))
      (σ : ∀ i, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (B.size i) F.Carrier)),
      π.IsIrreducible → (∀ i, Nontrivial (σ i)) →
      Nonempty ((T.normalizedJacquetFunctor B).obj π ≅ FiniteTensor.externalFunctor.obj σ) →
      ∃ f : π.representation.IntertwiningMap
          ((T.normalizedProductInductionFunctor B).obj σ).representation,
        Function.Injective f := by
  let _ := T.topology
  intro π σ hπ hσ ⟨e⟩
  let A : (T.normalizedJacquet B π.representation).IntertwiningMap
      (B.blockTensor (fun i => (σ i).representation)) := SmoothRep.hom e.hom
  let f := (Parabolic.FirstAdjointness.equiv T B π.isSmooth).symm A
  refine ⟨f, ?_⟩
  have := hπ
  rcases Representation.IsIrreducible.injective_or_eq_zero f with hf | hf
  · exact hf
  · exfalso
    have hA : A = 0 := by
      have h1 := congrArg (Parabolic.FirstAdjointness.equiv T B π.isSmooth) hf
      rw [map_zero, LinearEquiv.apply_symm_apply] at h1
      exact h1
    have : Nontrivial (FiniteTensor.externalFunctor.obj σ) :=
      nontrivial_piTensorProduct (fun i => hσ i)
    obtain ⟨y, hy⟩ := exists_ne (0 : FiniteTensor.externalFunctor.obj σ)
    obtain ⟨x, hx⟩ := LevelCalculus.iso_hom_surjective e y
    apply hy
    rw [← hx]
    change A x = 0
    rw [hA]
    rfl


theorem nonempty_ofPairProductIso {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0, uF, uW} ℂ (GeneralLinear b F.Carrier)),
      Nonempty ((T.binaryNormalizedProductFunctor a b).obj (A, B) ≅
        (T.normalizedProductInductionFunctor (BlockShape.ofPair a b ha hb rfl)).obj
          (twoBlockFactors ha hb A B)) := by
  let _ := T.topology
  intro A B
  have hrs : ∀ i : Fin 2, (![a, b] : Fin 2 → ℕ) i = (BlockShape.binary a b ha hb).size i := by
    intro i
    fin_cases i <;> rfl
  have hfam : (T.binaryPairFamilyFunctor ha hb).obj (A, B) =
      (fun i => T.castRank (hrs i) (twoBlockFactors ha hb A B i)) := by
    funext i
    fin_cases i <;> rfl
  have hobj : (T.binaryNormalizedProductFunctor a b).obj (A, B) =
      (T.normalizedProductInductionFunctor (BlockShape.binary a b ha hb)).obj
        (fun i => T.castRank (hrs i) (twoBlockFactors ha hb A B i)) := by
    rw [T.binaryNormalizedProductFunctor_of_pos ha hb]
    change (T.normalizedProductInductionFunctor (BlockShape.binary a b ha hb)).obj
        ((T.binaryPairFamilyFunctor ha hb).obj (A, B)) = _
    rw [hfam]
    rfl
  exact ⟨eqToIso hobj ≪≫ T.normalizedProductRankCastIso ![a, b]
    (BlockShape.binary a b ha hb).size (BlockShape.ofPair a b ha hb rfl).positive
    (BlockShape.binary a b ha hb).positive hrs (BlockShape.ofPair a b ha hb rfl).sum_eq
    (BlockShape.binary a b ha hb).sum_eq (twoBlockFactors ha hb A B)⟩

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- If an irreducible `π` has two-block Jacquet module `A ⊗ B` and the top derivative of
`B` vanishes, then the top derivative of `π` vanishes: `π` embeds in `A × B`, whose top
derivative is `A^(a) ⊗ B^(b)`. -/
theorem subsingleton_top_of_jacquet {N a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = N) :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier))
      (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)),
      π.IsIrreducible → Nontrivial A → Nontrivial B →
      Nonempty ((T.normalizedJacquetFunctor (BlockShape.ofPair a b ha hb h)).obj π ≅
        FiniteTensor.externalFunctor.obj (twoBlockFactors ha hb A B)) →
      Subsingleton ((generalLinearDerivative T ψ b b le_rfl).obj B) →
        Subsingleton ((generalLinearDerivative T ψ N N le_rfl).obj π) := by
  subst h
  let _ := T.topology
  intro π A B hπ hA hB hJ hδ
  have hσ : ∀ i, Nontrivial (twoBlockFactors ha hb A B i) := by
    intro i
    fin_cases i
    · exact hA
    · exact hB
  obtain ⟨f, hf⟩ := exists_injective_of_jacquet_iso T (BlockShape.ofPair a b ha hb rfl) π
    (twoBlockFactors ha hb A B) hπ hσ hJ
  obtain ⟨e⟩ := nonempty_ofPairProductIso T ha hb A B
  let g : π ⟶ (T.binaryNormalizedProductFunctor a b).obj (A, B) := SmoothRep.ofHom f ≫ e.inv
  have hg : Function.Injective (SmoothRep.hom g) :=
    (LevelCalculus.iso_hom_injective e.symm).comp hf
  have hD := LevelCalculus.map_injective_of_exact
    (generalLinearDerivativeExactness F T ψ (a + b) (a + b) le_rfl) g hg
  have := subsingleton_top_binaryProduct T ψ a b A B hδ
  exact LevelCalculus.subsingleton_of_injective _ hD

end Embedding


/-! ## Segment socles -/

section Socles

/-- The strong socle relation is transported along an equivalence of the socle. -/
theorem isIrreducibleSocle_of_targetEquiv {G : Type*} [Group G] {V W W' : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W']
    [Module ℂ W'] {ρ : Representation ℂ G V} {π : Representation ℂ G W}
    {π' : Representation ℂ G W'} (e : π.Equiv π') (h : IsIrreducibleSocle ρ π) :
    IsIrreducibleSocle ρ π' := by
  obtain ⟨hπ, j, hj, huniq⟩ := h
  refine ⟨(Weil.IsomorphismInvariance.irreducible_iff e).mp hπ,
    j.comp e.symm.toIntertwiningMap, fun x y hxy => e.symm.injective (hj hxy), ?_⟩
  intro W'' _ _ π'' hπ'' j' hj'
  rw [huniq W'' π'' hπ'' j' hj']
  ext x
  simp only [LinearMap.mem_range]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨e w, by simp⟩
  · rintro ⟨w, rfl⟩
    exact ⟨e.symm w, rfl⟩

variable (T : F.TopologicalData)

theorem isSegmentSocle_of_equiv {Δ : T.Segment.{uV, uF}}
    {π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (e : letI := T.topology; π.representation.Equiv π'.representation)
    (h : T.IsSegmentSocle Δ π) : T.IsSegmentSocle Δ π' := by
  obtain ⟨A, hA, hs⟩ := h
  exact ⟨A, hA, isIrreducibleSocle_of_targetEquiv e hs⟩

theorem isIrreducible_of_isSegmentSocle {Δ : T.Segment.{uV, uF}}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (h : T.IsSegmentSocle Δ π) :
    letI := T.topology
    π.IsIrreducible := by
  obtain ⟨A, hA, hs⟩ := h
  exact hs.1

theorem isSupercuspidal_castRank {r s : ℕ} (h : r = s) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uW} ℂ (GeneralLinear r F.Carrier),
      GeneralLinear.IsSupercuspidal A.representation →
        GeneralLinear.IsSupercuspidal (T.castRank h A).representation := by
  subst h
  intro A hA
  exact hA

/-- A socle of a one-term segment is irreducible and supercuspidal. -/
theorem supercuspidal_of_isSegmentSocle_length_one :
    letI := T.topology
    ∀ (Δ : T.Segment.{uV, uF})
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentSocle Δ π → Δ.length = 1 →
        π.IsIrreducible ∧ GeneralLinear.IsSupercuspidal π.representation := by
  let _ := T.topology
  intro Δ
  obtain ⟨ρ, m, hm⟩ := Δ
  intro π hπ h1
  change m = 1 at h1
  subst h1
  obtain ⟨A, hA, hirr, j, hj, -⟩ := hπ
  refine ⟨hirr, ?_⟩
  let e := T.singletonSegmentInducedEquiv ρ.rank_pos A.obj
  have hB := T.isIrreducible_castRank (Nat.one_mul ρ.rank).symm A.obj A.property.1
  let g := e.toIntertwiningMap.comp j
  have hg : Function.Injective g := fun x y hxy => hj (e.injective hxy)
  have hnt := nontrivial_of_isIrreducible hirr
  have hsurj : Function.Surjective g := by
    have := hB
    rcases Representation.IsIrreducible.surjective_or_eq_zero g with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (0 : π)
      apply hx
      apply hg
      rw [h, map_zero]
      rfl
  have eq := Representation.IntertwiningMap.ofBijective g ⟨hg, hsurj⟩
  exact GeneralLinear.isSupercuspidal_of_equiv eq.symm
    (isSupercuspidal_castRank T _ A.obj A.property.2)

/-- A socle of a one-term segment is equivalent to the rank transport of a supercuspidal
representative of the segment's base. -/
theorem exists_equiv_castRank_of_length_one :
    letI := T.topology
    ∀ (Δ : T.Segment.{uV, uF})
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentSocle Δ π → Δ.length = 1 →
        ∃ A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := Δ.rank),
          Δ.base.IsRepresentedBy A ∧ ∀ h : Δ.rank = Δ.degree,
            Nonempty (π.representation.Equiv (T.castRank h A.obj).representation) := by
  let _ := T.topology
  intro Δ
  obtain ⟨ρ, m, hm⟩ := Δ
  intro π hπ h1
  change m = 1 at h1
  subst h1
  obtain ⟨A, hA, hirr, j, hj, -⟩ := hπ
  refine ⟨A, hA, fun h => ?_⟩
  let e := T.singletonSegmentInducedEquiv ρ.rank_pos A.obj
  have hB := T.isIrreducible_castRank (Nat.one_mul ρ.rank).symm A.obj A.property.1
  let g := e.toIntertwiningMap.comp j
  have hg : Function.Injective g := fun x y hxy => hj (e.injective hxy)
  have hnt := nontrivial_of_isIrreducible hirr
  have hsurj : Function.Surjective g := by
    have := hB
    rcases Representation.IsIrreducible.surjective_or_eq_zero g with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (0 : π)
      apply hx
      apply hg
      rw [h, map_zero]
      rfl
  exact ⟨Representation.IntertwiningMap.ofBijective g ⟨hg, hsurj⟩⟩

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- BZ77 §4.4 (statement (a)) in an arbitrary positive rank. -/
theorem supercuspidal_derivatives_of {N : ℕ} (hN : 0 < N) :
    letI := T.topology
    ∀ π : SmoothRep.{0, uF, uW} ℂ (GeneralLinear N F.Carrier),
      π.IsIrreducible → GeneralLinear.IsSupercuspidal π.representation →
        (∀ (k : ℕ) (hk : k ≤ N), 0 < k → k < N →
          Subsingleton ((generalLinearDerivative T ψ N k hk).obj π)) ∧
        Module.finrank ℂ ((generalLinearDerivative T ψ N N le_rfl).obj π) = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  intro π hπ hsc
  exact supercuspidalDerivatives F T ψ n π hπ hsc

theorem finrank_derivative_order_eq {N k k' : ℕ} (hk : k ≤ N) (hk' : k' ≤ N) (h : k = k') :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uW} ℂ (GeneralLinear N F.Carrier),
      Module.finrank ℂ ((generalLinearDerivative T ψ N k hk).obj X) =
        Module.finrank ℂ ((generalLinearDerivative T ψ N k' hk').obj X) := by
  subst h
  intro X
  rfl

/-- The top derivative of a one-term segment socle is a line. -/
theorem finrank_topDerivative_of_length_one :
    letI := T.topology
    ∀ (Δ : T.Segment.{uV, uF})
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentSocle Δ π → Δ.length = 1 →
        Module.finrank ℂ ((topDerivative T ψ Δ.degree).obj π) = 1 := by
  let _ := T.topology
  intro Δ π hπ h1
  obtain ⟨hirr, hsc⟩ := supercuspidal_of_isSegmentSocle_length_one T Δ π hπ h1
  have h := (supercuspidal_derivatives_of T ψ Δ.degree_pos π hirr hsc).2
  change Module.finrank ℂ ((generalLinearRankCast T (Nat.sub_self Δ.degree)).obj
    ((generalLinearDerivative T ψ Δ.degree Δ.degree (Nat.le_refl _)).obj π)) = 1
  rw [TwoSupercuspidalPartialDerivatives.finrank_rankCast]
  exact h

theorem castRank_derivative_eq {N a k k' : ℕ} (hk : k ≤ N) (hk' : k' ≤ N) (hkk : k = k')
    (c : N - k = a) (c' : N - k' = a) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uW} ℂ (GeneralLinear N F.Carrier),
      T.castRank c ((generalLinearDerivative T ψ N k hk).obj X) =
        (generalLinearRankCast T c').obj ((generalLinearDerivative T ψ N k' hk').obj X) := by
  subst hkk
  subst c
  intro X
  rfl

end Socles

/-! ## Lemma 3.9: the top derivative of a long segment socle vanishes -/

section TopVanishing

variable (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- Ze80 Lemma 3.9 for all lengths `m + 2`, from its length-two case: by Ze80 3.4 the
socle `⟨Δ⟩` has Jacquet module `ρ ⊗ ⟨Δ'⟩` with `Δ' = [νρ, ν^(m+1) ρ]`, so it embeds in
`ρ × ⟨Δ'⟩`, whose top derivative vanishes by induction. -/
theorem top_subsingleton_of_base
    (hbase : letI := T.topology
      ∀ (Δ : T.Segment.{uV, uF})
        (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
        T.IsSegmentSocle Δ π → Δ.length = 2 →
          Subsingleton ((generalLinearDerivative T ψ Δ.degree Δ.degree le_rfl).obj π)) :
    letI := T.topology
    ∀ (m : ℕ) (Δ : T.Segment.{uV, uF})
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      Δ.length = m + 2 → T.IsSegmentSocle Δ π →
        Subsingleton ((generalLinearDerivative T ψ Δ.degree Δ.degree le_rfl).obj π) := by
  let _ := T.topology
  intro m
  induction m with
  | zero =>
    intro Δ π hm hπ
    exact hbase Δ π hπ hm
  | succ m ih =>
    intro Δ π hm hπ
    have hq : (0 : ℕ) < 1 := Nat.one_pos
    have hqm : 1 < Δ.length := by omega
    obtain ⟨π₁, π₂, h₁, h₂, hJ⟩ := (segmentSocleJacquetFormula F T Δ π hπ).2 1 hq hqm
    have hδ := ih (Δ.terminal 1 hqm) π₂ (by rw [PadicField.TopologicalData.Segment.terminal_length]; omega) h₂
    exact subsingleton_top_of_jacquet T ψ (Δ.initial 1 hq).degree_pos
      (Δ.terminal 1 hqm).degree_pos (Δ.initial_degree_add_terminal_degree 1 hq hqm) π π₁ π₂
      (isIrreducible_of_isSegmentSocle T hπ)
      (nontrivial_of_isIrreducible (isIrreducible_of_isSegmentSocle T h₁))
      (nontrivial_of_isIrreducible (isIrreducible_of_isSegmentSocle T h₂)) hJ hδ

end TopVanishing


/-! ## Base-case tools -/

section BaseTools

/-- The block tensor of factorwise equivalences, across carrier universes. -/
def blockTensorEquiv {K : Type*} [CommRing K] {n : ℕ} (B : BlockShape n)
    {V : Fin B.length → Type uW} {W : Fin B.length → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {ρ : ∀ i, Representation ℂ (GeneralLinear (B.size i) K) (V i)}
    {τ : ∀ i, Representation ℂ (GeneralLinear (B.size i) K) (W i)}
    (e : ∀ i, (ρ i).Equiv (τ i)) :
    (B.blockTensor ρ).Equiv (B.blockTensor τ) :=
  Representation.Equiv.mk (PiTensorProduct.congr (fun i => (e i).toLinearEquiv))
    (by
      intro g
      ext v
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, BlockShape.blockTensor_tprod,
        PiTensorProduct.congr_tprod]
      congr 1
      funext i
      exact DFunLike.congr_fun ((e i).isIntertwining' (g i)) (v i))

/-- If every graded piece of a filtration vanishes, the source vanishes. -/
theorem subsingleton_of_graded {C : Type*} [Category C] {G : Type*} [Monoid G]
    {Φ : C ⥤ Rep.{uW} ℂ G} {n : ℕ} (s : RepFunctorFiltration Φ n) (X : C)
    (h : ∀ i, Subsingleton ((s.graded i).obj X)) : Subsingleton (Φ.obj X) := by
  have key : ∀ i : Fin (n + 1), ((s.step i).obj X).toSubmodule = ⊥ := by
    intro i
    induction i using Fin.induction with
    | zero =>
      rw [show (s.step 0).obj X = ⊥ from s.zero X]
      rfl
    | succ i ih =>
      rw [eq_bot_iff]
      intro v hv
      have h0 : (Submodule.Quotient.mk ⟨v, hv⟩ :
          ↥((s.step i.succ).obj X).toSubmodule ⧸
            ((s.step i.castSucc).obj X).toSubmodule.comap
              ((s.step i.succ).obj X).toSubmodule.subtype) = 0 :=
        @Subsingleton.elim _ (h i) _ _
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, ih] at h0
      simpa using h0
  have htop := key (Fin.last n)
  rw [show (s.step (Fin.last n)).obj X = ⊤ from s.top X] at htop
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ (⊥ : Submodule ℂ (Φ.obj X)) := by
    rw [← htop]
    exact Submodule.mem_top
  have hy : y ∈ (⊥ : Submodule ℂ (Φ.obj X)) := by
    rw [← htop]
    exact Submodule.mem_top
  rw [Submodule.mem_bot] at hx hy
  rw [hx, hy]

variable (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- A binary product with a zero factor is zero. -/
theorem subsingleton_binary {a b : ℕ}
    (X : letI := T.topology
      SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uW} ℂ (GeneralLinear b F.Carrier))
    (h : Subsingleton X.1 ∨ Subsingleton X.2) :
    Subsingleton ((T.binaryNormalizedProductFunctor a b).obj X) := by
  let _ := T.topology
  have hz : ∀ {m : ℕ} (A : SmoothRep.{0, uF, uW} ℂ (GeneralLinear m F.Carrier)),
      Subsingleton A → Limits.IsZero A := by
    intro m A hA
    rw [Limits.IsZero.iff_id_eq_zero]
    ext v
    exact Subsingleton.elim _ _
  have hZ := T.isZero_binaryNormalizedProductFunctor_obj X
    (h.imp (fun h1 => hz X.1 h1) (fun h2 => hz X.2 h2))
  refine ⟨fun v w => ?_⟩
  have h0 : ∀ u : (T.binaryNormalizedProductFunctor a b).obj X, u = 0 := fun u =>
    congrArg (fun φ => SmoothRep.hom φ u) (hZ.eq_of_src (𝟙 _) 0)
  rw [h0 v, h0 w]

/-- The top derivative of a binary product has the product of the dimensions of the
top derivatives of its factors. -/
theorem finrank_top_binaryProduct (a b : ℕ) :
    letI := T.topology
    ∀ (D : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier))
      (P : SmoothRep.{0, uF, uW} ℂ (GeneralLinear b F.Carrier)),
      Module.finrank ℂ ((generalLinearDerivative T ψ (a + b) (a + b) le_rfl).obj
          ((T.binaryNormalizedProductFunctor a b).obj (D, P))) =
        Module.finrank ℂ ((generalLinearDerivative T ψ a a le_rfl).obj D) *
          Module.finrank ℂ ((generalLinearDerivative T ψ b b le_rfl).obj P) := by
  let _ := T.topology
  intro D P
  obtain ⟨e, s, hs⟩ := GeneralLinearDerivativeLeibnizFiltrationStatement.filtration T
    (generalLinearDerivativeLeibnizFiltration.{uF, uW} F T) ψ a b (a + b) le_rfl
  have hcard : (leibnizIndices a b (a + b)).card = 1 := by
    rw [leibnizIndices_top, Finset.card_singleton]
  have hpiece : ∀ y : LeibnizIndex a b (a + b),
      Module.finrank ℂ ((leibnizPiece T ψ a b (a + b) y).obj (D, P)) =
        Module.finrank ℂ ((generalLinearDerivative T ψ a a le_rfl).obj D) *
          Module.finrank ℂ ((generalLinearDerivative T ψ b b le_rfl).obj P) := by
    intro y
    have hy := mem_leibnizIndices.mp y.property
    have h1 : y.val.1 = a := by omega
    have h2 : y.val.2 = b := by omega
    have h3 : b - y.val.2 = 0 := by omega
    rw [leibnizPiece_obj]
    refine (TwoSupercuspidalPartialDerivatives.finrank_rankCast T _ _).trans ?_
    obtain ⟨f⟩ := nonempty_binaryProduct_rank_zero_equiv T h3
      ((generalLinearDerivative T ψ a y.val.1 (leibnizIndices_left_le y.property)).obj D)
      ((generalLinearDerivative T ψ b y.val.2 (leibnizIndices_right_le y.property)).obj P)
    rw [f.finrank_eq, Module.finrank_tensorProduct,
      finrank_derivative_order_eq T ψ _ le_rfl h1,
      finrank_derivative_order_eq T ψ _ le_rfl h2]
  let i : Fin (leibnizIndices a b (a + b)).card := e ⟨(a, b), by simp⟩
  obtain ⟨φ⟩ := hs i
  obtain ⟨g⟩ := nonempty_graded_equiv_of_length_one s hcard i (D, P)
  rw [← (hpiece (e.symm i)), ← (Representation.equivOfIso (φ.app (D, P))).toLinearEquiv.finrank_eq]
  exact g.finrank_eq.symm

/-- `(A₁ × A₂)^(j) = 0` for supercuspidal `A₁, A₂` of rank `k` and `k < j < 2k`: every
Leibniz grade contains a derivative of order strictly between `0` and `k` of a
supercuspidal factor. -/
theorem subsingleton_middle_derivative_binary {k j : ℕ} (hk : 0 < k) (hj1 : k < j)
    (hj2 : j < k + k) (hjN : j ≤ k + k) :
    letI := T.topology
    ∀ (A₁ A₂ : SmoothRep.{0, uF, uW} ℂ (GeneralLinear k F.Carrier)),
      A₁.IsIrreducible → GeneralLinear.IsSupercuspidal A₁.representation →
      A₂.IsIrreducible → GeneralLinear.IsSupercuspidal A₂.representation →
        Subsingleton ((generalLinearDerivative T ψ (k + k) j hjN).obj
          ((T.binaryNormalizedProductFunctor k k).obj (A₁, A₂))) := by
  let _ := T.topology
  intro A₁ A₂ h₁ s₁ h₂ s₂
  obtain ⟨e, s, hs⟩ := GeneralLinearDerivativeLeibnizFiltrationStatement.filtration T
    (generalLinearDerivativeLeibnizFiltration.{uF, uW} F T) ψ k k j hjN
  apply subsingleton_of_graded s (A₁, A₂)
  intro i
  obtain ⟨φ⟩ := hs i
  suffices hP : Subsingleton ((leibnizPiece T ψ k k j (e.symm i)).obj (A₁, A₂)) from
    (Representation.equivOfIso (φ.app (A₁, A₂))).toLinearEquiv.toEquiv.subsingleton
  set y := e.symm i
  have hy := mem_leibnizIndices.mp y.property
  rw [leibnizPiece_obj]
  refine (subsingleton_rankCast_iff T _ _).mpr ?_
  apply subsingleton_binary T
  by_cases hlt : y.val.1 < k
  · left
    exact (supercuspidal_derivatives_of T ψ hk A₁ h₁ s₁).1 _ _ (by omega) hlt
  · right
    exact (supercuspidal_derivatives_of T ψ hk A₂ h₂ s₂).1 _ _ (by omega) (by omega)

end BaseTools


/-! ## Lemma 3.9 for segments of length two -/

section BaseCase

variable (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- No nonzero real power of `ν` fixes a cuspidal datum. -/
theorem twist_ne_self (ρ : T.CuspidalDatum.{uV, uF}) (s : ℝ) (hs : s ≠ 0) :
    ρ.twist s ≠ ρ := by
  let := T.topology
  intro h
  rcases ρ with ⟨r, hr, c⟩
  have hc : T.supercuspidalClassRealPowerTwist r s c = c := by
    simpa only [PadicField.TopologicalData.CuspidalDatum.twist,
      PadicField.TopologicalData.CuspidalDatum.mk.injEq, heq_eq_eq, true_and] using h
  induction c using Quotient.inductionOn with
  | h A =>
    let At := SupercuspidalRep.twist (T.determinantPowerCharacter r s)
      (T.isOpen_ker_determinantPowerCharacter r s)
      (T.ker_determinant_le_ker_determinantPowerCharacter r s) A
    change At.isoClass = A.isoClass at hc
    obtain ⟨e⟩ := (SupercuspidalRep.isoClass_eq_iff At A).mp hc
    let e' := SmoothRep.equivOfIso ((supercuspidalProperty (F := F.Carrier)
      (n := r)).ι.mapIso e.symm)
    exact hs (Derivative.OrderedCuspidalProductTwistOne.exponent_eq_zero T r hr A.obj
      A.property.2.1 A.property.1 s e')

theorem isIrreducible_rankCast_iff {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier),
      ((generalLinearRankCast T h).obj X).IsIrreducible ↔ X.IsIrreducible := by
  subst h
  intro X
  exact Iff.rfl

theorem nonempty_equiv_castRank_of_rankCast {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ (Y : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier))
      (X : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)),
      ((generalLinearRankCast T h).obj Y).representation.Equiv X.representation →
        Nonempty (Y.representation.Equiv (T.castRank h.symm X).representation) := by
  subst h
  intro Y X e
  exact ⟨e⟩

/-- A quotient of a representation with zero derivative has zero derivative. -/
theorem subsingleton_derivative_quotient {N j : ℕ} (hj : j ≤ N) :
    letI := T.topology
    ∀ (P : SmoothRep.{0, uF, uW} ℂ (GeneralLinear N F.Carrier))
      (S : Subrepresentation P.representation),
      Subsingleton ((generalLinearDerivative T ψ N j hj).obj P) →
        Subsingleton ((generalLinearDerivative T ψ N j hj).obj (SmoothRep.quotient P S)) := by
  let _ := T.topology
  intro P S hP
  have hE := LevelCalculus.isShortExact_map
    (generalLinearDerivativeExactness F T ψ N j hj)
    (LevelCalculus.isShortExact_kernelι (SmoothRep.mkQ P S) (SmoothRep.mkQ_surjective P S))
  refine ⟨fun x y => ?_⟩
  obtain ⟨u, rfl⟩ := hE.surjective x
  obtain ⟨v, rfl⟩ := hE.surjective y
  rw [Subsingleton.elim u v]


/-- The top derivative of a product of two supercuspidal representations is a line. -/
theorem finrank_top_twoBlocks {k : ℕ} (hk : 0 < k) :
    letI := T.topology
    ∀ A₁ A₂ : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k),
      Module.finrank ℂ ((generalLinearDerivative T ψ (k + k) (k + k) le_rfl).obj
        ((T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
          (twoBlockFactors hk hk A₁.obj A₂.obj))) = 1 := by
  let _ := T.topology
  intro A₁ A₂
  obtain ⟨e⟩ := nonempty_ofPairProductIso T hk hk A₁.obj A₂.obj
  have h := finrank_top_binaryProduct T ψ k k A₁.obj A₂.obj
  rw [(supercuspidal_derivatives_of T ψ hk A₁.obj A₁.property.1 A₁.property.2).2,
    (supercuspidal_derivatives_of T ψ hk A₂.obj A₂.property.1 A₂.property.2).2] at h
  have h2 := (SmoothRep.equivOfIso
    ((generalLinearDerivative T ψ (k + k) (k + k) le_rfl).mapIso e)).toLinearEquiv.finrank_eq
  exact h2.symm.trans (h.trans (Nat.one_mul 1))

/-- The middle derivatives of a product of two supercuspidal representations of rank
`k` vanish strictly between `k` and `2k`. -/
theorem subsingleton_middle_twoBlocks {k j : ℕ} (hk : 0 < k) (hj1 : k < j) (hj2 : j < k + k)
    (hjN : j ≤ k + k) :
    letI := T.topology
    ∀ A₁ A₂ : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k),
      Subsingleton ((generalLinearDerivative T ψ (k + k) j hjN).obj
        ((T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
          (twoBlockFactors hk hk A₁.obj A₂.obj))) := by
  let _ := T.topology
  intro A₁ A₂
  obtain ⟨e⟩ := nonempty_ofPairProductIso T hk hk A₁.obj A₂.obj
  have h := subsingleton_middle_derivative_binary T ψ hk hj1 hj2 hjN A₁.obj A₂.obj
    A₁.property.1 A₁.property.2 A₂.property.1 A₂.property.2
  exact (LevelCalculus.subsingleton_iff_of_iso
    ((generalLinearDerivative T ψ (k + k) j hjN).mapIso e)).mp h

/-- If the top derivative of `P` is a line and that of `S ⊆ P` is nonzero, the top
derivative of `P / S` vanishes. -/
theorem subsingleton_top_quotient {N : ℕ} :
    letI := T.topology
    ∀ (P : SmoothRep.{0, uF, uW} ℂ (GeneralLinear N F.Carrier))
      (S : Subrepresentation P.representation),
      Module.finrank ℂ ((generalLinearDerivative T ψ N N le_rfl).obj P) = 1 →
      Nontrivial ((generalLinearDerivative T ψ N N le_rfl).obj
        (SmoothRep.subrepresentation P S)) →
        Subsingleton ((generalLinearDerivative T ψ N N le_rfl).obj
          (SmoothRep.quotient P S)) := by
  let _ := T.topology
  intro P S hP hS
  have hSE : LevelCalculus.IsShortExact (SmoothRep.subtype P S) (SmoothRep.mkQ P S) := by
    refine ⟨SmoothRep.subtype_injective P S, SmoothRep.mkQ_surjective P S, ?_⟩
    show LinearMap.range S.toSubmodule.subtype = LinearMap.ker S.toSubmodule.mkQ
    rw [Submodule.range_subtype, Submodule.ker_mkQ]
  have hE := LevelCalculus.isShortExact_map
    (generalLinearDerivativeExactness F T ψ N N le_rfl) hSE
  have : FiniteDimensional ℂ ((generalLinearDerivative T ψ N N le_rfl).obj P) :=
    Module.finite_of_finrank_eq_succ hP
  have hinj := hE.injective
  have : FiniteDimensional ℂ ((generalLinearDerivative T ψ N N le_rfl).obj
      (SmoothRep.subrepresentation P S)) :=
    Module.Finite.of_injective (SmoothRep.hom ((generalLinearDerivative T ψ N N le_rfl).map
      (SmoothRep.subtype P S))).toLinearMap hinj
  have h1 : Module.finrank ℂ ((generalLinearDerivative T ψ N N le_rfl).obj
      (SmoothRep.subrepresentation P S)) = 1 := by
    have hle := LinearMap.finrank_le_finrank_of_injective
      (f := (SmoothRep.hom ((generalLinearDerivative T ψ N N le_rfl).map
        (SmoothRep.subtype P S))).toLinearMap) hinj
    have hpos := Module.finrank_pos (R := ℂ) (M := (generalLinearDerivative T ψ N N
      le_rfl).obj (SmoothRep.subrepresentation P S))
    omega
  have hrange : LinearMap.range (SmoothRep.hom ((generalLinearDerivative T ψ N N le_rfl).map
      (SmoothRep.subtype P S))).toLinearMap = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj hinj, h1, hP]
  rw [hE.exact] at hrange
  refine ⟨fun x y => ?_⟩
  obtain ⟨u, rfl⟩ := hE.surjective x
  obtain ⟨v, rfl⟩ := hE.surjective y
  have hu : u ∈ LinearMap.ker (SmoothRep.hom ((generalLinearDerivative T ψ N N le_rfl).map
      (SmoothRep.mkQ P S))).toLinearMap := by
    rw [hrange]
    exact Submodule.mem_top
  have hv : v ∈ LinearMap.ker (SmoothRep.hom ((generalLinearDerivative T ψ N N le_rfl).map
      (SmoothRep.mkQ P S))).toLinearMap := by
    rw [hrange]
    exact Submodule.mem_top
  rw [LinearMap.mem_ker] at hu hv
  exact hu.trans hv.symm

theorem isIrreducible_of_rankCast_equiv {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ (Y : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier))
      (X : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)),
      ((generalLinearRankCast T h).obj Y).representation.Equiv X.representation →
        X.IsIrreducible → Y.IsIrreducible := by
  subst h
  intro Y X e hX
  exact (Weil.IsomorphismInvariance.irreducible_iff e).mpr hX

theorem nontrivial_rankCast_iff {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier),
      Nontrivial ((generalLinearRankCast T h).obj X) ↔ Nontrivial X := by
  subst h
  intro X
  exact Iff.rfl

theorem nontrivial_blockTensor_twoBlocks {k : ℕ} (hk : 0 < k) :
    letI := T.topology
    ∀ A₁ A₂ : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k),
      Nontrivial (PiTensorProduct ℂ (fun i => (twoBlockFactors hk hk A₁.obj A₂.obj i))) := by
  let _ := T.topology
  intro A₁ A₂
  have h1 : Nontrivial A₁.obj := nontrivial_of_isIrreducible A₁.property.1
  have h2 : Nontrivial A₂.obj := nontrivial_of_isIrreducible A₂.property.1
  apply nontrivial_piTensorProduct
  intro i
  fin_cases i
  · exact h1
  · exact h2

/-- Step one of the base case: if the top derivative of `π ⊆ A₁ × A₂` is nonzero, the
top derivative of the nonzero proper quotient `(A₁ × A₂) / π` vanishes. -/
theorem exists_quotient_of_nontrivial_top (k : ℕ) (hk : 0 < k) :
    letI := T.topology
    ∀ (A₁ A₂ : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)),
      A₂.isoClass = T.supercuspidalClassRealPowerTwist k 1 A₁.isoClass →
      ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (k + k) F.Carrier),
        π.IsIrreducible →
        (T.normalizedJacquet (Shahidi.twoBlocks k k hk hk) π.representation).Equiv
          ((Shahidi.twoBlocks k k hk hk).blockTensor
            (fun i => (twoBlockFactors hk hk A₁.obj A₂.obj i).representation)) →
        Nontrivial ((generalLinearDerivative T ψ (k + k) (k + k) le_rfl).obj π) →
        ∃ S : Subrepresentation ((T.normalizedProductInductionFunctor
            (Shahidi.twoBlocks k k hk hk)).obj (twoBlockFactors hk hk A₁.obj A₂.obj)).representation,
          S ≠ ⊥ ∧ S ≠ ⊤ ∧
          Subsingleton ((generalLinearDerivative T ψ (k + k) (k + k) le_rfl).obj
            (SmoothRep.quotient ((T.normalizedProductInductionFunctor
              (Shahidi.twoBlocks k k hk hk)).obj (twoBlockFactors hk hk A₁.obj A₂.obj)) S)) := by
  let _ := T.topology
  intro A₁ A₂ hcls π hπ eJ hδ
  have hnt12 := nontrivial_blockTensor_twoBlocks T hk A₁ A₂
  obtain ⟨f, hf⟩ := exists_injective_of_jacquet_equiv T (Shahidi.twoBlocks k k hk hk) _ π hπ eJ
  let P := (T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
    (twoBlockFactors hk hk A₁.obj A₂.obj)
  let fP : π ⟶ P := SmoothRep.ofHom f
  have hfP : Function.Injective (SmoothRep.hom fP) := hf
  let S : Subrepresentation P.representation := (SmoothRep.hom fP).range
  have hπnt := nontrivial_of_isIrreducible hπ
  refine ⟨S, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : π)
    have hmem : SmoothRep.hom fP x ∈ S := ⟨x, rfl⟩
    rw [h] at hmem
    have h0 : SmoothRep.hom fP x = 0 := hmem
    exact hx (hfP (h0.trans (map_zero (SmoothRep.hom fP)).symm))
  · intro h
    apply twoSupercuspidalAdjacentProductReducible F T k hk A₁ A₂ (Or.inl hcls)
    have hsurj : Function.Surjective (SmoothRep.hom fP) := fun y => by
      have hy : y ∈ S := by
        rw [h]
        exact Submodule.mem_top
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, hx⟩
    exact (Weil.IsomorphismInvariance.irreducible_iff
      ((SmoothRep.hom fP).ofBijective ⟨hfP, hsurj⟩)).mp hπ
  · have hP1 := finrank_top_twoBlocks T ψ hk A₁ A₂
    have hSnt : Nontrivial ((generalLinearDerivative T ψ (k + k) (k + k) le_rfl).obj
        (SmoothRep.subrepresentation P S)) :=
      (LevelCalculus.nontrivial_iff_of_iso
        ((generalLinearDerivative T ψ (k + k) (k + k) le_rfl).mapIso
          (LevelCalculus.isoRange fP hfP))).mp hδ
    exact subsingleton_top_quotient T ψ P S hP1 hSnt

/-- The two presentations `(k' + 1 + k') + 1` and `(k' + 1) + (k' + 1)` of the rank give
the same derivative. -/
theorem derivative_obj_rank_congr (k' j : ℕ) :
    letI := T.topology
    ∀ (X : SmoothRep.{0, uF, uW} ℂ (GeneralLinear ((k' + 1) + (k' + 1)) F.Carrier))
      (h : j ≤ (k' + 1 + k') + 1) (h' : j ≤ (k' + 1) + (k' + 1)),
      (generalLinearDerivative T ψ ((k' + 1 + k') + 1) j h).obj X =
        (generalLinearDerivative T ψ ((k' + 1) + (k' + 1)) j h').obj X := by
  intro X h h'
  rfl

/-- The ordered pair of supercuspidal factors `(A₂, A₁)` on the blocks of
`twoBlocks k k`. -/
def pairReps {k : ℕ} (hk : 0 < k) (A₂ A₁ : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)) :
    letI := T.topology
    ∀ i : Fin 2, SupercuspidalRep.{uF, uV} (F := F.Carrier)
      (n := (Shahidi.twoBlocks k k hk hk).size i) :=
  Fin.cases A₂ (Fin.cases A₁ finZeroElim)

/-- The cuspidal data of `pairReps`. -/
def pairData {k : ℕ} (hk : 0 < k) (A₂ A₁ : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)) :
    Fin 2 → T.CuspidalDatum.{uV, uF} := fun i =>
  letI := T.topology
  ⟨(Shahidi.twoBlocks k k hk hk).size i, (Shahidi.twoBlocks k k hk hk).positive i,
    (pairReps T hk A₂ A₁ i).isoClass⟩

theorem pairData_sum {k : ℕ} (hk : 0 < k) (A₂ A₁ : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)) :
    ∑ i, (pairData T hk A₂ A₁ i).rank = k + k :=
  (Shahidi.twoBlocks k k hk hk).sum_eq

theorem pairData_zero {k : ℕ} (hk : 0 < k) (A₂ A₁ : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)) :
    letI := T.topology
    pairData T hk A₂ A₁ 0 = ⟨k, hk, A₂.isoClass⟩ := rfl

theorem pairData_one {k : ℕ} (hk : 0 < k) (A₂ A₁ : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)) :
    letI := T.topology
    pairData T hk A₂ A₁ 1 = ⟨k, hk, A₁.isoClass⟩ := rfl

theorem cuspidalProductInduced_pairData {k : ℕ} (hk : 0 < k) (A₂ A₁ : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)) :
    letI := T.topology
    T.cuspidalProductInduced (pairData T hk A₂ A₁) (pairData_sum T hk A₂ A₁)
        (pairReps T hk A₂ A₁) =
      (T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
        (twoBlockFactors hk hk A₂.obj A₁.obj) := by
  let _ := T.topology
  show (T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
    (fun i => (pairReps T hk A₂ A₁ i).obj) = _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- A representation equivalent to a supercuspidal representative of `ρ` has the
supercuspidal support `{ρ}`. -/
theorem isSupercuspidalSupport_singleton {r n : ℕ} (hr : 0 < r) (h : r = n) :
    letI := T.topology
    ∀ (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
      (σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      σ.IsIrreducible → σ.representation.Equiv (T.castRank h A.obj).representation →
        T.IsSupercuspidalSupport σ {(⟨r, hr, A.isoClass⟩ : T.CuspidalDatum.{uV, uF})} := by
  subst h
  let _ := T.topology
  intro A σ hσ e
  have h₀ : ∑ i : Fin 1,
      ((fun _ : Fin 1 => (⟨r, hr, A.isoClass⟩ : T.CuspidalDatum.{uV, uF})) i).rank = r := by
    simp
  refine ⟨1, fun _ => ⟨r, hr, A.isoClass⟩, by simp, h₀, fun _ => A, fun _ => rfl, hσ, ?_⟩
  apply SmoothRep.IsSubrepresentation.isSubquotient
  let C := T.cuspidalShape (fun _ : Fin 1 => (⟨r, hr, A.isoClass⟩ : T.CuspidalDatum.{uV, uF})) h₀
  have hC : C.length = 1 := rfl
  let e2 := T.singleBlockNormalizedProductEquiv C hC
    (fun _ => A.obj.representation) (fun _ => A.obj.isSmooth) (0 : Fin 1)
  let e3 := T.castRankEquiv (C.singleBlock_size hC (0 : Fin 1)) A.obj
  exact ⟨(SmoothRep.mkIso
      (B := T.cuspidalProductInduced
        (fun _ : Fin 1 => (⟨r, hr, A.isoClass⟩ : T.CuspidalDatum.{uV, uF})) h₀ (fun _ => A))
      (e.trans (e2.trans e3).symm)).hom,
    LevelCalculus.iso_hom_injective _⟩

/-- The BZ77 4.7(b) contradiction. Let `Q` embed in `A₂ × A₁` with `A₂ ≅ ν A₁`, have
derivative `Q^(k) ≅ A₂` of order `k = k' + 1`, and no nonzero derivative of higher order.
Then BZ77 Lemma 4.7(b) gives `ν A₂ ∈ {A₂, A₁}`, which is impossible. -/
theorem false_of_highest_derivative (k' : ℕ) (hk : 0 < k' + 1) :
    letI := T.topology
    ∀ (A₁ A₂ : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k' + 1)),
      A₂.isoClass = T.supercuspidalClassRealPowerTwist (k' + 1) 1 A₁.isoClass →
      ∀ (Q : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((k' + 1) + (k' + 1)) F.Carrier))
        (g : Q.representation.IntertwiningMap ((T.normalizedProductInductionFunctor
          (Shahidi.twoBlocks (k' + 1) (k' + 1) hk hk)).obj
            (twoBlockFactors hk hk A₂.obj A₁.obj)).representation),
        Function.Injective g →
        ((generalLinearRankCast T (Nat.add_sub_cancel (k' + 1) (k' + 1))).obj
          ((generalLinearDerivative T ψ ((k' + 1) + (k' + 1)) (k' + 1)
            (Nat.le_add_left (k' + 1) (k' + 1))).obj Q)).representation.Equiv
          A₂.obj.representation →
        (∀ (j : ℕ) (hj : j ≤ (k' + 1) + (k' + 1)), k' + 1 < j →
          Subsingleton ((generalLinearDerivative T ψ ((k' + 1) + (k' + 1)) j hj).obj Q)) →
        False := by
  let _ := T.topology
  intro A₁ A₂ hcls Q g hg eQD hall
  have hP'' := cuspidalProductInduced_pairData T hk A₂ A₁
  let g'' : Q ⟶ T.cuspidalProductInduced (pairData T hk A₂ A₁) (pairData_sum T hk A₂ A₁)
      (pairReps T hk A₂ A₁) :=
    SmoothRep.ofHom g ≫ (eqToIso hP''.symm).hom
  have hg'' : Function.Injective (SmoothRep.hom g'') :=
    (LevelCalculus.iso_hom_injective (eqToIso hP''.symm)).comp hg
  have hk' : 0 < k' + 1 ∧ k' + 1 ≤ (k' + 1 + k') + 1 := ⟨hk, by omega⟩
  have hbr : ∀ (j : ℕ) (hj : 0 < j ∧ j ≤ (k' + 1 + k') + 1),
      (mirabolicDerivativeOfOrder T ψ (k' + 1 + k') j hj).obj
          ((generalLinearRestriction T (k' + 1 + k')).obj Q) =
        (generalLinearDerivative T ψ ((k' + 1 + k') + 1) j hj.2).obj Q := fun j hj =>
    (generalLinearDerivative_obj_eq_restriction T ψ (k' + 1 + k') j hj.2 hj Q).symm
  have hσirr : ((generalLinearDerivative T ψ ((k' + 1) + (k' + 1)) (k' + 1)
      (Nat.le_add_left (k' + 1) (k' + 1))).obj Q).IsIrreducible :=
    isIrreducible_of_rankCast_equiv T (Nat.add_sub_cancel (k' + 1) (k' + 1)) _ A₂.obj eQD
      A₂.property.1
  have hσirrN : ((generalLinearDerivative T ψ ((k' + 1 + k') + 1) (k' + 1)
      hk'.2).obj Q).IsIrreducible := by
    rw [derivative_obj_rank_congr T ψ k' (k' + 1) Q hk'.2 (Nat.le_add_left (k' + 1) (k' + 1))]
    exact hσirr
  have hQk : Nontrivial ((generalLinearDerivative T ψ ((k' + 1 + k') + 1) (k' + 1)
      hk'.2).obj Q) := nontrivial_of_isIrreducible hσirrN
  have hlevel : Derivative.level T ψ ((generalLinearRestriction T (k' + 1 + k')).obj Q) =
      k' + 1 := by
    rw [level_eq_iff T ψ hk]
    refine ⟨hk'.2, (hasNonzeroDerivative_iff T ψ hk' _).mpr (by rw [hbr]; exact hQk), ?_⟩
    rintro j hj1 hj2 ⟨hj, hnt⟩
    rw [hbr, derivative_obj_rank_congr T ψ k' j Q hj.2 (by omega)] at hnt
    exact not_subsingleton_iff_nontrivial.mpr hnt (hall j (by omega) hj1)
  have hσsub : IsIrreducibleSubrepresentation
      ((mirabolicDerivativeOfOrder T ψ (k' + 1 + k') (k' + 1) hk').obj
        ((generalLinearRestriction T (k' + 1 + k')).obj Q)).representation
      ((generalLinearDerivative T ψ ((k' + 1 + k') + 1) (k' + 1) hk'.2).obj Q).representation := by
    rw [hbr]
    exact ⟨hσirrN, Representation.IntertwiningMap.id _, fun _ _ h => h⟩
  obtain ⟨e1⟩ := nonempty_equiv_castRank_of_rankCast T (Nat.add_sub_cancel (k' + 1) (k' + 1))
    _ A₂.obj eQD
  have hsupp' := isSupercuspidalSupport_singleton T hk (Nat.add_sub_cancel (k' + 1) (k' + 1)).symm
    A₂ _ hσirr e1
  have hsupp : T.IsSupercuspidalSupport
      ((generalLinearDerivative T ψ ((k' + 1 + k') + 1) (k' + 1) hk'.2).obj Q)
      {(⟨k' + 1, hk, A₂.isoClass⟩ : T.CuspidalDatum.{uV, uF})} := by
    rw [derivative_obj_rank_congr T ψ k' (k' + 1) Q hk'.2 (Nat.le_add_left (k' + 1) (k' + 1))]
    exact hsupp'
  have hshift := cuspidalProductMirabolicSupportShift F T ψ (k' + 1 + k') 2
    (pairData T hk A₂ A₁) (pairData_sum T hk A₂ A₁) (pairReps T hk A₂ A₁) (fun _ => rfl)
    ((generalLinearRestriction T (k' + 1 + k')).obj Q)
    ((generalLinearRestriction T (k' + 1 + k')).map g'') hg'' (k' + 1) hk' hlevel _ hσsub _ hsupp
  simp only [Multiset.map_singleton, Multiset.singleton_le, Multiset.mem_coe,
    List.mem_ofFn] at hshift
  obtain ⟨i, hi⟩ := hshift
  have h01 : (⟨k' + 1, hk, A₂.isoClass⟩ : T.CuspidalDatum.{uV, uF}) =
      (⟨k' + 1, hk, A₁.isoClass⟩ : T.CuspidalDatum.{uV, uF}).twist 1 := by
    show (⟨k' + 1, hk, A₂.isoClass⟩ : T.CuspidalDatum.{uV, uF}) =
      (⟨k' + 1, hk, T.supercuspidalClassRealPowerTwist (k' + 1) 1 A₁.isoClass⟩ :
        T.CuspidalDatum.{uV, uF})
    rw [hcls]
  have hi01 : i = 0 ∨ i = 1 := by
    fin_cases i <;> simp
  rcases hi01 with rfl | rfl
  · rw [pairData_zero] at hi
    exact twist_ne_self T _ 1 one_ne_zero hi.symm
  · rw [pairData_one, h01, PadicField.TopologicalData.CuspidalDatum.twist_twist] at hi
    norm_num at hi
    exact twist_ne_self T _ 2 two_ne_zero hi.symm

/-- Step two of the base case: for `A₂ ≅ ν A₁`, no nonzero proper quotient `Q` of
`A₁ × A₂` has zero top derivative. -/
theorem false_of_quotient (k' : ℕ) (hk : 0 < k' + 1) :
    letI := T.topology
    ∀ (A₁ A₂ : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k' + 1)),
      A₂.isoClass = T.supercuspidalClassRealPowerTwist (k' + 1) 1 A₁.isoClass →
      ∀ S : Subrepresentation ((T.normalizedProductInductionFunctor
          (Shahidi.twoBlocks (k' + 1) (k' + 1) hk hk)).obj
            (twoBlockFactors hk hk A₁.obj A₂.obj)).representation,
        S ≠ ⊥ → S ≠ ⊤ →
        Subsingleton ((generalLinearDerivative T ψ ((k' + 1) + (k' + 1)) ((k' + 1) + (k' + 1))
          le_rfl).obj (SmoothRep.quotient ((T.normalizedProductInductionFunctor
            (Shahidi.twoBlocks (k' + 1) (k' + 1) hk hk)).obj
              (twoBlockFactors hk hk A₁.obj A₂.obj)) S)) → False := by
  let _ := T.topology
  intro A₁ A₂ hcls S hS0 hS1 hQtop
  obtain ⟨-, hcomp, hjac⟩ := twoSupercuspidalProductStructure F T
  have hc := hcomp (k' + 1) hk A₁ A₂ (Or.inl hcls)
  dsimp only at hc
  have hQirr := (hc.2.2 S hS0 hS1).2
  have hj := hjac (k' + 1) hk A₁ A₂ (Or.inl hcls)
  dsimp only at hj
  obtain ⟨-, ⟨eQJ⟩⟩ := hj S hS0 hS1
  have hm := twoSupercuspidalAdjacentProductMiddleDerivatives F T ψ (k' + 1) hk A₁ A₂
    (Or.inl hcls)
  dsimp only at hm
  obtain ⟨-, ⟨eQD⟩⟩ := hm S hS0 hS1
  have hnt21 := nontrivial_blockTensor_twoBlocks T hk A₂ A₁
  obtain ⟨g, hg⟩ := exists_injective_of_jacquet_equiv T (Shahidi.twoBlocks (k' + 1) (k' + 1) hk hk)
    ((Shahidi.twoBlocks (k' + 1) (k' + 1) hk hk).blockTensor
      (fun i => (twoBlockFactors hk hk A₂.obj A₁.obj i).representation)) _ hQirr eQJ
  refine false_of_highest_derivative T ψ k' hk A₁ A₂ hcls _ g hg eQD ?_
  intro j hj hkj
  rcases Nat.lt_or_ge j ((k' + 1) + (k' + 1)) with hlt | hge
  · exact subsingleton_derivative_quotient T ψ hj _ S
      (subsingleton_middle_twoBlocks T ψ hk hkj hlt hj A₁ A₂)
  · exact (subsingleton_derivative_order_iff T ψ hj le_rfl (le_antisymm hj hge) _).mpr hQtop

/-- Zelevinsky 1980, Lemma 3.9 for a segment of length two, in Jacquet form. -/
theorem top_subsingleton_core (k : ℕ) (hk : 0 < k) :
    letI := T.topology
    ∀ (A₁ A₂ : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)),
      A₂.isoClass = T.supercuspidalClassRealPowerTwist k 1 A₁.isoClass →
      ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (k + k) F.Carrier),
        π.IsIrreducible →
        (T.normalizedJacquet (Shahidi.twoBlocks k k hk hk) π.representation).Equiv
          ((Shahidi.twoBlocks k k hk hk).blockTensor
            (fun i => (twoBlockFactors hk hk A₁.obj A₂.obj i).representation)) →
        Subsingleton ((generalLinearDerivative T ψ (k + k) (k + k) le_rfl).obj π) := by
  let _ := T.topology
  intro A₁ A₂ hcls π hπ eJ
  by_contra hδ
  rw [not_subsingleton_iff_nontrivial] at hδ
  obtain ⟨S, hS0, hS1, hQ⟩ :=
    exists_quotient_of_nontrivial_top T ψ k hk A₁ A₂ hcls π hπ eJ hδ
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact false_of_quotient T ψ k' hk A₁ A₂ hcls S hS0 hS1 hQ

/-- The base case with the two segment ranks transported to the common rank `r`. -/
theorem top_subsingleton_of_jacquet_pair {N a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a + b = N)
    {r : ℕ} (hr : 0 < r) (h₁ : r = a) (h₂ : r = b) :
    letI := T.topology
    ∀ (A₁ A₂ : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r)),
      A₂.isoClass = T.supercuspidalClassRealPowerTwist r 1 A₁.isoClass →
      ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier),
        π.IsIrreducible →
        (T.normalizedJacquet (BlockShape.ofPair a b ha hb h) π.representation).Equiv
          ((BlockShape.ofPair a b ha hb h).blockTensor (fun i => (twoBlockFactors ha hb
            (T.castRank h₁ A₁.obj) (T.castRank h₂ A₂.obj) i).representation)) →
        Subsingleton ((generalLinearDerivative T ψ N N le_rfl).obj π) := by
  subst h₁ h₂ h
  intro A₁ A₂ hcls π hπ eJ
  exact top_subsingleton_core T ψ r hr A₁ A₂ hcls π hπ eJ

/-- Zelevinsky 1980, Lemma 3.9, for a segment of length two: by Ze80 3.4 the socle
`⟨[ρ, νρ]⟩` has Jacquet module `ρ ⊗ νρ`. -/
theorem top_subsingleton_length_two :
    letI := T.topology
    ∀ (Δ : T.Segment.{uV, uF})
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentSocle Δ π → Δ.length = 2 →
        Subsingleton ((generalLinearDerivative T ψ Δ.degree Δ.degree le_rfl).obj π) := by
  let _ := T.topology
  intro Δ π hπ h2
  have hq : (0 : ℕ) < 1 := Nat.one_pos
  have hqm : 1 < Δ.length := by omega
  obtain ⟨π₁, π₂, h₁, h₂, ⟨eJ⟩⟩ := (segmentSocleJacquetFormula F T Δ π hπ).2 1 hq hqm
  have hlen : (Δ.terminal 1 hqm).length = 1 := by
    rw [PadicField.TopologicalData.Segment.terminal_length]
    omega
  obtain ⟨A₁, hA₁, e₁⟩ := exists_equiv_castRank_of_length_one T _ π₁ h₁ rfl
  obtain ⟨A₂, hA₂, e₂⟩ := exists_equiv_castRank_of_length_one T _ π₂ h₂ hlen
  have hd₁ : Δ.rank = (Δ.initial 1 hq).degree := (Nat.one_mul _).symm
  have hd₂ : Δ.rank = (Δ.terminal 1 hqm).degree := by
    rw [PadicField.TopologicalData.Segment.terminal_degree, show Δ.length - 1 = 1 by omega,
      Nat.one_mul]
  obtain ⟨f₁⟩ := e₁ hd₁
  obtain ⟨f₂⟩ := e₂ hd₂
  have hcls : A₂.isoClass = T.supercuspidalClassRealPowerTwist Δ.rank 1 A₁.isoClass := by
    have h₂' : A₂.isoClass = (Δ.base.twist ((1 : ℕ) : ℝ)).cls := hA₂
    have h₁' : A₁.isoClass = Δ.base.cls := hA₁
    rw [h₂', h₁', Nat.cast_one]
    rfl
  have eT : ((Δ.socleSplitShape 1 hq hqm).blockTensor
      (fun i => (Δ.socleSplitFactors 1 hq hqm π₁ π₂ i).representation)).Equiv
      ((Δ.socleSplitShape 1 hq hqm).blockTensor (fun i => (twoBlockFactors
        (Δ.initial 1 hq).degree_pos (Δ.terminal 1 hqm).degree_pos
        (T.castRank hd₁ A₁.obj) (T.castRank hd₂ A₂.obj) i).representation)) :=
    blockTensorEquiv _ (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact f₁
      · refine Fin.cases ?_ (fun l => l.elim0) j
        exact f₂)
  exact top_subsingleton_of_jacquet_pair T ψ (Δ.initial 1 hq).degree_pos
    (Δ.terminal 1 hqm).degree_pos (Δ.initial_degree_add_terminal_degree 1 hq hqm) Δ.rank_pos
    hd₁ hd₂ A₁ A₂ hcls π (isIrreducible_of_isSegmentSocle T hπ)
    ((SmoothRep.equivOfIso eJ).trans eT)

end BaseCase

/-! ## Lemma 3.9 and the assembly -/

section Assembly

variable (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- Zelevinsky 1980, Lemma 3.9: the top derivative of a socle of a segment of length at
least two vanishes. -/
theorem top_subsingleton :
    letI := T.topology
    ∀ (Δ : T.Segment.{uV, uF})
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
      T.IsSegmentSocle Δ π → 2 ≤ Δ.length →
        Subsingleton ((generalLinearDerivative T ψ Δ.degree Δ.degree le_rfl).obj π) := by
  let _ := T.topology
  intro Δ π hπ h2
  exact top_subsingleton_of_base T ψ (top_subsingleton_length_two T ψ) (Δ.length - 2) Δ π
    (by omega) hπ

end Assembly

end SegmentSocleDerivativesProof

open SegmentSocleDerivativesProof in
/-- **Zelevinsky 1980, Theorem 3.5.** For every nontrivial unitary additive character `ψ`
and every socle `π` of a segment `Δ = [ρ, ν^(m-1) ρ]` with `ρ` of rank `r`: the derivatives of
`π` of positive order other than `r` vanish; for `m = 1` the order-`r` derivative is a line;
for `m ≥ 2` the order-`r` derivative, transported to rank `(m - 1) r`, is a socle of
`Δ⁻ = [ρ, ν^(m-2) ρ]`. -/
theorem segmentSocleDerivatives {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : SegmentSocleDerivatives.{uF, uV} F T := by
  let _ := T.topology
  intro ψ Δ π hπ
  have htop := top_subsingleton T ψ
  have hn : Δ.degree = Δ.length * Δ.rank := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro k hk hpos hne
    rcases Nat.lt_or_ge k Δ.degree with hlt | hge
    · by_cases hdiv : Δ.rank ∣ k
      · obtain ⟨j, rfl⟩ := hdiv
        have hj1 : j ≠ 1 := by
          rintro rfl
          exact hne (Nat.mul_one _)
        have hj0 : j ≠ 0 := by
          rintro rfl
          simp at hpos
        have hjm : j < Δ.length := by
          by_contra h
          have : Δ.length * Δ.rank ≤ Δ.rank * j := by
            rw [Nat.mul_comm]
            exact Nat.mul_le_mul_left _ (not_lt.mp h)
          omega
        have hq : 0 < Δ.length - j := by omega
        have hqm : Δ.length - j < Δ.length := by omega
        obtain ⟨π₁, π₂, h₁, h₂, hJ⟩ :=
          (segmentSocleJacquetFormula F T Δ π hπ).2 (Δ.length - j) hq hqm
        have hlen : (Δ.terminal (Δ.length - j) hqm).length = j := by
          rw [PadicField.TopologicalData.Segment.terminal_length]
          omega
        have hδ := htop _ π₂ h₂ (by omega)
        have hbk : (Δ.terminal (Δ.length - j) hqm).degree = Δ.rank * j := by
          rw [PadicField.TopologicalData.Segment.terminal_degree, Nat.sub_sub_self hjm.le, Nat.mul_comm]
        have hbN : (Δ.terminal (Δ.length - j) hqm).degree ≤ Δ.degree := by
          rw [hbk]
          exact hk
        have hD := subsingleton_derivative_of_jacquet_tensor T ψ
          (Δ.initial (Δ.length - j) hq).degree_pos (Δ.terminal (Δ.length - j) hqm).degree_pos
          (Δ.initial_degree_add_terminal_degree (Δ.length - j) hq hqm) hbN π π₁ π₂ hJ hδ
        exact (subsingleton_derivative_order_iff T ψ hbN hk hbk π).mp hD
      · have hl : 0 < Δ.degree - k := by omega
        have hln : Δ.degree - k < Δ.degree := by omega
        have hndiv : ¬ Δ.rank ∣ Δ.degree - k := by
          intro h
          apply hdiv
          have hdn : Δ.rank ∣ Δ.degree := ⟨Δ.length, by rw [hn, Nat.mul_comm]⟩
          have := Nat.dvd_sub hdn h
          rwa [Nat.sub_sub_self hk] at this
        have hJ := (segmentSocleJacquetFormula F T Δ π hπ).1 (Δ.degree - k) hl hln hndiv
        have hD := subsingleton_derivative_of_jacquet T ψ hl (Nat.sub_pos_of_lt hln)
          (Nat.add_sub_of_le hln.le) (Nat.sub_le _ _) π hJ
        exact (subsingleton_derivative_order_iff T ψ _ hk (Nat.sub_sub_self hk) π).mp hD
    · have hkn : k = Δ.degree := le_antisymm hk hge
      have h2 : 2 ≤ Δ.length := by
        by_contra h
        have h1 : Δ.length = 1 := by
          have := Δ.length_pos
          omega
        apply hne
        rw [hkn, hn, h1, Nat.one_mul]
      exact (subsingleton_derivative_order_iff T ψ hk le_rfl hkn π).mpr (htop Δ π hπ h2)
  · intro hm h1
    obtain ⟨hirr, hsc⟩ := supercuspidal_of_isSegmentSocle_length_one T Δ π hπ h1
    have hr : Δ.rank = Δ.degree := by rw [hn, h1, Nat.one_mul]
    rw [finrank_derivative_order_eq T ψ hm le_rfl hr]
    exact (supercuspidal_derivatives_of T ψ Δ.degree_pos π hirr hsc).2
  · intro hm h2 hdeg
    have hq : 0 < Δ.length - 1 := by omega
    have hqm : Δ.length - 1 < Δ.length := by omega
    obtain ⟨π₁, π₂, h₁, h₂, hJ⟩ :=
      (segmentSocleJacquetFormula F T Δ π hπ).2 (Δ.length - 1) hq hqm
    have hlen : (Δ.terminal (Δ.length - 1) hqm).length = 1 := by
      rw [PadicField.TopologicalData.Segment.terminal_length]
      omega
    have hfin := finrank_topDerivative_of_length_one T ψ _ π₂ h₂ hlen
    have hkk : Δ.rank = (Δ.terminal (Δ.length - 1) hqm).degree := by
      rw [PadicField.TopologicalData.Segment.terminal_degree, show Δ.length - (Δ.length - 1) = 1 by omega, Nat.one_mul]
    have hsum := Δ.initial_degree_add_terminal_degree (Δ.length - 1) hq hqm
    have hbN : (Δ.terminal (Δ.length - 1) hqm).degree ≤ Δ.degree := by omega
    have hcast : Δ.degree - (Δ.terminal (Δ.length - 1) hqm).degree =
        (Δ.initial (Δ.length - 1) hq).degree := by omega
    obtain ⟨e⟩ := nonempty_derivative_equiv_first T ψ
      (Δ.initial (Δ.length - 1) hq).degree_pos (Δ.terminal (Δ.length - 1) hqm).degree_pos
      hsum hbN hcast π π₁ π₂ hJ hfin
    rw [castRank_derivative_eq T ψ hm hbN hkk hdeg hcast π]
    exact isSegmentSocle_of_equiv T e.symm h₁

end Langlands.Classification
