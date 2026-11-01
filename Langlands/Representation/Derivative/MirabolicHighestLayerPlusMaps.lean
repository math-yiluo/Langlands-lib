import Langlands.Representation.Derivative.MirabolicPlusNormalization

/-!
# Maps used in the actual highest mirabolic layer

Heterogeneous postcomposition on normalized compact Phi-plus, and the
normalized Psi-plus/Psi-minus comparison when the radical acts trivially.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Derivative.Mirabolic.HighestLayer

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

private def phiPlusPostValue (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    {τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} →
    {σ : SmoothRep.{0, uF, uW} ℂ (mirabolic n F.Carrier)} →
    (E : Representation.IntertwiningMap τ.representation σ.representation) →
    Function.Injective E → (phiPlus T ψ n).obj τ → (phiPlus T ψ n).obj σ := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (n + 1 + 1)
  intro τ σ E hE φ
  let hstab := phiPlusNormalizedEval_exists_openSubgroup T ψ n τ φ
  let K := Classical.choose hstab
  have hK := Classical.choose_spec hstab
  refine phiPlusNormalizedMk T ψ n σ
    (fun x => E (phiPlusNormalizedEval T ψ n τ φ x)) ?_ K ?_ ?_
  · intro q x
    rw [phiPlusNormalizedEval_covariant, map_smul, map_smul,
      E.isIntertwining]
  · intro k x
    rw [hK k x]
  · have hs : Induction.quotientSupport (plusSubgroup n F.Carrier)
        (fun x => E (phiPlusNormalizedEval T ψ n τ φ x)) =
        Induction.quotientSupport (plusSubgroup n F.Carrier)
          (phiPlusNormalizedEval T ψ n τ φ) := by
      unfold Induction.quotientSupport
      congr 1
      ext x
      change E (phiPlusNormalizedEval T ψ n τ φ x) ≠ 0 ↔
        phiPlusNormalizedEval T ψ n τ φ x ≠ 0
      rw [← map_zero E, hE.ne_iff]
    rw [hs]
    exact phiPlusNormalizedEval_isCompact_quotientSupport T ψ n τ φ

private theorem phiPlusPostValue_eval (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)}
      {σ : SmoothRep.{0, uF, uW} ℂ (mirabolic n F.Carrier)}
      (E : Representation.IntertwiningMap τ.representation σ.representation)
      (hE : Function.Injective E) (φ : (phiPlus T ψ n).obj τ)
      (x : mirabolic (n + 1) F.Carrier),
      phiPlusNormalizedEval T ψ n σ (phiPlusPostValue T ψ n E hE φ) x =
        E (phiPlusNormalizedEval T ψ n τ φ x) := by
  intros
  rfl

/-- Postcompose actual normalized compact functions with an injective intertwiner,
allowing independent carrier universes. -/
def phiPlusPost (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    {τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} →
    {σ : SmoothRep.{0, uF, uW} ℂ (mirabolic n F.Carrier)} →
    (E : Representation.IntertwiningMap τ.representation σ.representation) →
    Function.Injective E →
    Representation.IntertwiningMap ((phiPlus T ψ n).obj τ).representation
      ((phiPlus T ψ n).obj σ).representation := by
  letI := T.topology
  intro τ σ E hE
  refine
    { toLinearMap :=
        { toFun := phiPlusPostValue T ψ n E hE
          map_add' := ?_
          map_smul' := ?_ }
      isIntertwining' := ?_ }
  · intro φ η
    apply phiPlusNormalizedEval_injective T ψ n σ
    funext x
    change E (phiPlusNormalizedEval T ψ n τ φ x +
      phiPlusNormalizedEval T ψ n τ η x) =
      E (phiPlusNormalizedEval T ψ n τ φ x) +
        E (phiPlusNormalizedEval T ψ n τ η x)
    exact map_add E _ _
  · intro a φ
    apply phiPlusNormalizedEval_injective T ψ n σ
    funext x
    change E (a • phiPlusNormalizedEval T ψ n τ φ x) =
      a • E (phiPlusNormalizedEval T ψ n τ φ x)
    exact map_smul E a _
  · intro g
    apply LinearMap.ext
    intro φ
    apply phiPlusNormalizedEval_injective T ψ n σ
    funext x
    rfl

theorem phiPlusPost_eval (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)}
      {σ : SmoothRep.{0, uF, uW} ℂ (mirabolic n F.Carrier)}
      (E : Representation.IntertwiningMap τ.representation σ.representation)
      (hE : Function.Injective E) (φ : (phiPlus T ψ n).obj τ)
      (x : mirabolic (n + 1) F.Carrier),
      phiPlusNormalizedEval T ψ n σ (phiPlusPost T ψ n E hE φ) x =
        E (phiPlusNormalizedEval T ψ n τ φ x) := by
  intros
  rfl

theorem phiPlusPost_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)}
      {σ : SmoothRep.{0, uF, uW} ℂ (mirabolic n F.Carrier)}
      (E : Representation.IntertwiningMap τ.representation σ.representation)
      (hE : Function.Injective E),
      Function.Injective (phiPlusPost T ψ n E hE) := by
  let := T.topology
  intro τ σ E hE φ η heq
  apply phiPlusNormalizedEval_injective T ψ n τ
  funext x
  apply hE
  exact congrArg (fun f => phiPlusNormalizedEval T ψ n σ f x) heq

theorem mem_range_phiPlusPost (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)}
      {σ : SmoothRep.{0, uF, uW} ℂ (mirabolic n F.Carrier)}
      (E : Representation.IntertwiningMap τ.representation σ.representation)
      (hE : Function.Injective E) (φ : (phiPlus T ψ n).obj σ),
      φ ∈ (phiPlusPost T ψ n E hE).range ↔
        ∀ x, phiPlusNormalizedEval T ψ n σ φ x ∈ E.range := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1 + 1)
  intro τ σ E hE φ
  constructor
  · rintro ⟨η, rfl⟩ x
    exact ⟨phiPlusNormalizedEval T ψ n τ η x, rfl⟩
  · intro hφ
    choose f hf using hφ
    change ∀ x, E (f x) = phiPlusNormalizedEval T ψ n σ φ x at hf
    obtain ⟨K, hK⟩ := phiPlusNormalizedEval_exists_openSubgroup T ψ n σ φ
    have hcov : ∀ (q : plusSubgroup n F.Carrier) (x : mirabolic (n + 1) F.Carrier),
        f ((q : mirabolic (n + 1) F.Carrier) * x) =
          (thetaPlus ψ n q : ℂ) • (phiPlusCharacter T n (plusProjection q) : ℂ) •
            τ.representation (plusProjection q) (f x) := by
      intro q x
      apply hE
      rw [hf, map_smul, map_smul, E.isIntertwining, hf,
        phiPlusNormalizedEval_covariant]
    have hright : ∀ (k : K) (x : mirabolic (n + 1) F.Carrier),
        f (x * (k : mirabolic (n + 1) F.Carrier)) = f x := by
      intro k x
      apply hE
      rw [hf, hf, hK]
    have hs : Induction.quotientSupport (plusSubgroup n F.Carrier) f =
        Induction.quotientSupport (plusSubgroup n F.Carrier)
          (phiPlusNormalizedEval T ψ n σ φ) := by
      unfold Induction.quotientSupport
      congr 1
      ext x
      change f x ≠ 0 ↔ phiPlusNormalizedEval T ψ n σ φ x ≠ 0
      rw [← hf x, ← map_zero E, hE.ne_iff]
    have hc : IsCompact (Induction.quotientSupport (plusSubgroup n F.Carrier) f) := by
      rw [hs]
      exact phiPlusNormalizedEval_isCompact_quotientSupport T ψ n σ φ
    refine ⟨phiPlusNormalizedMk T ψ n τ f hcov K hright hc, ?_⟩
    apply phiPlusNormalizedEval_injective T ψ n σ
    funext x
    exact hf x

private def psiPlusBaseLinear (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
    (∀ (u : radical n F.Carrier) (v : A),
      A.representation (u : mirabolic n F.Carrier) v = v) →
    Jacquet.Localization.Coinvariants A.representation (radical n F.Carrier) 1 →ₗ[ℂ] A := by
  letI := T.topology
  intro A h
  exact Jacquet.Localization.lift A.representation (radical n F.Carrier) 1
    LinearMap.id (by intro u v; simpa using h u v)

/-- Inverse to the actual Psi-minus quotient when the radical acts trivially.
The positive and negative normalization characters cancel. -/
def psiPlusBaseEmbedding (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
    (∀ (u : radical n F.Carrier) (v : A),
      A.representation (u : mirabolic n F.Carrier) v = v) →
    Representation.IntertwiningMap
      ((psiPlus T n).obj ((psiMinus T n).obj A)).representation A.representation := by
  letI := T.topology
  intro A h
  refine
    { toLinearMap := psiPlusBaseLinear T n A h
      isIntertwining' := ?_ }
  intro g
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := psiMinusQuotient_surjective T n A x
  change psiPlusBaseLinear T n A h
    ((psiPlusCharacter T n (projection g) : ℂ) •
      (psiMinusCharacter T n (projection g) : ℂ) •
        psiMinusQuotient T n A (A.representation (levi (projection g)) v)) =
    A.representation g v
  rw [map_smul, map_smul]
  change (psiPlusCharacter T n (projection g) : ℂ) •
      (psiMinusCharacter T n (projection g) : ℂ) •
        A.representation (levi (projection g)) v = A.representation g v
  have hc : (psiPlusCharacter T n (projection g) : ℂ) *
      (psiMinusCharacter T n (projection g) : ℂ) = 1 := by
    have hh := congrArg (fun χ => χ (projection g))
      (psiPlusCharacter_mul_psiMinusCharacter T n)
    exact congrArg Units.val hh
  rw [smul_smul, hc, one_smul]
  conv_rhs => rw [eq_radicalElement_mul_levi g, map_mul, Module.End.mul_apply, h]

theorem psiPlusBaseEmbedding_quotient (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (h : ∀ (u : radical n F.Carrier) (v : A),
        A.representation (u : mirabolic n F.Carrier) v = v) (v : A),
      psiPlusBaseEmbedding T n A h (psiMinusQuotient T n A v) = v := by
  intros
  rfl

theorem psiMinusQuotient_psiPlusBaseEmbedding (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (h : ∀ (u : radical n F.Carrier) (v : A),
        A.representation (u : mirabolic n F.Carrier) v = v)
      (x : (psiMinus T n).obj A),
      psiMinusQuotient T n A (psiPlusBaseEmbedding T n A h x) = x := by
  let := T.topology
  intro A h x
  obtain ⟨v, rfl⟩ := psiMinusQuotient_surjective T n A x
  rfl

theorem psiPlusBaseEmbedding_injective (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (h : ∀ (u : radical n F.Carrier) (v : A),
        A.representation (u : mirabolic n F.Carrier) v = v),
      Function.Injective (psiPlusBaseEmbedding T n A h) := by
  let := T.topology
  intro A h x y heq
  have hh := congrArg (psiMinusQuotient T n A) heq
  change @Eq (Jacquet.Localization.Coinvariants A.representation (radical n F.Carrier) 1) x y
  simpa only [psiMinusQuotient_psiPlusBaseEmbedding] using hh

theorem psiPlusBaseEmbedding_range (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (h : ∀ (u : radical n F.Carrier) (v : A),
        A.representation (u : mirabolic n F.Carrier) v = v),
      (psiPlusBaseEmbedding T n A h).range = ⊤ := by
  let := T.topology
  intro A h
  apply top_unique
  intro v _
  exact ⟨psiMinusQuotient T n A v, psiPlusBaseEmbedding_quotient T n A h v⟩

end Langlands.Derivative.Mirabolic.HighestLayer
