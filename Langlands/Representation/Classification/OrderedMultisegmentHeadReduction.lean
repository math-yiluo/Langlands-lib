import Langlands.Representation.Classification.MultisegmentClassificationStatement
import Langlands.Representation.Classification.OrderedSegmentSquareIntegrableConversionStatement
import Langlands.Representation.Classification.TemperedBlockStatement
import Langlands.Representation.Classification.RegularLanglandsStatement
import Langlands.Representation.Induction.SingleBlock
import Mathlib.RingTheory.SimpleModule.Basic

/-! Rank-zero heads and conditional assembly for ordered segment products. -/

noncomputable section

namespace Langlands.Classification

universe uG uF uV

/-- A representation on a one-dimensional complex space is irreducible. -/
theorem isIrreducible_of_linearEquiv_complex {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] ℂ) :
    Representation.IsIrreducible ρ := by
  let : IsSimpleModule ℂ V := e.isSimpleModule_iff.mpr inferInstance
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤)
      (congrArg Subrepresentation.toSubmodule h)
  · intro S
    rcases eq_bot_or_eq_top S.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

/-- An irreducible representation is its own strong head, witnessed by identity. -/
theorem isIrreducibleHead_self {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    IsIrreducibleHead ρ ρ := by
  let := hρ
  refine ⟨hρ, Representation.IntertwiningMap.id ρ, Function.surjective_id, ?_⟩
  intro W _ _ π hπ q hq
  let := hπ
  have hqi : Function.Injective q := by
    rcases Representation.IsIrreducible.injective_or_eq_zero q with hi | hz
    · exact hi
    · have hzero : ∀ w : W, w = 0 := by
        intro w
        obtain ⟨v, rfl⟩ := hq w
        rw [hz]
        rfl
      let : Subsingleton W := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
      exact False.elim ((bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
        (Subrepresentation.ext (Subsingleton.elim _ _)))
  exact (LinearMap.ker_eq_bot.mpr hqi).trans
    (LinearMap.ker_eq_bot.mpr Function.injective_id).symm

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual normalized product for a rank-zero block shape has a carrier
linearly equivalent to the complex numbers. -/
def rankZeroNormalizedProductLinearEquiv (B : GeneralLinear.BlockShape 0)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup 0
    Induction.SmoothFunctions (B.parabolic F.Carrier)
      (twist (T.parabolicHalfModulus B)
        ((B.blockTensor σ).comp (B.leviProjection F.Carrier))) ≃ₗ[ℂ] ℂ := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup 0
  letI : IsEmpty (Fin B.length) := ⟨fun i =>
    Fin.elim0 (B.indexEquiv ⟨i, ⟨0, B.positive i⟩⟩)⟩
  let ρ := Representation.trivial ℂ (GeneralLinear 0 F.Carrier) (PiTensorProduct ℂ V)
  have hρ : IsSmooth ρ := by
    intro v
    exact ⟨⊤, fun _ => rfl⟩
  have hP : B.parabolic F.Carrier = ⊤ := by
    apply top_unique
    intro g _
    rw [Subsingleton.elim g 1]
    exact (B.parabolic F.Carrier).one_mem
  let e := Induction.smoothInducedTopEquiv (B.parabolic F.Carrier) hP
    (twist (T.parabolicHalfModulus B)
      ((B.blockTensor σ).comp (B.leviProjection F.Carrier))) ρ
    (by intro g; rw [Subsingleton.elim g 1, map_one]; rfl) hρ
  exact e.toLinearEquiv.trans (PiTensorProduct.isEmptyEquiv (R := ℂ) (s := V) _)

/-- Rank zero requires no ordering, analytic, or block-irreducibility hypothesis. -/
theorem rankZeroNormalizedProduct_isIrreducible (B : GeneralLinear.BlockShape 0)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    Representation.IsIrreducible (T.normalizedProductInduced B σ) :=
  isIrreducible_of_linearEquiv_complex _ (rankZeroNormalizedProductLinearEquiv F T B σ)

/-- The empty ordered segment product is its own strong Langlands head. -/
theorem orderedMultisegmentHead_rankZero
    (d : T.SegmentProductDatum.{max uF uV, uF} 0)
    (ho : d.IsPrecedenceOrdered) (hh : d.HasSegmentHeads) :
    d.IsLanglandsHead d.induced := by
  let := T.topology
  exact ⟨ho, hh, isIrreducibleHead_self _
    (rankZeroNormalizedProduct_isIrreducible F T d.shape
      (fun i => (d.blocks i).representation))⟩

/-- Conditional positive-rank assembly from grouping and the regular head theorem. -/
theorem squareIntegrableLanglandsHeadExistence_of_grouping
    (hg : SquareIntegrableEqualExponentGrouping.{uF, uV} F T)
    (hr : GLRegularLanglandsHeadExistenceStatement.{uF, uV}) :
    SquareIntegrableLanglandsHeadExistence.{uF, uV} F T := by
  let := T.topology
  intro n hn d
  obtain ⟨_, t, _, _, _, _, _, ⟨e⟩⟩ := hg n hn d
  obtain ⟨π, hπ⟩ := hr p F T n hn t
  exact ⟨π, IsIrreducibleHead.of_equiv (SmoothRep.equivOfIso e).symm hπ⟩

/-- Conditional all-rank assembly; rank zero is proved above. -/
theorem orderedMultisegmentHeadExistence_of_conversion
    (hc : OrderedSegmentSquareIntegrableConversion.{uF, uV} F T)
    (hh : SquareIntegrableLanglandsHeadExistence.{uF, uV} F T) :
    OrderedMultisegmentHeadExistence.{uF, uV} F T := by
  let := T.topology
  intro n d ho hs
  cases n with
  | zero => exact ⟨d.induced, orderedMultisegmentHead_rankZero F T d ho hs⟩
  | succ n =>
    obtain ⟨e, ⟨j⟩, _⟩ := hc (n + 1) (Nat.succ_pos n) d ho hs
    obtain ⟨π, hπ⟩ := hh (n + 1) (Nat.succ_pos n) e
    exact ⟨π, ho, hs, IsIrreducibleHead.of_equiv (SmoothRep.equivOfIso j).symm hπ⟩

/-- The three published prerequisite propositions suffice for the all-rank target.
This theorem retains all three as hypotheses. -/
theorem orderedMultisegmentHeadExistence_of_prerequisites
    (hc : OrderedSegmentSquareIntegrableConversion.{uF, uV} F T)
    (hg : SquareIntegrableEqualExponentGrouping.{uF, uV} F T)
    (hr : GLRegularLanglandsHeadExistenceStatement.{uF, uV}) :
    OrderedMultisegmentHeadExistence.{uF, uV} F T :=
  orderedMultisegmentHeadExistence_of_conversion F T hc
    (squareIntegrableLanglandsHeadExistence_of_grouping F T hg hr)

end Langlands.Classification
