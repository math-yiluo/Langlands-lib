import Langlands.Representation.Derivative.MirabolicHighestLayerPlus

/-! # Proof of the actual highest mirabolic layer

For a representation `A` of `P_(n+j+1)` of level `j + 1`, the highest layer is the
invariant subspace obtained from `A` by `j` lifts through `Φ⁻` steps, starting from the
whole of `(Φ⁻)^j A`. It is the image of an injective intertwining map from
`(Φ⁺)^j Ψ⁺ (A^(j+1))`, its invariant subspaces correspond to those of the derivative
`A^(j+1)`, and it meets an invariant subspace exactly when that subspace has a nonzero
derivative of order `j + 1`.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.Mirabolic.HighestLayer

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis RankinSelberg Topology
open Jacquet.Localization

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-! ## The plus model of the layer -/

section Model

variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The iterated normalized plus induction `(Φ⁺)^(j+1) (Ψ⁺ D)` of a representation `D`
of `GL_n`, a representation of `P_(n+j+2)`. -/
def plusLayerSucc (n : ℕ) :
    letI := T.topology
    (j : ℕ) → SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) →
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (n + j + 1) F.Carrier) := by
  letI := T.topology
  intro j
  induction j with
  | zero => exact fun D => (phiPlus T ψ n).obj ((psiPlus T n).obj D)
  | succ j ih => exact fun D => (phiPlus T ψ (n + j + 1)).obj (ih D)

theorem plusLayerSucc_zero (n : ℕ) :
    letI := T.topology
    ∀ D : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      plusLayerSucc T ψ n 0 D = (phiPlus T ψ n).obj ((psiPlus T n).obj D) :=
  fun _ => rfl

theorem plusLayerSucc_succ (n j : ℕ) :
    letI := T.topology
    ∀ D : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      plusLayerSucc T ψ n (j + 1) D = (phiPlus T ψ (n + j + 1)).obj (plusLayerSucc T ψ n j D) :=
  fun _ => rfl

/-- `U` is the range of an injective intertwining map into `A` from
`(Φ⁺)^j Ψ⁺ (A^(j+1))`, where `A^(j+1) = Ψ⁻ (Φ⁻)^j A` is the derivative of order `j + 1`
of the representation `A` of `P_(n+j+1)`. For `j = 0` the source is `Ψ⁺ (Ψ⁻ A)`. -/
def IsPlusLayerImage (n : ℕ) :
    letI := T.topology
    (j : ℕ) → (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + j) F.Carrier)) →
      Subrepresentation A.representation → Prop := by
  letI := T.topology
  intro j
  cases j with
  | zero =>
    exact fun A U => ∃ E : Representation.IntertwiningMap
        ((psiPlus T n).obj ((mirabolicDerivative T ψ n 0).obj A)).representation
        A.representation, Function.Injective E ∧ E.range = U
  | succ j =>
    exact fun A U => ∃ E : Representation.IntertwiningMap
        (plusLayerSucc T ψ n j ((mirabolicDerivative T ψ n (j + 1)).obj A)).representation
        A.representation, Function.Injective E ∧ E.range = U

theorem isPlusLayerImage_zero (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 0) F.Carrier))
      (U : Subrepresentation A.representation),
      IsPlusLayerImage T ψ n 0 A U ↔
        ∃ E : Representation.IntertwiningMap
          ((psiPlus T n).obj ((mirabolicDerivative T ψ n 0).obj A)).representation
          A.representation, Function.Injective E ∧ E.range = U :=
  fun _ _ => Iff.rfl

theorem isPlusLayerImage_succ (n j : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + (j + 1)) F.Carrier))
      (U : Subrepresentation A.representation),
      IsPlusLayerImage T ψ n (j + 1) A U ↔
        ∃ E : Representation.IntertwiningMap
          (plusLayerSucc T ψ n j ((mirabolicDerivative T ψ n (j + 1)).obj A)).representation
          A.representation, Function.Injective E ∧ E.range = U :=
  fun _ _ => Iff.rfl

/-- The whole of a representation on which the radical acts trivially is the image of
`Ψ⁺ (Ψ⁻ A)`. -/
theorem isPlusLayerImage_top (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 0) F.Carrier),
      (∀ (u : radical n F.Carrier) (v : A), A.representation (u : mirabolic n F.Carrier) v = v) →
        IsPlusLayerImage T ψ n 0 A ⊤ := by
  let := T.topology
  intro A h
  exact ⟨psiPlusBaseEmbedding T n A h, psiPlusBaseEmbedding_injective T n A h,
    psiPlusBaseEmbedding_range T n A h⟩

/-- On objects, the derivative of order `j + 2` is the derivative of order `j + 1` of
`Φ⁻`. -/
theorem derivative_obj_succ (n j : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + (j + 1)) F.Carrier),
      (mirabolicDerivative T ψ n (j + 1)).obj A =
        (mirabolicDerivative T ψ n j).obj ((phiMinus T ψ (n + j)).obj A) :=
  fun _ => rfl

/-- One `Φ⁻` step lifts a plus image to a plus image. -/
theorem isPlusLayerImage_liftStep (n j : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + (j + 1)) F.Carrier))
      (U' : Subrepresentation ((phiMinus T ψ (n + j)).obj A).representation),
      IsPlusLayerImage T ψ n j ((phiMinus T ψ (n + j)).obj A) U' →
        IsPlusLayerImage T ψ n (j + 1) A (liftStep T ψ (n + j) A U') := by
  let := T.topology
  intro A U' hU'
  rw [isPlusLayerImage_succ, derivative_obj_succ]
  cases j with
  | zero =>
    rw [isPlusLayerImage_zero] at hU'
    obtain ⟨E, hE, hrange⟩ := hU'
    obtain ⟨E', hE', hrange'⟩ := exists_plusStep T ψ (n + 0) A E hE
    have hφ : phiPlus.{uV, uF} T ψ (n + 0) = phiPlus T ψ n := rfl
    rw [plusLayerSucc_zero, ← hφ]
    exact ⟨E', hE', hrange'.trans (congrArg (liftStep T ψ (n + 0) A) hrange)⟩
  | succ j =>
    rw [isPlusLayerImage_succ] at hU'
    obtain ⟨E, hE, hrange⟩ := hU'
    obtain ⟨E', hE', hrange'⟩ := exists_plusStep T ψ (n + (j + 1)) A E hE
    have hφ : phiPlus.{max uF uV, uF} T ψ (n + (j + 1)) = phiPlus T ψ (n + j + 1) := rfl
    rw [plusLayerSucc_succ, ← hφ]
    exact ⟨E', hE', hrange'.trans (congrArg (liftStep T ψ (n + (j + 1)) A) hrange)⟩

end Model

/-! ## The layer, by induction on the order -/

section Layer

variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The highest layer of a representation of level `j + 1`, with the derivative read
through the decomposition of the rank as `n + j`. -/
theorem exists_layer (j : ℕ) :
    letI := T.topology
    ∀ (n : ℕ) (A : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + j) F.Carrier)),
      level T ψ A = j + 1 →
        ∃ U : Subrepresentation A.representation, U ≠ ⊥ ∧
          Nonempty (Subrepresentation ((mirabolicDerivative T ψ n j).obj A).representation ≃o
            Set.Iic U) ∧
          (∀ S : Subrepresentation A.representation,
            (Nontrivial ((mirabolicDerivative T ψ n j).obj (SmoothRep.subrepresentation A S)) ↔
              U ⊓ S ≠ ⊥)) ∧
          IsPlusLayerImage T ψ n j A U := by
  let := T.topology
  induction j with
  | zero =>
    intro n A hA
    have hrad := radical_trivial_of_level_le_one T ψ n A (by omega)
    have := LevelCalculus.nontrivial_of_level_ne_zero T ψ A (by omega)
    refine ⟨⊤, LevelCalculus.top_ne_bot,
      ⟨(psiIso T n A hrad).symm.trans OrderIso.IicTop.symm⟩, fun S => ?_,
      isPlusLayerImage_top T ψ n A hrad⟩
    rw [top_inf_eq]
    have hradS := radical_trivial_subrepresentation T n A hrad S
    exact (nontrivial_iff_of_bijective _ (psiMinusQuotient_injective T n _ hradS)
      (psiMinusQuotient_surjective T n _)).symm.trans (nontrivial_subrepresentation_iff A S)
  | succ j ih =>
    intro n A hA
    have hpos : 0 < level T ψ ((phiMinus T ψ (n + j)).obj A) := by
      have h1 := LevelCalculus.hasNonzeroDerivative_level T ψ A (by omega)
      rw [hA] at h1
      have h2 := (LevelCalculus.hasNonzeroDerivative_succ_iff (M := n + j) T ψ A
        (k := j + 1) (by omega)).mp h1
      have := le_level_of_hasNonzeroDerivative T ψ _ h2
      omega
    have hlev := LevelCalculus.level_eq_level_phiMinus_succ (M := n + j) T ψ A hpos
    obtain ⟨U', hU', ⟨e'⟩, hS', hplus'⟩ := ih n ((phiMinus T ψ (n + j)).obj A) (by omega)
    refine ⟨liftStep T ψ (n + j) A U', ?_, ⟨e'.trans (stepIso T ψ (n + j) A U').symm⟩,
      fun S => ?_, isPlusLayerImage_liftStep T ψ n j A U' hplus'⟩
    · intro h
      apply hU'
      rw [← imageStep_liftStep T ψ (n + j) A U', h, imageStep_bot]
    · change Nontrivial ((mirabolicDerivative T ψ n j).obj
        ((phiMinus T ψ (n + j)).obj (SmoothRep.subrepresentation A S))) ↔ _
      rw [LevelCalculus.nontrivial_iff_of_iso
        ((mirabolicDerivative T ψ n j).mapIso (phiMinusSubIso T ψ (n + j) A S)), hS',
        inf_imageStep_ne_bot_iff]

/-- Reading the derivative through two equal decompositions of the rank. -/
theorem derivative_cast {N n n' j j' : ℕ} (hn : n = n') (hj : j = j') (h : N = n + j)
    (h' : N = n' + j') :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier),
      Nonempty (Subrepresentation
          ((mirabolicDerivative T ψ n j).obj ((mirabolicRankCast T h).obj A)).representation ≃o
        Subrepresentation
          ((mirabolicDerivative T ψ n' j').obj
            ((mirabolicRankCast T h').obj A)).representation) := by
  subst hn hj
  intro A
  exact ⟨OrderIso.refl _⟩

end Layer

end Langlands.Derivative.Mirabolic.HighestLayer

namespace Langlands.Derivative

universe uF uV

/-- The actual highest layer of a representation `A` of `P_(n+j+1)` of level `j + 1`:
a nonzero invariant subspace `U` whose invariant subspaces correspond to those of the
derivative of order `j + 1`, which meets every nonzero invariant subspace exactly when `A`
is homogeneous, and which is the range of an injective intertwining map into `A` from
`(Φ⁺)^j Ψ⁺ (A^(j+1))`. -/
theorem mirabolicHighestLayer_plusModel {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) :
    letI := T.topology
    ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n j : ℕ)
      (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear.mirabolic (n + j) F.Carrier))
      (hk : 0 < j + 1 ∧ j + 1 ≤ n + j + 1),
      j + 1 = level T ψ A →
        ∃ U : Subrepresentation A.representation,
          U ≠ ⊥ ∧
          Nonempty (Subrepresentation
            ((mirabolicDerivativeOfOrder T ψ (n + j) (j + 1) hk).obj A).representation ≃o
              Set.Iic U) ∧
          (IsHomogeneous T ψ A ↔
            ∀ S : Subrepresentation A.representation, S ≠ ⊥ → U ⊓ S ≠ ⊥) ∧
          Mirabolic.HighestLayer.IsPlusLayerImage T ψ n j A U := by
  let := T.topology
  intro ψ n j A hk hlev
  obtain ⟨U, hU, ⟨e⟩, hS, hplus⟩ := Mirabolic.HighestLayer.exists_layer T ψ j n A hlev.symm
  obtain ⟨e₀⟩ := Mirabolic.HighestLayer.derivative_cast T ψ (n' := n) (j' := j) (by omega)
    (by omega) (mirabolic_rank_eq_of_order hk) rfl A
  have hnz : ∀ S : Subrepresentation A.representation,
      HasNonzeroDerivative T ψ (SmoothRep.subrepresentation A S) (j + 1) ↔ U ⊓ S ≠ ⊥ :=
    fun S => (LevelCalculus.hasNonzeroDerivative_succ_iff_cast T ψ rfl _).trans (hS S)
  refine ⟨U, hU, ⟨e₀.trans e⟩, ?_, hplus⟩
  rw [isHomogeneous_iff T ψ A]
  constructor
  · intro hhom S hS0
    apply (hnz S).mp
    have h1 := hhom S hS0
    rw [← hlev] at h1
    have h2 := LevelCalculus.hasNonzeroDerivative_level T ψ (SmoothRep.subrepresentation A S)
      (by omega)
    rwa [h1] at h2
  · intro h S hS0
    have h1 := le_level_of_hasNonzeroDerivative T ψ _ ((hnz S).mpr (h S hS0))
    have h2 := Mirabolic.HighestLayer.level_subrepresentation_le T ψ A S
    omega

/-- The actual highest mirabolic layer, its derivative lattice and the homogeneity
criterion. -/
theorem mirabolicHighestLayer {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : MirabolicHighestLayerStatement.{uF, uV} F T := by
  let := T.topology
  intro ψ N A k hk _ hlev
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + j := ⟨N - j, by omega⟩
  obtain ⟨U, hU, he, hhom, -⟩ := mirabolicHighestLayer_plusModel F T ψ n j A hk hlev
  exact ⟨U, hU, he, hhom⟩

end Langlands.Derivative
