import Langlands.Automorphic.OperatorLieAction
import Langlands.Automorphic.CuspidalOperatorRealization
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Infinitesimal characters and the regular algebraic type at infinity

Clozel (1990), Définitions 1.8 and 3.12, as used by Harris (1998, p.185) for
`Reg(n,E)`: the center of the complexified enveloping algebra acts on an actual
automorphic realization through the infinitesimal character of an irreducible
algebraic representation of `∏_σ GL_n(ℂ)`, that is, through the central
character of a highest-weight vector of dominant integral weight.
-/

noncomputable section

universe u

open NumberField NumberField.InfinitePlace

open scoped Classical

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Indices of the complex embeddings of `K`: one for each real place, and two
for each complex place (the place's coordinate and its complex conjugate). -/
abbrev EmbeddingIndex :=
  {w : InfinitePlace K // IsReal w} ⊕ ({w : InfinitePlace K // IsComplex w} × Bool)

/-- The coordinate of the archimedean ring `K ⊗ ℝ` at an embedding index. -/
def embeddingComponent : EmbeddingIndex K → mixedEmbedding.mixedSpace K →ₐ[ℝ] ℂ
  | .inl w => Complex.ofRealAm.comp
      ((Pi.evalAlgHom (R := ℝ) (A := fun _ => ℝ) w).comp (AlgHom.fst ℝ _ _))
  | .inr (w, false) => (Pi.evalAlgHom (R := ℝ) (A := fun _ => ℂ) w).comp (AlgHom.snd ℝ _ _)
  | .inr (w, true) => Complex.conjAe.toAlgHom.comp
      ((Pi.evalAlgHom (R := ℝ) (A := fun _ => ℂ) w).comp (AlgHom.snd ℝ _ _))

omit [NumberField K] in
@[simp]
theorem embeddingComponent_inl (w : {w : InfinitePlace K // IsReal w})
    (x : mixedEmbedding.mixedSpace K) :
    embeddingComponent K (.inl w) x = (x.1 w : ℂ) := rfl

omit [NumberField K] in
@[simp]
theorem embeddingComponent_inr_false (w : {w : InfinitePlace K // IsComplex w})
    (x : mixedEmbedding.mixedSpace K) :
    embeddingComponent K (.inr (w, false)) x = x.2 w := rfl

omit [NumberField K] in
@[simp]
theorem embeddingComponent_inr_true (w : {w : InfinitePlace K // IsComplex w})
    (x : mixedEmbedding.mixedSpace K) :
    embeddingComponent K (.inr (w, true)) x = (starRingEnd ℂ) (x.2 w) := rfl

/-- The value of a weight `μ` on the complexified diagonal matrix `1 ⊗ diag(d)`,
whose component at the embedding index `j` is `diag(σ_j(d_1), …, σ_j(d_n))`. -/
def diagonalWeight (μ : EmbeddingIndex K → Fin n → ℂ)
    (d : Fin n → mixedEmbedding.mixedSpace K) : ℂ :=
  ∑ j, ∑ i, μ j i * embeddingComponent K j (d i)

/-- The complexification `1 ⊗ X` of a real archimedean matrix, as an element of
the enveloping algebra. -/
def realGenerator (X : ArchimedeanMatrix K n) : EnvelopingAlgebra K n :=
  envelopingGenerator K n (complexify K n ((realLieAlgebraToMatrix K n).symm X))

/-- `w` is a highest-weight vector of weight `μ` for the Borel subalgebra of
upper triangular matrices: it is nonzero, the diagonal matrices act on it through
`μ`, and the strictly upper triangular matrices kill it. -/
def IsHighestWeightVector {W : ModuleCat.{u} (EnvelopingAlgebra K n)}
    (μ : EmbeddingIndex K → Fin n → ℂ) (w : W) : Prop :=
  w ≠ 0 ∧
    (∀ d : Fin n → mixedEmbedding.mixedSpace K,
      realGenerator K n (Matrix.diagonal d) • w =
        algebraMap ℂ (EnvelopingAlgebra K n) (diagonalWeight K n μ d) • w) ∧
    ∀ i j : Fin n, i < j → ∀ a : mixedEmbedding.mixedSpace K,
      realGenerator K n (Matrix.single i j a) • w = 0

/-- `χ` is the infinitesimal character of highest weight `μ`: the center of the
enveloping algebra acts through `χ` on a highest-weight vector of weight `μ`. -/
def IsHighestWeightCharacter (μ : EmbeddingIndex K → Fin n → ℂ)
    (χ : EnvelopingCenter K n →ₐ[ℂ] ℂ) : Prop :=
  ∃ (W : ModuleCat.{u} (EnvelopingAlgebra K n)) (w : W),
    IsHighestWeightVector K n μ w ∧
      ∀ z : EnvelopingCenter K n,
        (z : EnvelopingAlgebra K n) • w = algebraMap ℂ (EnvelopingAlgebra K n) (χ z) • w

/-- Clozel's regular algebraic infinitesimal characters: those of the irreducible
algebraic representations of `∏_σ GL_n(ℂ)`, whose highest weights are the integral
weights that are dominant (nonincreasing) for the upper triangular Borel subalgebra
at every embedding index. -/
def IsRegularAlgebraicCharacter (χ : EnvelopingCenter K n →ₐ[ℂ] ℂ) : Prop :=
  ∃ μ : EmbeddingIndex K → Fin n → ℤ,
    (∀ j, Antitone (μ j)) ∧ IsHighestWeightCharacter K n (fun j i => (μ j i : ℂ)) χ

section Trivial

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The augmentation character of the enveloping algebra: every element of the
complex Lie algebra acts by `0`. -/
def augmentation : EnvelopingAlgebra K n →ₐ[ℂ] ℂ :=
  UniversalEnvelopingAlgebra.lift ℂ (0 : ComplexLieAlgebra K n →ₗ⁅ℂ⁆ ℂ)

omit [NumberField K] in
@[simp]
theorem augmentation_envelopingGenerator (X : ComplexLieAlgebra K n) :
    augmentation K n (envelopingGenerator K n X) = 0 := by
  simp [augmentation, envelopingGenerator]

/-- The trivial representation of the enveloping algebra, on `ULift ℂ`. -/
def trivialModule : ModuleCat.{u} (EnvelopingAlgebra K n) :=
  letI : Module (EnvelopingAlgebra K n) (ULift.{u} ℂ) :=
    Module.compHom (ULift.{u} ℂ) (augmentation K n).toRingHom
  ModuleCat.of (EnvelopingAlgebra K n) (ULift.{u} ℂ)

/-- The vector `1` of the trivial representation. -/
def trivialVector : trivialModule K n := (ULift.up 1 : ULift.{u} ℂ)

omit [NumberField K] in
/-- The enveloping algebra acts on the trivial representation through the
augmentation. -/
theorem trivialModule_smul (a : EnvelopingAlgebra K n) (w : trivialModule K n) :
    a • w = (ULift.up (augmentation K n a * (ULift.down w)) : ULift.{u} ℂ) := rfl

/-- The trivial representation has a highest-weight vector of weight `0`. -/
theorem isHighestWeightVector_trivial :
    IsHighestWeightVector K n (fun _ _ => 0) (trivialVector K n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact one_ne_zero (congrArg ULift.down h)
  · intro d
    rw [trivialModule_smul, trivialModule_smul]
    simp [realGenerator, diagonalWeight]
    rfl
  · intro i j _ a
    rw [trivialModule_smul]
    simp [realGenerator]
    rfl

/-- Non-vacuity: the infinitesimal character of the trivial representation,
the augmentation restricted to the center, is regular algebraic, with highest
weight `0`. -/
theorem isRegularAlgebraicCharacter_augmentation :
    IsRegularAlgebraicCharacter K n ((augmentation K n).comp (centerInclusion K n)) := by
  refine ⟨fun _ _ => 0, fun _ => antitone_const, trivialModule K n,
    trivialVector K n, ?_, ?_⟩
  · simpa using isHighestWeightVector_trivial K n
  · intro z
    rw [trivialModule_smul, trivialModule_smul]
    simp
    rfl

end Trivial

end Langlands.Global.ArchimedeanGL

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance regularAlgebraicRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance regularAlgebraicContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance regularAlgebraicSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance regularAlgebraicFormsAddCommGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance regularAlgebraicStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization F n)

local instance regularAlgebraicSpaceAddCommGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance regularAlgebraicSpaceAddCommGroup' : AddCommGroup T.Space :=
  Submodule.addCommGroup _

/-- The center of the enveloping algebra acts on the realization by the scalars `χ`. -/
def HasInfinitesimalCharacter (χ : ArchimedeanGL.EnvelopingCenter F n →ₐ[ℂ] ℂ) : Prop :=
  ∀ (z : ArchimedeanGL.EnvelopingCenter F n) (f : S.Space),
    S.envelopingAction (z : ArchimedeanGL.EnvelopingAlgebra F n) f = χ z • f

/-- Clozel's regular algebraic type at infinity: the realization has the
infinitesimal character of an irreducible algebraic representation. -/
def IsRegularAlgebraic : Prop :=
  ∃ χ : ArchimedeanGL.EnvelopingCenter F n →ₐ[ℂ] ℂ,
    ArchimedeanGL.IsRegularAlgebraicCharacter F n χ ∧ S.HasInfinitesimalCharacter χ

variable {S T}

/-- A realization with a nonzero vector has at most one infinitesimal character. -/
theorem HasInfinitesimalCharacter.unique {f : S.Space} (hf : f ≠ 0)
    {χ χ' : ArchimedeanGL.EnvelopingCenter F n →ₐ[ℂ] ℂ}
    (h : S.HasInfinitesimalCharacter χ) (h' : S.HasInfinitesimalCharacter χ') : χ = χ' := by
  ext z
  exact smul_left_injective ℂ hf
    (show (fun c : ℂ => c • f) (χ z) = (fun c : ℂ => c • f) (χ' z) from
      (h z f).symm.trans (h' z f))

set_option maxHeartbeats 2000000 in
/-- The infinitesimal character is transported along full-operator equivalences. -/
theorem HasInfinitesimalCharacter.of_equivalence (e : S.Equivalence T)
    {χ : ArchimedeanGL.EnvelopingCenter F n →ₐ[ℂ] ℂ}
    (h : S.HasInfinitesimalCharacter χ) : T.HasInfinitesimalCharacter χ := by
  intro z f
  have hd := Intertwiner.differential e.toIntertwiningMap
    (z : ArchimedeanGL.EnvelopingAlgebra F n) (e.symm f)
  have hs : e.toIntertwiningMap (χ z • e.symm f) = χ z • e.toIntertwiningMap (e.symm f) :=
    map_smul e.toIntertwiningMap.toLinearMap (χ z) (e.symm f)
  have hf : e.toIntertwiningMap (e.symm f) = f := by
    rw [Representation.Equiv.coe_toIntertwiningMap]
    exact e.apply_symm_apply f
  rw [h z (e.symm f), hs, hf] at hd
  exact hd.symm

/-- Equivalent realizations have the same infinitesimal characters. -/
theorem hasInfinitesimalCharacter_iff_of_equivalence (e : S.Equivalence T)
    (χ : ArchimedeanGL.EnvelopingCenter F n →ₐ[ℂ] ℂ) :
    S.HasInfinitesimalCharacter χ ↔ T.HasInfinitesimalCharacter χ :=
  ⟨HasInfinitesimalCharacter.of_equivalence e, HasInfinitesimalCharacter.of_equivalence e.symm⟩

/-- The regular algebraic type is invariant under full-operator equivalence. -/
theorem isRegularAlgebraic_iff_of_equivalence (e : S.Equivalence T) :
    S.IsRegularAlgebraic ↔ T.IsRegularAlgebraic := by
  simp only [IsRegularAlgebraic, hasInfinitesimalCharacter_iff_of_equivalence e]

/-- A full-operator class has regular algebraic type when some representative has. -/
def IsoClass.IsRegularAlgebraic (c : IsoClass F n) : Prop :=
  ∃ S : OperatorRealization F n, S.isoClass = c ∧ S.IsRegularAlgebraic

/-- For a class, one representative has regular algebraic type exactly when every
representative has. -/
theorem isoClass_isRegularAlgebraic_iff (S : OperatorRealization F n) :
    S.isoClass.IsRegularAlgebraic ↔ S.IsRegularAlgebraic := by
  constructor
  · rintro ⟨T, hT, hTS⟩
    obtain ⟨e⟩ := (T.isoClass_eq_iff S).mp hT
    exact (isRegularAlgebraic_iff_of_equivalence e).mp hTS
  · intro h
    exact ⟨S, rfl, h⟩

end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- An irreducible cuspidal class has regular algebraic type (Clozel's
`Alg ∩ Reg`, Harris's `Reg(r+1, F)` for a cuspidal class) when its full-operator
class has. -/
def IsoClass.IsRegularAlgebraic (c : IsoClass F r) : Prop :=
  c.toOperatorClass.IsRegularAlgebraic

theorem isoClass_isRegularAlgebraic_iff (S : CuspidalOperatorRealization F r) :
    S.isoClass.IsRegularAlgebraic ↔ S.realization.IsRegularAlgebraic :=
  S.realization.isoClass_isRegularAlgebraic_iff

end CuspidalOperatorRealization

end Langlands.Automorphic
