import Langlands.Representation.Classification.FiniteLengthProof
import Langlands.AllField.Representation.Classification.FiniteLengthStatement
import Langlands.AllField.Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof
import Langlands.AllField.Representation.CuspidalSupport.QuasicuspidalFiniteLengthProof
import Langlands.AllField.Representation.CuspidalSupport.RefinedJacquetLengthProof
import Langlands.AllField.Representation.Induction.SingleBlock
import Langlands.AllField.Representation.Parabolic.FlattenedJacquetQuotientProof
import Langlands.AllField.Representation.Parabolic.JacquetFiniteGenerationProof
import Langlands.AllField.Representation.Parabolic.NormalizedJacquetAdmissibilityProof
/-!
Finite length of admissible finitely generated GL representations.
The proof inducts on the semisimple rank of standard product Levis.
-/

noncomputable section

open scoped MonoidAlgebra
open Representation

namespace Langlands.AllField.FiniteLengthAssembly
open Langlands.FiniteLengthAssembly hiding finiteLength_normalizedJacquet_of_refinements finiteLength_of_refinedJacquet finiteLength_of_singleBlockJacquet isAdmissible_levi_subrepresentation isAdmissible_normalizedJacquet normalizedJacquet_eq_twist refinedJacquetMap_surjective refinement_measure_lt singleBlockJacquetInclusion singleBlockJacquetInclusion_injective
open Langlands.AllField.FiniteLengthAssembly

universe uK uG uH uV uW

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {H : Type uH} [Monoid H] {V : Type uV} [AddCommGroup V] [Module k V]
  {W : Type uW} [AddCommGroup W] [Module k W]

section Padic

universe uF

variable {F : Type uF} [Field F]
  (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
  {X : Type uV} {Y : Type uW} [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

/-- The two published presentations of the normalized product-Levi action agree. -/
theorem normalizedJacquet_eq_twist
    (ρ : Representation ℂ (GeneralLinear n F) X) :
    T.normalizedJacquet B ρ =
      twist (Jacquet.inverseHalfCharacter (T.leviModulus B))
        (Parabolic.leviCoinvariants B (ρ.comp (B.parabolic F).subtype)) := by
  apply MonoidHom.ext
  intro m
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := B.jacquetMk_surjective ρ v
  rw [T.normalizedJacquet_mk]
  change _ = (Jacquet.inverseHalfCharacter (T.leviModulus B) m : ℂ) •
    Parabolic.leviCoinvariants B (ρ.comp (B.parabolic F).subtype)
      m (B.jacquetMk ρ w)
  rw [Jacquet.inverseHalfCharacter_apply]
  rfl

/-- Apply the published admissibility theorem to the standard Jacquet API. -/
theorem isAdmissible_normalizedJacquet :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear n F) X), IsAdmissible ρ →
      IsAdmissible (T.normalizedJacquet B ρ) := by
  let := T.topology
  intro ρ hρ
  rw [normalizedJacquet_eq_twist T B ρ]
  exact Parabolic.normalizedJacquetAdmissibility F T B X ρ hρ

/-- Invariant subspaces inherit admissibility through their actual inclusion. -/
theorem isAdmissible_levi_subrepresentation :
    letI := T.topology
    ∀ (ρ : Representation ℂ (B.Levi F) X) (S : Subrepresentation ρ),
      IsAdmissible ρ → IsAdmissible S.toRepresentation := by
  let := T.topology
  intro ρ S hρ
  let i : S.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  exact isAdmissible_of_injective i (Submodule.injective_subtype _) hρ

/-- Proper refinement strictly decreases the natural-number induction measure. -/
theorem refinement_measure_lt (R : Geometric.BlockRefinement B)
    (hR : Geometric.refinedParabolic F B R ≠ ⊤) :
    n - (B.flatten R).length < n - B.length := by
  have hlt := B.length_lt_flatten R F hR
  have hle := (B.flatten R).length_le
  omega

/-- The actual normalized refined Jacquet map preserves surjectivity. -/
theorem refinedJacquetMap_surjective (R : Geometric.BlockRefinement B)
    {ρ : Representation ℂ (B.Levi F) X}
    {τ : Representation ℂ (B.Levi F) Y}
    (f : ρ.IntertwiningMap τ) (hf : Function.Surjective f) :
    Function.Surjective (T.normalizedRefinedJacquetMap B R f) := by
  intro x
  obtain ⟨w, rfl⟩ := Jacquet.mk_surjective τ (Geometric.refinedUnipotent F B R) x
  obtain ⟨v, rfl⟩ := hf w
  exact ⟨Geometric.refinedJacquetMk B R ρ v, rfl⟩

/-- The decomposition and detection theorems reduce finite length to the
proper refined Jacquet modules. -/
theorem finiteLength_of_refinedJacquet :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F)),
      A.IsAdmissible →
      Module.Finite ℂ[B.Levi F] A.representation.asModule →
      (∀ R : Geometric.BlockRefinement B,
        Geometric.refinedParabolic F B R ≠ ⊤ →
          IsFiniteLength ℂ[Geometric.refinedLevi F B R]
            (T.normalizedRefinedJacquet B R A.representation).asModule) →
      IsFiniteLength ℂ[B.Levi F] A.representation.asModule := by
  let := T.topology
  intro A hA hfg hJ
  let : Module.Finite ℂ[B.Levi F] A.representation.asModule := hfg
  obtain ⟨S, Q, hcompl, hS, hQ⟩ :=
    CuspidalSupport.leviQuasicuspidalDecomposition F T B A
  have hSf : IsFiniteLength ℂ[B.Levi F] S.toRepresentation.asModule :=
    CuspidalSupport.leviQuasicuspidalFiniteLength F T n B
      (SmoothRep.subrepresentation A S)
      (isAdmissible_levi_subrepresentation T B A.representation S hA) hS
      (finite_summand A.representation S Q hcompl)
  have hQf : IsFiniteLength ℂ[B.Levi F] Q.toRepresentation.asModule := by
    apply CuspidalSupport.refinedJacquetFiniteLengthDetection F T n B
      (SmoothRep.subrepresentation A Q) hQ
    intro R hR
    let q := complementaryProjection A.representation Q S hcompl.symm
    exact finiteLength_of_surjective (T.normalizedRefinedJacquetMap B R q)
      (refinedJacquetMap_surjective T B R q
        (complementaryProjection_surjective A.representation Q S hcompl.symm))
      (hJ R hR)
  exact finiteLength_of_complement A.representation S Q hcompl hSf hQf

/-- For a standard Jacquet module, the published admissibility and
finite-generation results discharge both inputs of the decomposition step. -/
theorem finiteLength_normalizedJacquet_of_refinements :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear n F) X),
      IsAdmissible ρ →
      Module.Finite ℂ[GeneralLinear n F] ρ.asModule →
      (∀ R : Geometric.BlockRefinement B,
        Geometric.refinedParabolic F B R ≠ ⊤ →
          IsFiniteLength ℂ[Geometric.refinedLevi F B R]
            (T.normalizedRefinedJacquet B R (T.normalizedJacquet B ρ)).asModule) →
      IsFiniteLength ℂ[B.Levi F] (T.normalizedJacquet B ρ).asModule := by
  let := T.topology
  intro ρ hρ hfg hJ
  exact finiteLength_of_refinedJacquet T B
    (SmoothRep.of (T.normalizedJacquet B ρ) (T.isSmooth_normalizedJacquet B hρ.1))
    (isAdmissible_normalizedJacquet T B ρ hρ)
    (Parabolic.normalizedJacquetFiniteGeneration F T n B X ρ hρ.1 hfg) hJ

/-- In one block the quotient map is equivariant for the original Levi action. -/
def singleBlockJacquetInclusion (hB : B.length = 1)
    (ρ : Representation ℂ (GeneralLinear n F) X) :
    Representation.IntertwiningMap (ρ.comp (B.leviEmbedding F))
      (T.normalizedJacquet B ρ) where
  toLinearMap := B.jacquetMk ρ
  isIntertwining' m := by
    apply LinearMap.ext
    intro v
    change B.jacquetMk ρ (ρ (B.leviEmbedding F m) v) =
      T.normalizedJacquet B ρ m (B.jacquetMk ρ v)
    rw [T.normalizedJacquet_mk_eq_inv_halfModulus,
      T.singleBlock_leviHalfModulus B hB, inv_one, one_smul]

theorem singleBlockJacquetInclusion_injective (hB : B.length = 1)
    (ρ : Representation ℂ (GeneralLinear n F) X) :
    Function.Injective (singleBlockJacquetInclusion T B hB ρ) :=
  B.jacquetMk_injective_of_length_le_one F hB.le ρ

/-- Finite length of a one-block normalized Jacquet module gives finite length
of the original representation, with no smoothness assumption needed here. -/
theorem finiteLength_of_singleBlockJacquet (hB : B.length = 1)
    (ρ : Representation ℂ (GeneralLinear n F) X)
    (hJ : IsFiniteLength ℂ[B.Levi F] (T.normalizedJacquet B ρ).asModule) :
    IsFiniteLength ℂ[GeneralLinear n F] ρ.asModule := by
  apply (finiteLength_comp_surjective_iff ρ (B.leviEmbedding F)
    (B.singleBlock_leviEmbedding_surjective hB F)).mpr
  exact finiteLength_of_injective (singleBlockJacquetInclusion T B hB ρ)
    (singleBlockJacquetInclusion_injective T B hB ρ) hJ

end Padic

end Langlands.AllField.FiniteLengthAssembly

namespace Langlands.AllField.Parabolic
open Langlands.Parabolic hiding FlattenedJacquetQuotientStatement NormalizedJacquetAdmissibilityClause NormalizedJacquetFiniteGenerationStatement ParabolicQuotientCompactClause UnipotentFiniteContainmentClause exists_iwahori_levi_subset flattenJacquetMap_action_mk flattenJacquetMap_equivariant flattenJacquetMap_equivariant_mk flattenJacquetMap_mk flattenedJacquetQuotient flattenedJacquetQuotientMap isAdmissible_leviCoinvariants isCompact_integralRange isSmooth_leviCoinvariants jacquetModuleEquiv_leviCoinvariants normalizedIteratedJacquet_mk normalizedJacquetAdmissibility normalizedJacquetFiniteGeneration normalizedJacquetFiniteLength parabolicQuotientCompact quotientMap_image_integralRange unipotentFiniteContainment
open Langlands.AllField.Parabolic

open Langlands.FiniteLengthAssembly hiding finiteLength_normalizedJacquet_of_refinements finiteLength_of_refinedJacquet finiteLength_of_singleBlockJacquet isAdmissible_levi_subrepresentation isAdmissible_normalizedJacquet normalizedJacquet_eq_twist refinedJacquetMap_surjective refinement_measure_lt singleBlockJacquetInclusion singleBlockJacquetInclusion_injective
open Langlands.AllField.FiniteLengthAssembly

universe uF uV

/-- Every standard normalized Jacquet module of an admissible finitely generated
ambient GL representation has finite length over the actual product-Levi group
algebra, including rank zero and arbitrary independent carrier universes. -/
theorem normalizedJacquetFiniteLength
    {F : Type uF} [Field F]
    (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
    {X : Type uV} [AddCommGroup X] [Module ℂ X] :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear n F) X),
      IsAdmissible ρ →
      Module.Finite ℂ[GeneralLinear n F] ρ.asModule →
      IsFiniteLength ℂ[B.Levi F] (T.normalizedJacquet B ρ).asModule := by
  let := T.topology
  intro ρ hρ hfg
  suffices h : ∀ d : ℕ, ∀ C : GeneralLinear.BlockShape n,
      n - C.length = d →
      IsFiniteLength ℂ[C.Levi F] (T.normalizedJacquet C ρ).asModule from
    h _ B rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro C hC
    apply finiteLength_normalizedJacquet_of_refinements T C ρ hρ hfg
    intro R hR
    have hlt : n - (C.flatten R).length < d := by
      rw [← hC]
      exact refinement_measure_lt (F := F) C R hR
    have hflat := ih _ hlt (C.flatten R) rfl
    obtain ⟨f, _, hf⟩ := flattenedJacquetQuotient F T n C R X ρ
    exact (finiteLength_comp_surjective_iff
      (T.normalizedRefinedJacquet C R (T.normalizedJacquet C ρ))
      (Geometric.flattenedLeviEquiv F C R).toMonoidHom
      (Geometric.flattenedLeviEquiv F C R).surjective).mpr
        (finiteLength_of_surjective f hf hflat)

end Langlands.AllField.Parabolic

namespace Langlands.AllField

universe uF uV

/-- An admissible finitely generated representation of positive-rank GL over
an actual nonarchimedean local field has finite group-algebra length. -/
theorem glAdmissibleFiniteLength : GLAdmissibleFiniteLengthStatement.{uF,uV} := by
  intro F _ T
  let := T.topology
  intro n hn X _ _ ρ hρ hfg
  let B : GeneralLinear.BlockShape n := ⟨1, fun _ => n, fun _ => hn, by simp⟩
  apply FiniteLengthAssembly.finiteLength_of_singleBlockJacquet
    T B rfl ρ
  have hJ := Parabolic.normalizedJacquetFiniteLength T B (X := X)
  exact hJ ρ hρ hfg

end Langlands.AllField
