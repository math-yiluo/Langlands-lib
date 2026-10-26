import Langlands.Representation.Classification.FiniteLengthStatement
import Langlands.LocalField.CanonicalProof
import Langlands.Representation.Parabolic.FlattenedJacquetQuotientProof
import Langlands.Representation.CuspidalSupport.InducedJacquetCount
import Langlands.Representation.CuspidalSupport.MinimalJacquetProof
import Langlands.Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof
import Langlands.Representation.CuspidalSupport.QuasicuspidalFiniteLengthProof
import Langlands.Representation.CuspidalSupport.RefinedJacquetLengthProof
import Langlands.Representation.Filtration.RepresentationLength
import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Induction.SingleBlock
import Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof
import Langlands.Representation.Parabolic.JacquetFiniteGenerationProof
import Langlands.Representation.Smooth.Admissibility.EmbeddingProof
import Mathlib.LinearAlgebra.Projection

/-!
Finite length of admissible finitely generated GL representations.
The proof inducts on the semisimple rank of standard product Levis.
-/

noncomputable section

open scoped MonoidAlgebra
open Representation

namespace Langlands.FiniteLengthAssembly

universe uK uG uH uV uW

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {H : Type uH} [Monoid H] {V : Type uV} [AddCommGroup V] [Module k V]
  {W : Type uW} [AddCommGroup W] [Module k W]

/-- A surjective change of acting monoid preserves the full module length. -/
theorem length_comp_surjective (ρ : Representation k G V) (f : H →* G)
    (hf : Function.Surjective f) :
    Module.length k[G] ρ.asModule =
      Module.length k[H] (Representation.asModule (ρ.comp f)) := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso
    (Subrepresentation.subrepresentationSubmoduleOrderIso.symm.trans
      ((CuspidalSupport.JacquetLength.compSubrepresentationOrderIso ρ f hf).trans
        Subrepresentation.subrepresentationSubmoduleOrderIso))

/-- Finite length can be transported in both directions along a surjection. -/
theorem finiteLength_comp_surjective_iff (ρ : Representation k G V) (f : H →* G)
    (hf : Function.Surjective f) :
    IsFiniteLength k[G] ρ.asModule ↔
      IsFiniteLength k[H] (Representation.asModule (ρ.comp f)) := by
  rw [← Module.length_ne_top_iff, ← Module.length_ne_top_iff,
    length_comp_surjective ρ f hf]

/-- A surjective intertwiner transfers finite generation to its target. -/
theorem finite_of_surjective {ρ : Representation k G V} {σ : Representation k G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    [Module.Finite k[G] ρ.asModule] : Module.Finite k[G] σ.asModule :=
  Module.Finite.of_surjective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f) hf

/-- A surjective intertwiner transfers finite length to its target. -/
theorem finiteLength_of_surjective {ρ : Representation k G V} {σ : Representation k G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (hρ : IsFiniteLength k[G] ρ.asModule) : IsFiniteLength k[G] σ.asModule :=
  hρ.of_surjective
    (f := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f) hf

/-- An injective intertwiner transfers finite length to its source. -/
theorem finiteLength_of_injective {ρ : Representation k G V} {σ : Representation k G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f)
    (hσ : IsFiniteLength k[G] σ.asModule) : IsFiniteLength k[G] ρ.asModule :=
  hσ.of_injective
    (f := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f) hf

/-- Projection along an invariant complement is an actual intertwiner. -/
def complementaryProjection (ρ : Representation k G V) (S Q : Subrepresentation ρ)
    (h : IsCompl S.toSubmodule Q.toSubmodule) : ρ.IntertwiningMap S.toRepresentation where
  toLinearMap := S.toSubmodule.projectionOnto Q.toSubmodule h
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    obtain ⟨s, q, rfl, _⟩ := Submodule.existsUnique_add_of_isCompl h v
    change S.toSubmodule.projectionOnto Q.toSubmodule h (ρ g ((s : V) + q)) =
      S.toRepresentation g (S.toSubmodule.projectionOnto Q.toSubmodule h ((s : V) + q))
    rw [map_add, map_add, map_add, Submodule.projectionOnto_apply_left,
      Submodule.projectionOnto_apply_right, add_zero,
      Submodule.projectionOnto_apply_of_mem_left h (S.apply_mem_toSubmodule g s.2),
      Submodule.projectionOnto_apply_of_mem_right h (Q.apply_mem_toSubmodule g q.2),
      add_zero]
    rfl

theorem complementaryProjection_surjective (ρ : Representation k G V)
    (S Q : Subrepresentation ρ) (h : IsCompl S.toSubmodule Q.toSubmodule) :
    Function.Surjective (complementaryProjection ρ S Q h) :=
  Submodule.projectionOnto_surjective h

/-- Finite generation passes to an invariant direct summand by projection. -/
theorem finite_summand (ρ : Representation k G V) (S Q : Subrepresentation ρ)
    (h : IsCompl S.toSubmodule Q.toSubmodule) [Module.Finite k[G] ρ.asModule] :
    Module.Finite k[G] S.toRepresentation.asModule :=
  finite_of_surjective (complementaryProjection ρ S Q h)
    (complementaryProjection_surjective ρ S Q h)

/-- Complementary invariant summands give an actual short exact sequence. -/
theorem length_eq_add_of_complement (ρ : Representation k G V)
    (S Q : Subrepresentation ρ) (h : IsCompl S.toSubmodule Q.toSubmodule) :
    repLength ρ = repLength S.toRepresentation + repLength Q.toRepresentation := by
  let i : S.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  refine repLength_eq_add_of_exact i (complementaryProjection ρ Q S h.symm)
    (Submodule.injective_subtype _) (complementaryProjection_surjective ρ Q S h.symm) ?_
  change LinearMap.range S.toSubmodule.subtype =
    LinearMap.ker (Q.toSubmodule.projectionOnto S.toSubmodule h.symm)
  rw [Submodule.range_subtype, Submodule.ker_projectionOnto]

/-- Finite length of both complementary summands gives finite length of the whole. -/
theorem finiteLength_of_complement (ρ : Representation k G V)
    (S Q : Subrepresentation ρ) (h : IsCompl S.toSubmodule Q.toSubmodule)
    (hS : IsFiniteLength k[G] S.toRepresentation.asModule)
    (hQ : IsFiniteLength k[G] Q.toRepresentation.asModule) :
    IsFiniteLength k[G] ρ.asModule := by
  rw [← Module.length_ne_top_iff] at hS hQ ⊢
  change repLength ρ ≠ ⊤
  rw [length_eq_add_of_complement ρ S Q h]
  simpa only [repLength, ne_eq, ENat.add_eq_top, not_or] using And.intro hS hQ

section Padic

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
  {X : Type uV} {Y : Type uW} [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

/-- The two published presentations of the normalized product-Levi action agree. -/
theorem normalizedJacquet_eq_twist
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) X) :
    T.normalizedJacquet B ρ =
      twist (Jacquet.inverseHalfCharacter (T.leviModulus B))
        (Parabolic.leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype)) := by
  apply MonoidHom.ext
  intro m
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := B.jacquetMk_surjective ρ v
  rw [T.normalizedJacquet_mk]
  change _ = (Jacquet.inverseHalfCharacter (T.leviModulus B) m : ℂ) •
    Parabolic.leviCoinvariants B (ρ.comp (B.parabolic F.Carrier).subtype)
      m (B.jacquetMk ρ w)
  rw [Jacquet.inverseHalfCharacter_apply]
  rfl

/-- Apply the published admissibility theorem to the standard Jacquet API. -/
theorem isAdmissible_normalizedJacquet :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) X), IsAdmissible ρ →
      IsAdmissible (T.normalizedJacquet B ρ) := by
  let := T.topology
  intro ρ hρ
  rw [normalizedJacquet_eq_twist T B ρ]
  exact Parabolic.normalizedJacquetAdmissibility F T B X ρ hρ

/-- Invariant subspaces inherit admissibility through their actual inclusion. -/
theorem isAdmissible_levi_subrepresentation :
    letI := T.topology
    ∀ (ρ : Representation ℂ (B.Levi F.Carrier) X) (S : Subrepresentation ρ),
      IsAdmissible ρ → IsAdmissible S.toRepresentation := by
  let := T.topology
  intro ρ S hρ
  let i : S.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  exact isAdmissible_of_injective i (Submodule.injective_subtype _) hρ

/-- Proper refinement strictly decreases the natural-number induction measure. -/
theorem refinement_measure_lt (R : Geometric.BlockRefinement B)
    (hR : Geometric.refinedParabolic F.Carrier B R ≠ ⊤) :
    n - (B.flatten R).length < n - B.length := by
  have hlt := B.length_lt_flatten R F.Carrier hR
  have hle := (B.flatten R).length_le
  omega

/-- The actual normalized refined Jacquet map preserves surjectivity. -/
theorem refinedJacquetMap_surjective (R : Geometric.BlockRefinement B)
    {ρ : Representation ℂ (B.Levi F.Carrier) X}
    {τ : Representation ℂ (B.Levi F.Carrier) Y}
    (f : ρ.IntertwiningMap τ) (hf : Function.Surjective f) :
    Function.Surjective (T.normalizedRefinedJacquetMap B R f) := by
  intro x
  obtain ⟨w, rfl⟩ := Jacquet.mk_surjective τ (Geometric.refinedUnipotent F.Carrier B R) x
  obtain ⟨v, rfl⟩ := hf w
  exact ⟨Geometric.refinedJacquetMk B R ρ v, rfl⟩

/-- The decomposition and detection theorems reduce finite length to the
proper refined Jacquet modules. -/
theorem finiteLength_of_refinedJacquet :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      A.IsAdmissible →
      Module.Finite ℂ[B.Levi F.Carrier] A.representation.asModule →
      (∀ R : Geometric.BlockRefinement B,
        Geometric.refinedParabolic F.Carrier B R ≠ ⊤ →
          IsFiniteLength ℂ[Geometric.refinedLevi F.Carrier B R]
            (T.normalizedRefinedJacquet B R A.representation).asModule) →
      IsFiniteLength ℂ[B.Levi F.Carrier] A.representation.asModule := by
  let := T.topology
  intro A hA hfg hJ
  let : Module.Finite ℂ[B.Levi F.Carrier] A.representation.asModule := hfg
  obtain ⟨S, Q, hcompl, hS, hQ⟩ :=
    CuspidalSupport.leviQuasicuspidalDecomposition F T B A
  have hSf : IsFiniteLength ℂ[B.Levi F.Carrier] S.toRepresentation.asModule :=
    CuspidalSupport.leviQuasicuspidalFiniteLength p F T n B
      (SmoothRep.subrepresentation A S)
      (isAdmissible_levi_subrepresentation T B A.representation S hA) hS
      (finite_summand A.representation S Q hcompl)
  have hQf : IsFiniteLength ℂ[B.Levi F.Carrier] Q.toRepresentation.asModule := by
    apply CuspidalSupport.refinedJacquetFiniteLengthDetection p F T n B
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
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) X),
      IsAdmissible ρ →
      Module.Finite ℂ[GeneralLinear n F.Carrier] ρ.asModule →
      (∀ R : Geometric.BlockRefinement B,
        Geometric.refinedParabolic F.Carrier B R ≠ ⊤ →
          IsFiniteLength ℂ[Geometric.refinedLevi F.Carrier B R]
            (T.normalizedRefinedJacquet B R (T.normalizedJacquet B ρ)).asModule) →
      IsFiniteLength ℂ[B.Levi F.Carrier] (T.normalizedJacquet B ρ).asModule := by
  let := T.topology
  intro ρ hρ hfg hJ
  exact finiteLength_of_refinedJacquet T B
    (SmoothRep.of (T.normalizedJacquet B ρ) (T.isSmooth_normalizedJacquet B hρ.1))
    (isAdmissible_normalizedJacquet T B ρ hρ)
    (Parabolic.normalizedJacquetFiniteGeneration p F T n B X ρ hρ.1 hfg) hJ

/-- In one block the quotient map is equivariant for the original Levi action. -/
def singleBlockJacquetInclusion (hB : B.length = 1)
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) X) :
    Representation.IntertwiningMap (ρ.comp (B.leviEmbedding F.Carrier))
      (T.normalizedJacquet B ρ) where
  toLinearMap := B.jacquetMk ρ
  isIntertwining' m := by
    apply LinearMap.ext
    intro v
    change B.jacquetMk ρ (ρ (B.leviEmbedding F.Carrier m) v) =
      T.normalizedJacquet B ρ m (B.jacquetMk ρ v)
    rw [T.normalizedJacquet_mk_eq_inv_halfModulus,
      T.singleBlock_leviHalfModulus B hB, inv_one, one_smul]

theorem singleBlockJacquetInclusion_injective (hB : B.length = 1)
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) X) :
    Function.Injective (singleBlockJacquetInclusion T B hB ρ) :=
  B.jacquetMk_injective_of_length_le_one F.Carrier hB.le ρ

/-- Finite length of a one-block normalized Jacquet module gives finite length
of the original representation, with no smoothness assumption needed here. -/
theorem finiteLength_of_singleBlockJacquet (hB : B.length = 1)
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) X)
    (hJ : IsFiniteLength ℂ[B.Levi F.Carrier] (T.normalizedJacquet B ρ).asModule) :
    IsFiniteLength ℂ[GeneralLinear n F.Carrier] ρ.asModule := by
  apply (finiteLength_comp_surjective_iff ρ (B.leviEmbedding F.Carrier)
    (B.singleBlock_leviEmbedding_surjective hB F.Carrier)).mpr
  exact finiteLength_of_injective (singleBlockJacquetInclusion T B hB ρ)
    (singleBlockJacquetInclusion_injective T B hB ρ) hJ

end Padic

end Langlands.FiniteLengthAssembly


namespace Langlands.Parabolic

open FiniteLengthAssembly

universe uF uV

/-- Every standard normalized Jacquet module of an admissible finitely generated
ambient GL representation has finite length over the actual product-Levi group
algebra, including rank zero and arbitrary independent carrier universes. -/
theorem normalizedJacquetFiniteLength
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    {X : Type uV} [AddCommGroup X] [Module ℂ X] :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear n F.Carrier) X),
      IsAdmissible ρ →
      Module.Finite ℂ[GeneralLinear n F.Carrier] ρ.asModule →
      IsFiniteLength ℂ[B.Levi F.Carrier] (T.normalizedJacquet B ρ).asModule := by
  let := T.topology
  intro ρ hρ hfg
  suffices h : ∀ d : ℕ, ∀ C : GeneralLinear.BlockShape n,
      n - C.length = d →
      IsFiniteLength ℂ[C.Levi F.Carrier] (T.normalizedJacquet C ρ).asModule from
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
    obtain ⟨f, _, hf⟩ := flattenedJacquetQuotient p F T n C R X ρ
    exact (finiteLength_comp_surjective_iff
      (T.normalizedRefinedJacquet C R (T.normalizedJacquet C ρ))
      (Geometric.flattenedLeviEquiv F.Carrier C R).toMonoidHom
      (Geometric.flattenedLeviEquiv F.Carrier C R).surjective).mpr
        (finiteLength_of_surjective f hf hflat)

end Langlands.Parabolic

namespace Langlands

universe uF uV

/-- An admissible finitely generated representation of positive-rank GL over
an actual finite extension of Q_p has finite group-algebra length. -/
theorem glAdmissibleFiniteLength : GLAdmissibleFiniteLengthStatement.{uF,uV} := by
  intro p _ F
  let := F.canonicalTopology
  intro n hn X _ _ ρ hρ hfg
  let B : GeneralLinear.BlockShape n := ⟨1, fun _ => n, fun _ => hn, by simp⟩
  apply FiniteLengthAssembly.finiteLength_of_singleBlockJacquet
    F.canonicalTopologicalData B rfl ρ
  have hJ := Parabolic.normalizedJacquetFiniteLength F.canonicalTopologicalData B (X := X)
  rw [PadicField.canonicalTopologicalData_topology] at hJ
  exact hJ ρ hρ hfg

end Langlands
