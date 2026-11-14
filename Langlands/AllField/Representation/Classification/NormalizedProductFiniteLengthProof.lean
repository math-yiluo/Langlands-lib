import Langlands.Representation.Classification.NormalizedProductFiniteLengthProof
import Langlands.AllField.Representation.Classification.IrreducibleProductFiniteLengthProof
import Langlands.AllField.Representation.Parabolic.InductionExactnessProof
import Langlands.AllField.Representation.Tensor.FactorMatchingProof
/-! Finite-length preservation for actual normalized induction. -/

noncomputable section

namespace Langlands.AllField.Classification.ProductLengthProof
open Langlands.Classification.ProductLengthProof hiding irreducibleLevi leviPreservation step
open Langlands.AllField.Classification.ProductLengthProof
open Langlands.Classification hiding AdmissibleFiniteLengthProductPreservation IrreducibleProductEmbeddingTheorem IrreducibleProductFiniteLength admissibleFiniteLengthProductPreservation irreducibleProductEmbedding irreducibleProductFiniteLength irreducibleProduct_embedding irreducible_supercuspidalProduct_embedding normalizedInductionFiniteLength normalizedProduct_embedding_of_factor_embeddings
open Langlands.AllField.Classification

universe uG uV uW uX uF

section Generic


end Generic

section Padic

variable (F : Type uF) [Field F]
  (T : LocalFieldData F) {n : ℕ} (hn : 0 < n) (B : GeneralLinear.BlockShape n)

include hn in
theorem irreducibleLevi :
    letI := T.topology
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (B.Levi F) V),
    IsAdmissible σ → Representation.IsIrreducible σ →
    IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F))
      (T.normalizedParabolicInduced B σ).asModule := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro V _ _ σ ha hi
  obtain ⟨A, hAi, _, ⟨e⟩⟩ := Langlands.AllField.CuspidalSupport.padicLeviAdmissibleFactorization
    F T n hn B (SmoothRep.of σ ha.1) hi ha
  have hA := irreducibleProductFiniteLength.{uF,uV} F T n hn B A hAi
  let e' := T.normalizedParabolicInducedEquiv B e
  exact finiteLength_of_injective e'.toIntertwiningMap e'.injective hA

include hn in
theorem step :
    letI := T.topology
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (B.Levi F) V} (_ha : IsAdmissible ρ)
    (S R : Subrepresentation ρ) (_hSR : S ⋖ R)
    (_hS : IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F))
      (T.normalizedParabolicInduced B S.toRepresentation).asModule),
    IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F))
      (T.normalizedParabolicInduced B R.toRepresentation).asModule := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let := T.leviTopologicalGroup B
  intro V _ _ ρ ha S R hSR hS
  let i : S.toRepresentation.IntertwiningMap R.toRepresentation :=
    { toLinearMap := Submodule.inclusion hSR.le
      isIntertwining' g := by ext v; rfl }
  let j : R.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := R.toSubmodule.subtype
      isIntertwining' g := by ext v; rfl }
  let τ := LengthCriterionProof.quotientRep S R
  let q : R.toRepresentation.IntertwiningMap τ :=
    { toLinearMap := (LengthCriterionProof.lower S R).mkQ
      isIntertwining' g := by ext v; rfl }
  have hRa := isAdmissible_of_injective j (Submodule.injective_subtype _) ha
  have hSa := isAdmissible_of_injective i (Submodule.inclusion_injective hSR.le) hRa
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hτa : IsAdmissible τ :=
    Unramified.SphericalExistence.isAdmissible_of_surjective (fun H => by
      obtain ⟨K, hK, hKH⟩ := Langlands.AllField.CuspidalSupport.levi_exists_compact_openSubgroup_subset
        T B H (H.isOpen.mem_nhds H.one_mem)
      exact ⟨K, hK, hKH⟩) q hq hRa
  have hτi : Representation.IsIrreducible τ :=
    (LengthCriterionProof.isIrreducible_quotientRep_iff hSR.le).mpr hSR
  have hτ := irreducibleLevi F T hn B τ hτa hτi
  have he : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap := by
    ext v
    change (∃ w : S.toSubmodule, i w = v) ↔
      Submodule.Quotient.mk (p := LengthCriterionProof.lower S R) v = 0
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨w, rfl⟩
      exact w.property
    · intro hv
      exact ⟨⟨v.1, hv⟩, rfl⟩
  have h := Langlands.AllField.Parabolic.normalizedInductionExactness F T B
    S.toSubmodule R.toSubmodule (R.toSubmodule ⧸ LengthCriterionProof.lower S R)
    S.toRepresentation R.toRepresentation τ i q hSa.1 hRa.1 hτa.1
    (Submodule.inclusion_injective hSR.le) hq he
  exact finiteLength_of_range_eq_ker
    (T.normalizedParabolicInducedMap B i) (T.normalizedParabolicInducedMap B q)
    h.2.1 hS hτ

include hn in
theorem leviPreservation :
    letI := T.topology
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F) V) (_ha : IsAdmissible ρ)
    (_hl : IsFiniteLength (MonoidAlgebra ℂ (B.Levi F)) ρ.asModule),
    IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F))
      (T.normalizedParabolicInduced B ρ).asModule := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro V _ _ ρ ha hl
  obtain ⟨s, h₀, h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp hl
  obtain ⟨f, hf⟩ :=
    LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries (A := Rep.of ρ) s h₀ h₁
  have hcov := (LengthCriterionProof.hasSimpleFactors_iff_covBy f).mp hf
  have hstep : ∀ i, IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F))
      (T.normalizedParabolicInduced B (f.subrepresentation i).toRepresentation).asModule := by
    intro i
    induction i using Fin.induction with
    | zero =>
      rw [f.subrepresentation_zero]
      have : Subsingleton (T.normalizedParabolicInduced B
          (⊥ : Subrepresentation ρ).toRepresentation).asModule := by
        refine ⟨fun x y => ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        funext g
        apply Subtype.ext
        exact (show (x.1.1 g).1 = 0 from (x.1.1 g).2).trans
          (show (y.1.1 g).1 = 0 from (y.1.1 g).2).symm
      exact .of_subsingleton
    | succ i ih =>
      exact step F T hn B ha _ _ (hcov i) ih
  have htop := hstep (Fin.last s.length)
  rw [f.subrepresentation_last] at htop
  let e : (⊤ : Subrepresentation ρ).toRepresentation.Equiv ρ :=
    Representation.Equiv.mk Submodule.topEquiv (fun g => by ext v; rfl)
  let e' := T.normalizedParabolicInducedEquiv B e
  exact finiteLength_of_surjective e'.toIntertwiningMap e'.surjective htop

end Padic

end Langlands.AllField.Classification.ProductLengthProof

namespace Langlands.AllField.Classification
open Langlands.Classification hiding AdmissibleFiniteLengthProductPreservation IrreducibleProductEmbeddingTheorem IrreducibleProductFiniteLength admissibleFiniteLengthProductPreservation irreducibleProductEmbedding irreducibleProductFiniteLength irreducibleProduct_embedding irreducible_supercuspidalProduct_embedding normalizedInductionFiniteLength normalizedProduct_embedding_of_factor_embeddings
open Langlands.AllField.Classification

universe uF uV

/-- Normalized induction of an arbitrary admissible finite-length standard-Levi
representation has finite group-algebra length at positive total rank. -/
theorem normalizedInductionFiniteLength 
    (F : Type uF) [Field F] (T : LocalFieldData F) {n : ℕ} (hn : 0 < n)
    (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F) V),
    IsAdmissible ρ →
    IsFiniteLength (MonoidAlgebra ℂ (B.Levi F)) ρ.asModule →
    IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F))
      (T.normalizedParabolicInduced B ρ).asModule :=
  Langlands.AllField.Classification.ProductLengthProof.leviPreservation F T hn B

/-- The complete admissible finite-length block-product preservation statement. -/
theorem admissibleFiniteLengthProductPreservation 
    (F : Type uF) [Field F] (T : LocalFieldData F) :
    AdmissibleFiniteLengthProductPreservation.{uF,uV} F T := by
  let := T.topology
  intro n hn B A hA
  have hmatch := Langlands.AllField.FiniteTensor.padicExternalTensorFactors F T n hn B A A
    (fun i => (hA i).1) (fun i => (hA i).1)
    (fun i => ProductLengthProof.selfMatching_of_finiteLength (hA i).2)
  obtain ⟨m, s, _, hs, _, _⟩ := hmatch
  have htensor := LengthCriterionProof.isFiniteLength_of_hasCompositionSeriesLength ⟨s, hs⟩
  have ha := FiniteTensor.isAdmissible_external (fun i => (A i).representation)
    (fun i => (hA i).1)
  exact normalizedInductionFiniteLength F T hn B _ ha htensor

end Langlands.AllField.Classification
