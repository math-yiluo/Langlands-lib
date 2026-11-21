import Langlands.Automorphic.CuspidalArithmeticSpectralTransportProof
import Langlands.Automorphic.CuspidalSpectralDeterminantTwist

/-! # The unramified spectrum of the cyclic character-twisted block sum -/

noncomputable section

open scoped BigOperators

universe uE uV

set_option autoImplicit false

namespace Langlands.TraceFormula.CyclicBlockSum

open Langlands.Automorphic Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Unramified

variable {E : Type uE} [Field E] [NumberField E]

/-- Inverse arithmetic pullback for block `α`; the class in this block is
`σ^α Π`. The place convention is the one in `cuspidalArithmeticSpectralTransport`. -/
def blockPullback {d : ℕ} (σ : E ≃+* E) (α : Fin d) : E ≃+* E :=
  (σ ^ α.val).symm

/-- The finite place from which the block takes its eigenvalues. -/
def blockSourcePlace {d : ℕ} (σ : E ≃+* E) (α : Fin d) : FinitePlace E ≃ FinitePlace E :=
  (finitePlaceEquiv (blockPullback σ α)).symm

private theorem not_mem_map_symm {I : Type*} (e : I ≃ I) (T : Finset I) {v : I}
    (hv : v ∉ T.map e.symm.toEmbedding) : e v ∉ T := by
  intro h
  exact hv (Finset.mem_map.mpr ⟨e v, h, e.symm_apply_apply v⟩)

/-- The individual reindexed Satake block, before scaling by its character. -/
def blockPullbackSystem {b d : ℕ} (σ : E ≃+* E) (α : Fin d)
    (s : SpectralSystem (FinitePlace E) b) : SpectralSystem (FinitePlace E) b where
  exceptional := s.exceptional.map (blockSourcePlace σ α).symm.toEmbedding
  eigenvalues v hv := s.eigenvalues (blockSourcePlace σ α v)
    (not_mem_map_symm (blockSourcePlace σ α) _ hv)

/-- The `α` block of the Hecke system: take the Satake data at `σ^(−α) v` and
scale by the local uniformizer value of `η_α`. -/
def twistedHeckeBlock {b d : ℕ} (σ : E ≃+* E) (η : Fin d → HeckeCharacter E)
    (s : SpectralSystem (FinitePlace E) b) (α : Fin d) :
    SpectralSystem (FinitePlace E) b :=
  SpectralSystem.scale (η α).finiteUniformizerValue (blockPullbackSystem σ α s)

/-- The transferred numerical system on the `d` blocks. -/
def twistedBlockSystem {b d : ℕ} (σ : E ≃+* E) (η : Fin d → HeckeCharacter E)
    (s : SpectralSystem (FinitePlace E) b) :
    SpectralSystem (FinitePlace E) (∑ _ : Fin d, b) :=
  SpectralSystem.finiteSum (twistedHeckeBlock σ η s)

theorem twistedHeckeBlock_eulerPolynomial {b d : ℕ} (σ : E ≃+* E)
    (η : Fin d → HeckeCharacter E) (s : SpectralSystem (FinitePlace E) b) (α : Fin d)
    (v : FinitePlace E) (hv : v ∉ (twistedHeckeBlock σ η s α).exceptional) :
    (twistedHeckeBlock σ η s α).eulerPolynomial v hv =
      (s.eulerPolynomial (blockSourcePlace σ α v)
        (not_mem_map_symm (blockSourcePlace σ α) _ hv)).comp
        (Polynomial.C ((η α).finiteUniformizerValue v : ℂ) * Polynomial.X) :=
  SpectralSystem.scale_eulerPolynomial _ _ _ _

section Actual

variable [CompactSpace (AdeleQuotient E)]
variable {d m b : ℕ} (σ : E ≃+* E) (η : Fin d → HeckeCharacter E)
  (hη : ∀ α, (η α).HasFiniteOrder)

/-- Actual cuspidal classes of the transfer, indexed by a block and a
constituent of the original Hecke support. Multiplicities are not discarded. -/
def twistedBlockConstituent (c : Fin m → PositiveRankCuspidalClass E)
    (a : Fin d × Fin m) : PositiveRankCuspidalClass E :=
  ((c a.2).arithmeticComap (blockPullback σ a.1)).determinantTwist (η a.1) (hη a.1)

/-- Any specified Satake block has genuine attached cuspidal support, by
transport and determinant twist on each actual constituent of the input. -/
theorem exists_twistedHeckeBlock_support
    (c : Fin m → PositiveRankCuspidalClass E)
    (t : ∀ j, SpectralSystem (FinitePlace E) (c j).rank)
    (ht : ∀ j, PositiveRankCuspidalClass.HasSpectralSystem.{uE, uV} (c j) (t j))
    (s : SpectralSystem (FinitePlace E) b)
    (hs : (SpectralSystem.finiteSum t).SameEulerPolynomials s) (α : Fin d) :
    ∃ u : ∀ j : Fin m, SpectralSystem (FinitePlace E) (twistedBlockConstituent σ η hη c (α,j)).rank,
      (∀ j, PositiveRankCuspidalClass.HasSpectralSystem.{uE, uV}
        (twistedBlockConstituent σ η hη c (α,j)) (u j)) ∧
      (SpectralSystem.finiteSum u).SameEulerPolynomials (twistedHeckeBlock σ η s α) := by
  classical
  choose t' ht' hlocal using fun j =>
    cuspidalArithmeticSpectralTransport.{uE, uE, uV}
      E E (blockPullback σ α) (c j).1 (c j).2 (t j) (ht j)
  let u : ∀ j : Fin m, SpectralSystem (FinitePlace E) (twistedBlockConstituent σ η hη c (α,j)).rank :=
    fun j => (SpectralSystem.scale (η α).finiteUniformizerValue (t' j)).restrict
      ((t' j).exceptional ∪ (η α).finiteDeterminantTail (c j).rank (hη α))
      Finset.subset_union_left
  refine ⟨u, fun j => PositiveRankCuspidalClass.HasSpectralSystem.determinantTwist
    (c := (c j).arithmeticComap (blockPullback σ α)) (ht' j) (η α) (hη α), ?_⟩
  have hw : Filter.Tendsto (blockSourcePlace σ α) Filter.cofinite Filter.cofinite :=
    (blockSourcePlace σ α).injective.tendsto_cofinite
  have hloc := Filter.eventually_all.mpr hlocal
  filter_upwards [hloc, hw.eventually hs,
    hw.eventually (SpectralSystem.familyExceptional t).eventually_cofinite_notMem]
    with v hloc hs hv₀
  intro hv hv'
  refine (SpectralSystem.finiteSum_eulerPolynomial u v hv).trans ?_
  refine Eq.trans ?_ (twistedHeckeBlock_eulerPolynomial σ η s α v hv').symm
  rw [← hs hv₀ (not_mem_map_symm (blockSourcePlace σ α) _ hv'),
    SpectralSystem.finiteSum_eulerPolynomial t _ hv₀, Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun j _ => ?_
  have h₁ : v ∉ (t' j).exceptional := fun h =>
    SpectralSystem.not_mem_exceptional u v hv j (Finset.mem_union_left _ h)
  refine (SpectralSystem.scale_eulerPolynomial (η α).finiteUniformizerValue (t' j) v h₁).trans ?_
  exact congrArg
    (fun P : Polynomial ℂ =>
      P.comp (Polynomial.C ((η α).finiteUniformizerValue v : ℂ) * Polynomial.X))
    (hloc j h₁ (SpectralSystem.not_mem_exceptional t _ hv₀ j))

/-- Flatten the transferred blocks to one family of actually attached support.
This works for repeated constituents, in particular a normalized residual string
or inducing data, whenever their individual cuspidal attachments are supplied. -/
theorem exists_twistedBlockSystem_support
    (c : Fin m → PositiveRankCuspidalClass E)
    (t : ∀ j, SpectralSystem (FinitePlace E) (c j).rank)
    (ht : ∀ j, PositiveRankCuspidalClass.HasSpectralSystem.{uE, uV} (c j) (t j))
    (s : SpectralSystem (FinitePlace E) b)
    (hs : (SpectralSystem.finiteSum t).SameEulerPolynomials s) :
    ∃ u : ∀ a : Fin d × Fin m, SpectralSystem (FinitePlace E) (twistedBlockConstituent σ η hη c a).rank,
      (∀ a, PositiveRankCuspidalClass.HasSpectralSystem.{uE, uV}
        (twistedBlockConstituent σ η hη c a) (u a)) ∧
      (SpectralSystem.finiteSum u).SameEulerPolynomials (twistedBlockSystem σ η s) := by
  classical
  choose u hu he using exists_twistedHeckeBlock_support σ η hη c t ht s hs
  let u' := fun a : Fin d × Fin m => u a.1 a.2
  refine ⟨u', fun a => hu a.1 a.2, ?_⟩
  have h := Filter.eventually_all.mpr he
  filter_upwards [h, Filter.eventually_all.mpr
      (fun α => (SpectralSystem.familyExceptional (u α)).eventually_cofinite_notMem)]
    with v h hall
  intro hv hv'
  refine (SpectralSystem.finiteSum_eulerPolynomial u' v hv).trans ?_
  refine Eq.trans ?_
    (SpectralSystem.finiteSum_eulerPolynomial (twistedHeckeBlock σ η s) v hv').symm
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun α _ => ?_
  refine Eq.trans ?_ (h α (hall α) _)
  exact (SpectralSystem.finiteSum_eulerPolynomial (u α) v (hall α)).symm

end Actual

end Langlands.TraceFormula.CyclicBlockSum
