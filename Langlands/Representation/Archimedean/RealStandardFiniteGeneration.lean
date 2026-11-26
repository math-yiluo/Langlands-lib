import Langlands.Representation.Archimedean.RealJacquetFiniteGenerationProof
import Langlands.Representation.Archimedean.RealLanglandsFromPrincipalSeriesProof
import Langlands.Representation.Archimedean.RealStandardIrreducibleCriterionProof
import Langlands.Representation.Archimedean.RealStandardFiltration

/-! # Finite generation of real standard modules under matrix derivatives -/

noncomputable section

open scoped TensorProduct Matrix
open Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealStandardFiniteGeneration

open RealJacquetFiniteGeneration (op wordOp wordSpan)
open RealStandardFiltration (KF IsFiltration)

variable {n : ℕ}

/-- A finite-dimensional subspace generates the standard module under words in real matrix
directions. -/
def HasFiniteDerivativeGenerators (n : ℕ) (ds : List RealBlock) : Prop :=
  ∃ F : Submodule ℂ (KF n ds), FiniteDimensional ℂ F ∧ wordSpan (realStandardLie n ds) F = ⊤

private theorem le_wordSpan (ds : List RealBlock) (F : Submodule ℂ (KF n ds)) :
    F ≤ wordSpan (realStandardLie n ds) F := by
  intro f hf
  have hh : wordOp (realStandardLie n ds) [] f ∈ wordSpan (realStandardLie n ds) F :=
    RealJacquetFiniteGeneration.wordOp_apply_mem_wordSpan [] hf
  simpa using hh

theorem of_ordered {ds : List RealBlock} (hrank : realRank ds = n)
    (hord : IsRealLanglandsOrdered ds) : HasFiniteDerivativeGenerators n ds := by
  obtain ⟨R, _, hR, hmax⟩ := realLeviLanglandsQuotient realLeviChartIntegrable realLeviParabolicIntegration
    realTemperedStandardIrreducible n ds hrank hord
  obtain ⟨v, hv⟩ : ∃ v : KF n ds, v ∉ R := by
    by_contra! hv
    exact hR (Submodule.eq_top_iff'.mpr hv)
  let F := FiniteVectors.orbitSpan (realStandardRep n ds) v
  have hGK := isRealGKModule_realStandardModule n ds
  refine ⟨F, hGK.1 v, ?_⟩
  let S := wordSpan (realStandardLie n ds) F
  have hF (k : Matrix.unitaryGroup (Fin n) ℝ) (f : KF n ds) (hf : f ∈ F) :
      realStandardRep n ds k f ∈ F :=
    (FiniteVectors.orbitSubrepresentation (realStandardRep n ds) v).apply_mem_toSubmodule k hf
  have hS : IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) S :=
    ⟨fun k f hf => RealJacquetFiniteGeneration.rho_mem_wordSpan hGK hF k hf,
      fun X _ hf => RealJacquetFiniteGeneration.apply_mem_wordSpan X hf⟩
  by_contra hproper
  exact hv (hmax S hS hproper (le_wordSpan ds F (FiniteVectors.self_mem_orbitSpan _ v)))

theorem of_filtration {ι : Type} [Fintype ι] [LinearOrder ι] {ds : List RealBlock}
    {es : ι → List RealBlock} {q : ∀ j, KF n (es j) →ₗ[ℂ] KF n ds}
    (hfil : IsFiltration n ds es q) (hgen : ∀ j, HasFiniteDerivativeGenerators n (es j)) :
    HasFiniteDerivativeGenerators n ds := by
  classical
  choose F hdim hF using hgen
  let _ (j : ι) : FiniteDimensional ℂ (F j) := hdim j
  let E := ⨆ j, (F j).map (q j)
  let S := wordSpan (realStandardLie n ds) E
  have hE : FiniteDimensional ℂ E := Submodule.finiteDimensional_iSup _
  have h_range (j : ι) : LinearMap.range (q j) ≤ S := by
    apply (wellFounded_lt : WellFounded (fun i j : ι => i < j)).induction j
    · intro j ih
      have hPrev : (⨆ (i : ι) (_ : i < j), LinearMap.range (q i)) ≤ S :=
        iSup_le fun i => iSup_le fun hij => ih i hij
      let T := S.comap (q j)
      have hFT : F j ≤ T := fun f hf => le_wordSpan ds E
        (Submodule.mem_iSup_of_mem j (Submodule.mem_map_of_mem hf))
      have hstable (X : Matrix (Fin n) (Fin n) ℝ) (f : KF n (es j)) (hf : f ∈ T) :
          op (realStandardLie n (es j)) X f ∈ T := by
        obtain ⟨hf', hg', hdiff⟩ := (hfil.1 j).2 X f
        have he₁ : (⟨_, hf'⟩ : KF n (es j)) = op (realStandardLie n (es j)) X f :=
          Subtype.ext (realStandardLie_one_tmul_apply_coe n (es j) X f).symm
        have he₂ : (⟨_, hg'⟩ : KF n ds) = op (realStandardLie n ds) X (q j f) :=
          Subtype.ext (realStandardLie_one_tmul_apply_coe n ds X (q j f)).symm
        rw [he₁, he₂] at hdiff
        have hg : op (realStandardLie n ds) X (q j f) ∈ S :=
          RealJacquetFiniteGeneration.op_apply_mem_wordSpan X hf
        change q j (op (realStandardLie n (es j)) X f) ∈ S
        simpa only [sub_add_cancel] using S.add_mem (hPrev hdiff) hg
      have htop : (⊤ : Submodule ℂ (KF n (es j))) ≤ T := by
        rw [← hF j]
        apply RealJacquetFiniteGeneration.wordSpan_le
        intro w f hf
        induction w with
        | nil => simpa using hFT hf
        | cons X w ih =>
          rw [RealJacquetFiniteGeneration.wordOp_cons, Module.End.mul_apply]
          exact hstable X _ ih
      rintro v ⟨f, rfl⟩
      exact htop Submodule.mem_top
  refine ⟨E, hE, top_le_iff.mp ?_⟩
  rw [← hfil.2]
  exact iSup_le h_range

end RealStandardFiniteGeneration

open RealStandardFiniteGeneration (HasFiniteDerivativeGenerators)

/-- Every real standard module of the stipulated rank is generated under matrix right
derivatives by a finite-dimensional subspace of its compact-finite source. -/
def RealStandardFiniteGenerationStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n → HasFiniteDerivativeGenerators n ds

theorem realStandardFiniteGeneration : RealStandardFiniteGenerationStatement := by
  intro n ds₀ hRank
  let supp := realExponentSupport ds₀
  let K : ℕ := ⌊2 * (supp.map fun z => z.re ^ 2).sum⌋₊
  have hK (ds : List RealBlock) (hds : (realExponentSupport ds).Perm supp) :
      realWeightSquareSum ds ≤ K := by
    apply Nat.le_floor
    have h := realWeightSquareSum_le ds
    rwa [(hds.map fun z : ℂ => z.re ^ 2).sum_eq] at h
  have hrank (ds : List RealBlock) (hds : (realExponentSupport ds).Perm supp) :
      realRank ds = n := by
    rw [← length_realExponentSupport, hds.length_eq, show supp.length = n by
      dsimp only [supp]; rw [length_realExponentSupport, hRank]]
  suffices h : ∀ a b : ℕ, ∀ ds : List RealBlock, K - realWeightSquareSum ds = a →
      realInversionCount ds = b → (realExponentSupport ds).Perm supp →
      HasFiniteDerivativeGenerators n ds from h _ _ ds₀ rfl rfl (List.Perm.refl _)
  intro a
  refine Nat.strong_induction_on a (fun a iha b => ?_)
  refine Nat.strong_induction_on b (fun b ihb ds ha hb hs => ?_)
  by_cases ho : IsRealLanglandsOrdered ds
  · exact RealStandardFiniteGeneration.of_ordered (hrank ds hs) ho
  obtain ⟨pre, x, y, post, rfl, hxy⟩ := exists_adjacent_inversion_of_not_ordered ho
  obtain ⟨k, ws, q, hws, hq, hspan⟩ := realAdjacentFiltration_of_statements realCharacterPairFiltration
    realInducedPairFiltration n pre post x y (hrank _ hs) hxy
  apply RealStandardFiniteGeneration.of_filtration (es := fun j => pre ++ ws j ++ post) (q := q) ⟨hq, hspan⟩
  intro j
  rcases hws j with hj | ⟨hperm, hweight⟩
  · rw [hj, show pre ++ [y, x] ++ post = pre ++ y :: x :: post by simp]
    have hinv := realInversionCount_swap_lt pre post hxy
    have heq := realWeightSquareSum_swap pre post x y
    exact ihb _ (hinv.trans_eq hb) _ (by rw [heq, ha]) rfl
      ((realExponentSupport_swap pre post x y).trans hs)
  · have hp : pre ++ x :: y :: post = pre ++ [x, y] ++ post := by simp
    have hs' : (realExponentSupport (pre ++ ws j ++ post)).Perm supp := by
      apply List.Perm.trans _ hs
      rw [hp, realExponentSupport_append, realExponentSupport_append,
        realExponentSupport_append, realExponentSupport_append]
      exact (hperm.append_left _).append_right _
    have hweight' : realWeightSquareSum (pre ++ x :: y :: post) <
        realWeightSquareSum (pre ++ ws j ++ post) := by
      rw [hp, realWeightSquareSum_append, realWeightSquareSum_append,
        realWeightSquareSum_append, realWeightSquareSum_append]
      omega
    exact iha _ (by have := hK _ hs'; omega) _ _ rfl rfl hs'

end Langlands.Archimedean
