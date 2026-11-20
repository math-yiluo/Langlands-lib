import Langlands.Automorphic.HeckeTwist.CuspidalSpectralTwist
import Langlands.Automorphic.Unramified.CyclicCuspidalLocalProduct
import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement
import Langlands.Global.Factors.FiniteComparisonProof

/-! # Comparison of partial pair products over cyclic character powers -/

noncomputable section

universe uF uQ

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Unramified
open Langlands.Global.CuspidalPairBoundaryNonvanishing
open Langlands.Global.CuspidalPairFunctionalEquation (pairEulerPolynomial residueCardinality)
open Langlands.Global.FunctionalEquationComparison (eq_on_halfplane_meromorphicEq)

variable {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r t : ℕ} {T U : CuspidalOperatorRealization F r} {V : CuspidalOperatorRealization F t}

private theorem partialEulerFactor_heckeDeterminantTwist_pow
    (P : CuspidalSpectralPresentation.{uF, uQ} T) (R : CuspidalSpectralPresentation.{uF, uQ} V)
    (η : HeckeCharacter F) (i : ℕ) {S : Finset (FinitePlace F)}
    (hP : (P.heckeDeterminantTwist (η ^ i)).exceptional ⊆ S) (hR : R.exceptional ⊆ S)
    (v : {v : FinitePlace F // v ∉ S}) (hv : v.1 ∉ P.exceptional) (s : ℂ) :
    partialEulerFactor (P.heckeDeterminantTwist (η ^ i)) R hP hR v s =
      ((pairEulerPolynomial
        ((P.spectralSystem.eigenvalues v.1 hv).scale (η.finiteUniformizerValue v.1 ^ i))
        (R.spectralSystem.eigenvalues v.1 (fun h => v.2 (hR h)))).eval
        (RankinSelberg.spectralPoint (residueCardinality v.1) s))⁻¹ := by
  have hη : (η ^ i).finiteUniformizerValue v.1 = η.finiteUniformizerValue v.1 ^ i :=
    ContinuousMonoidHom.pow_apply η i _
  rw [← hη]
  rfl

/-- A cofinite residue-power comparison with the local orders of the character implies
    equality of the total orders of the two partial pair products at `s = 1`. Both products
    use one finite omitted set, the same second presentation and all `d` powers. -/
def CyclicCuspidalPairProductStatement : Prop :=
  ∀ (F : Type uF) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T U : CuspidalOperatorRealization F r) (V : CuspidalOperatorRealization F t)
    (P : CuspidalSpectralPresentation.{uF, uQ} T) (Q : CuspidalSpectralPresentation.{uF, uQ} U)
    (R : CuspidalSpectralPresentation.{uF, uQ} V) (η : HeckeCharacter F) (d : ℕ),
    (∀ᶠ v in Filter.cofinite, ∃ (hp : v ∉ P.exceptional) (hq : v ∉ Q.exceptional) (f : ℕ),
      0 < f ∧ f ∣ d ∧ IsPrimitiveRoot (η.finiteUniformizerValue v) f ∧
        (P.spectralSystem.eigenvalues v hp).power f = (Q.spectralSystem.eigenvalues v hq).power f) →
    ∃ (S : Finset (FinitePlace F)) (hR : R.exceptional ⊆ S)
      (hP : ∀ i : Fin d, (P.heckeDeterminantTwist (η ^ (i : ℕ))).exceptional ⊆ S)
      (hQ : ∀ i : Fin d, (Q.heckeDeterminantTwist (η ^ (i : ℕ))).exceptional ⊆ S),
      ∀ L M : Fin d → ℂ → ℂ,
        (∀ i : Fin d,
          IsPartialPairLFunction (P.heckeDeterminantTwist (η ^ (i : ℕ))) R (hP i) hR (L i)) →
        (∀ i : Fin d,
          IsPartialPairLFunction (Q.heckeDeterminantTwist (η ^ (i : ℕ))) R (hQ i) hR (M i)) →
        ∑ i, meromorphicOrderAt (L i) 1 = ∑ i, meromorphicOrderAt (M i) 1

/-- The partial Euler product comparison in Arthur–Clozel III.3.1. -/
theorem cyclicCuspidalPairProduct : CyclicCuspidalPairProductStatement.{uF, uQ} := by
  classical
  intro F _ _ _ r t T U V P Q R η d hgood
  have hbad := Filter.eventually_cofinite.mp hgood
  let EP (i : Fin d) := (P.heckeDeterminantTwist (η ^ (i : ℕ))).exceptional
  let EQ (i : Fin d) := (Q.heckeDeterminantTwist (η ^ (i : ℕ))).exceptional
  let S := hbad.toFinset ∪ (R.exceptional ∪ (Finset.univ.biUnion EP ∪ Finset.univ.biUnion EQ))
  have hR : R.exceptional ⊆ S := fun v hv =>
    Finset.mem_union_right _ (Finset.mem_union_left _ hv)
  have hP (i : Fin d) : EP i ⊆ S := fun v hv =>
    Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hv⟩)))
  have hQ (i : Fin d) : EQ i ⊆ S := fun v hv =>
    Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hv⟩)))
  refine ⟨S, hR, hP, hQ, fun L M hL hM => ?_⟩
  let l (i : Fin d) := partialEulerFactor (P.heckeDeterminantTwist (η ^ (i : ℕ))) R (hP i) hR
  let m (i : Fin d) := partialEulerFactor (Q.heckeDeterminantTwist (η ^ (i : ℕ))) R (hQ i) hR
  have hfactor (v : {v : FinitePlace F // v ∉ S}) (s : ℂ) :
      (∏ i, l i v s) = ∏ i, m i v s := by
    have hv : v.1 ∉ hbad.toFinset := fun hv => v.2 (Finset.mem_union_left _ hv)
    have h := not_not.mp (fun hn => hv (hbad.mem_toFinset.mpr hn))
    obtain ⟨hp, hq, f, hf, hfd, hζ, hpower⟩ := h
    dsimp only [l, m]
    simp_rw [partialEulerFactor_heckeDeterminantTwist_pow P R η _ _ hR v hp s,
      partialEulerFactor_heckeDeterminantTwist_pow Q R η _ _ hR v hq s, Finset.prod_inv_distrib,
      cyclicCuspidalLocalProduct _ _ _ _ hf hζ hfd, hpower]
  have hLprod (i : Fin d) : ∀ᶠ ρ : ℝ in Filter.atTop,
      ∀ s : ℂ, ρ ≤ s.re → HasProd (fun v => l i v s) (L i s) := by
    obtain ⟨σ, hσ⟩ := (hL i).2
    filter_upwards [Filter.eventually_gt_atTop σ] with ρ hρ s hs
    exact (hσ s (hρ.trans_le hs)).2
  have hMprod (i : Fin d) : ∀ᶠ ρ : ℝ in Filter.atTop,
      ∀ s : ℂ, ρ ≤ s.re → HasProd (fun v => m i v s) (M i s) := by
    obtain ⟨σ, hσ⟩ := (hM i).2
    filter_upwards [Filter.eventually_gt_atTop σ] with ρ hρ s hs
    exact (hσ s (hρ.trans_le hs)).2
  obtain ⟨σ, hσ⟩ := Filter.eventually_atTop.mp
    ((Filter.eventually_all.mpr hLprod).and (Filter.eventually_all.mpr hMprod))
  have hLf (i : Fin d) : Meromorphic (L i) := meromorphicOn_univ.mp (hL i).1
  have hMf (i : Fin d) : Meromorphic (M i) := meromorphicOn_univ.mp (hM i).1
  have hEq : ∀ s : ℂ, σ < s.re → (∏ i, L i s) = ∏ i, M i s := by
    intro s hs
    have hl := hasProd_prod (s := Finset.univ) (fun i _ => (hσ σ le_rfl).1 i s hs.le)
    have hm := hasProd_prod (s := Finset.univ) (fun i _ => (hσ σ le_rfl).2 i s hs.le)
    rw [show (fun v => ∏ i, l i v s) = (fun v => ∏ i, m i v s) from
      funext (fun v => hfactor v s)] at hl
    exact hl.unique hm
  have hmer := eq_on_halfplane_meromorphicEq
    (fun s => MeromorphicAt.fun_prod (fun i _ => hLf i s))
    (fun s => MeromorphicAt.fun_prod (fun i _ => hMf i s)) hEq
  have hord := meromorphicOrderAt_congr (hmer 1)
  rwa [meromorphicOrderAt_fun_prod (fun i _ => hLf i 1),
    meromorphicOrderAt_fun_prod (fun i _ => hMf i 1)] at hord

end Langlands.Automorphic.Unramified
