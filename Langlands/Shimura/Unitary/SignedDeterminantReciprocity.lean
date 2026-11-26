import Langlands.Shimura.Unitary.FiniteSignedDeterminant
import Langlands.GaloisCohomology.Global.BrauerSequence.Hasse

/-! # Parity of the finite signed determinant defects from Brauer reciprocity -/

noncomputable section

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global.AdelicFunctoriality
open Langlands.Global (FiniteCompletion)
open Langlands.LocalClassField Langlands.ClassFieldTheory.Local
open Langlands.GaloisCohomology Langlands.ProfiniteCohomology Langlands.Galois
open scoped FiniteExtension

universe u v w

local notation "ι₂" => denominatorMap 2 (by decide)

private theorem halfClass_injective : Function.Injective ι₂ := by
  intro a b h
  apply (denominatorEquiv 2 (by decide)).injective
  exact Subtype.ext h

private theorem halfClass_one : ι₂ 1 = rationalClass (1 / 2) := by
  change (denominatorEquiv 2 (by decide) 1 : RationalModIntegers) = _
  simp [denominatorEquiv_one, reciprocalClass, one_div]

private theorem halfClass_ne_zero : rationalClass (1 / 2) ≠ 0 := by
  rw [← halfClass_one, ← map_zero ι₂]
  exact fun h => (by decide : (1 : ZMod 2) ≠ 0) (halfClass_injective h)

private theorem mul_denominatorEquiv_eq_half {n : ℕ} (hn : 0 < n) (he : 2 ∣ n) (a : ZMod n) :
    (n / 2) • (denominatorEquiv n hn a : RationalModIntegers) =
      ι₂ (ZMod.castHom he (ZMod 2) a) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective a
  rw [map_intCast (ZMod.castHom he (ZMod 2)), denominatorEquiv_intCast,
    denominatorMap_intCast, ← map_nsmul]
  congr 1
  have hn' : n = 2 * (n / 2) := by omega
  have hq : (n : ℚ) = 2 * ((n / 2 : ℕ) : ℚ) := by exact_mod_cast hn'
  have hm : (0 : ℚ) < ((n / 2 : ℕ) : ℚ) := by
    exact_mod_cast (show 0 < n / 2 by omega)
  rw [nsmul_eq_mul]
  push_cast
  field_simp
  rw [hq]
  ring

private def realEmbeddingEquiv (E : Type u) [Field E] [IsTotallyReal E] :
    InfinitePlace E ≃ (E →+* ℝ) := by
  let f (p : InfinitePlace E) := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal p)
  refine Equiv.ofBijective f ⟨fun p q h => ?_, fun τ => ?_⟩
  · apply InfinitePlace.embedding_injective E
    ext x
    have h' := congrArg (fun τ : E →+* ℝ => (τ x : ℂ)) h
    simpa only [f, InfinitePlace.embedding_of_isReal_apply] using h'
  · let c := Complex.ofRealHom.comp τ
    have hc : ComplexEmbedding.IsReal c := ComplexEmbedding.isReal_iff.mpr (by
      ext x
      simp [c, ComplexEmbedding.conjugate_coe_eq])
    let p : InfinitePlace E := InfinitePlace.mk c
    refine ⟨p, RingHom.ext fun x => Complex.ofReal_injective ?_⟩
    change ((InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal p)) x : ℂ) = (τ x : ℂ)
    rw [InfinitePlace.embedding_of_isReal_apply]
    exact congrArg (fun g : E →+* ℂ => g x) (InfinitePlace.embedding_mk_eq_of_isReal hc)

section Defects

variable {E Ω : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field Ω] [Algebra E Ω] [IsSepClosure E Ω]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n) (hn : 0 < n) (he : 2 ∣ n)
  {s : Finset (Langlands.Global.FinitePlace E)} (a : s → ZMod n) (r : (E →+* ℝ) → ℕ)
  (hz : ∀ p ∉ s, ∀ q : FinitePlacesAbove K p, HasCompletedBrauerInvariant K A q.val 0)

attribute [local instance] FiniteExtension.local_finite

local notation "DetNorm(" p "," hp "," hps ")" =>
  (Subtype.val (nonsplitSignedDeterminant p hp D hn (hz p hps)) ∈
    normSubgroup (FiniteCompletion E p) (FiniteCompletion K (Subtype.val (placeAbove K p))))

set_option maxRecDepth 8192 in
include he in
private theorem exists_evenSignedDeterminantDefectSet (hc : CompatibleUnitaryLocalProfile E a r)
    (ι : PlaceEmbeddings E Ω) (x : cohomology (unitsModule E Ω) 2)
    (hchosen : ∀ p : s, localInvariant ι p.val x = (n / 2) •
      (denominatorEquiv n hn (a p) : RationalModIntegers))
    (hsplit : ∀ p ∉ s, IsSplitPlace E K p → localInvariant ι p x = 0)
    (hnonsplit : ∀ p (hps : p ∉ s) (hp : ¬ IsSplitPlace E K p),
      localInvariant ι p x = (by classical exact if DetNorm(p, hp, hps) then 0 else rationalClass (1 / 2)))
    (hreal : ∀ w : InfinitePlace E,
      realLocalInvariant ι w x = ι₂ (((n / 2 +
        (n - r (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))) : ℕ) : ZMod 2))) :
    ∃ S : Finset (Langlands.Global.FinitePlace E), (∀ p ∈ S, ¬ IsSplitPlace E K p) ∧
      Disjoint S s ∧ Even S.card ∧
        ∀ p (hps : p ∉ s) (hp : ¬ IsSplitPlace E K p), DetNorm(p, hp, hps) ↔ p ∉ S := by
  classical
  obtain ⟨hfinite, hrec⟩ := localInvariant_finite_support_and_sum_eq_zero ι x
  let S := hfinite.toFinset \ s
  have hS (p : Langlands.Global.FinitePlace E) : p ∈ S ↔ localInvariant ι p x ≠ 0 ∧ p ∉ s := by
    simp only [S, Finset.mem_sdiff, Set.Finite.mem_toFinset, Function.mem_support]
  have hd : Disjoint S s := Finset.sdiff_disjoint
  have hNS (p : Langlands.Global.FinitePlace E) (hp : p ∈ S) : ¬ IsSplitPlace E K p :=
    fun he => ((hS p).mp hp).1 (hsplit p ((hS p).mp hp).2 he)
  have hNorm (p : Langlands.Global.FinitePlace E) (hps : p ∉ s) (hp : ¬ IsSplitPlace E K p) :
      DetNorm(p, hp, hps) ↔ p ∉ S := by
    rw [hS, and_iff_left hps, not_not, hnonsplit p hps hp]
    split_ifs with h
    · simp [h]
    · exact iff_of_false h halfClass_ne_zero
  have hxS (p : Langlands.Global.FinitePlace E) (hp : p ∈ S) : localInvariant ι p x = ι₂ 1 := by
    have hps := ((hS p).mp hp).2
    have hpn := hNS p hp
    have hnot : ¬ DetNorm(p, hpn, hps) := fun h => (hNorm p hps hpn).mp h hp
    rw [hnonsplit p hps hpn, ite_eq_right hnot, halfClass_one]
  have hfs : ∑ᶠ p, localInvariant ι p x =
      (∑ p : s, localInvariant ι p.val x) + ∑ p ∈ S, localInvariant ι p x := by
    rw [finsum_eq_sum_of_support_subset _ (s := s ∪ S) (by
      intro p hp
      exact Finset.mem_union.mpr (or_iff_not_imp_left.mpr (fun hps => (hS p).mpr ⟨hp, hps⟩))),
      Finset.sum_union hd.symm]
    exact congrArg (· + ∑ p ∈ S, localInvariant ι p x)
      (s.sum_coe_sort (fun p => localInvariant ι p x)).symm
  have hsumS : ∑ p ∈ S, localInvariant ι p x = ι₂ (S.card : ZMod 2) := by
    rw [Finset.sum_congr rfl hxS, Finset.sum_const, ← map_nsmul, nsmul_eq_mul, mul_one]
  have hsumArch : ∑ w : InfinitePlace E, realLocalInvariant ι w x =
      ι₂ (((Fintype.card (E →+* ℝ) * (n / 2) : ℕ) : ZMod 2) +
        ∑ τ : E →+* ℝ, ((n - r τ : ℕ) : ZMod 2)) := by
    have hr (w : InfinitePlace E) : realLocalInvariant ι w x =
        ι₂ (((n / 2 + (n - r (realEmbeddingEquiv E w)) : ℕ) : ZMod 2)) := hreal w
    simp only [hr, ← map_sum]
    rw [(realEmbeddingEquiv E).sum_comp (fun τ => ((n / 2 + (n - r τ) : ℕ) : ZMod 2))]
    simp only [Nat.cast_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_mul,
      Finset.card_univ]
  have hsumChosen : ∑ p : s, localInvariant ι p.val x =
      ι₂ (∑ p : s, ZMod.castHom he (ZMod 2) (a p)) := by
    simp only [hchosen, mul_denominatorEquiv_eq_half hn he, map_sum]
  rw [hfs, hsumS, hsumArch, hsumChosen, ← map_add, ← map_add, ← map_zero ι₂] at hrec
  have hrec' := halfClass_injective hrec
  have hcompat := hc he
  rw [add_assoc] at hcompat
  have hcard : (S.card : ZMod 2) = 0 := by
    rw [add_right_comm, hcompat, zero_add] at hrec'
    exact hrec'
  exact ⟨S, hNS, hd, ZMod.natCast_eq_zero_iff_even.mp hcard, hNorm⟩

set_option maxRecDepth 8192 in
/-- The Brauer invariant formulas at split, nonsplit and real places, together
with profile compatibility, give a finite even set of signed determinant defects. -/
def evenSignedDeterminantDefectSet (hc : CompatibleUnitaryLocalProfile E a r)
    (ι : PlaceEmbeddings E Ω) (x : cohomology (unitsModule E Ω) 2)
    (hchosen : ∀ p : s, localInvariant ι p.val x = (n / 2) •
      (denominatorEquiv n hn (a p) : RationalModIntegers))
    (hsplit : ∀ p ∉ s, IsSplitPlace E K p → localInvariant ι p x = 0)
    (hnonsplit : ∀ p (hps : p ∉ s) (hp : ¬ IsSplitPlace E K p),
      localInvariant ι p x = (by classical exact if DetNorm(p, hp, hps) then 0 else rationalClass (1 / 2)))
    (hreal : ∀ w : InfinitePlace E,
      realLocalInvariant ι w x = ι₂ (((n / 2 +
        (n - r (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))) : ℕ) : ZMod 2))) :
    {S : Finset (Langlands.Global.FinitePlace E) // (∀ p ∈ S, ¬ IsSplitPlace E K p) ∧
      Disjoint S s ∧ Even S.card ∧
        ∀ p (hps : p ∉ s) (hp : ¬ IsSplitPlace E K p), DetNorm(p, hp, hps) ↔ p ∉ S} :=
  let h := exists_evenSignedDeterminantDefectSet D hn he a r hz hc ι x hchosen hsplit hnonsplit hreal
  ⟨h.choose, h.choose_spec⟩

end Defects

end Langlands.Shimura.FiniteUnitary
