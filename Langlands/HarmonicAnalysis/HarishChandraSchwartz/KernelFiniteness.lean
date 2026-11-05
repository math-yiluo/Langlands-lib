import Langlands.HarmonicAnalysis.HarishChandraSchwartz.KernelQuotient
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.KernelDiagonal
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalIntegrability

/-! # Proposition VIII.4.1: finiteness of `p_χ(°C_H)` (abstract assembly)

Waldspurger 2003, Proposition VIII.4.1: for every compact open subgroup `H` of `G` and every
unitary character `χ` of `A_G`, the space `p_χ(°C_H)` is finite dimensional. The proof shows
that `α_χ(·, g)` is a reproducing kernel for this space on `A_G\G` (formula (1)), rewrites the
diagonal as `α_χ(g, g) = ∫_G °e(g⁻¹ g' g) ϕ(g') dg'` with `ϕ` the product of `ψ` and the
characteristic function of `G¹`, and concludes with Corollary VIII.3.2, applied at `h = g⁻¹`.

This module assembles `KernelQuotient`, `KernelDiagonal` and `CuspidalIntegrability`. The
evaluation of Corollary VIII.3.2 at `h = g⁻¹` is done by reading the quotient through the map
`h ↦ A h⁻¹`: for central `A`, the representative `q̇` of the class of `h⁻¹` satisfies
`q̇⁻¹ x q̇ = h x h⁻¹`. The cells of the Corollary are then images of the sets `(K' a Y)⁻¹`.
-/

noncomputable section

open MeasureTheory Langlands.QuotientIntegration
open scoped ENNReal ComplexConjugate

namespace Langlands.HarishChandraSchwartz

universe u

section Inversion

variable {G : Type u} [Group G] {A : Subgroup G}

/-- For central `A`, conjugation by a representative of the class `A g` is conjugation by `g`:
`q̇⁻¹ x q̇ = g⁻¹ x g` when `q = A g`. -/
theorem out_inv_mul_mul_out (hAc : A ≤ Subgroup.center G) {g : G} {q : LeftQuotient A}
    (hq : Quotient.mk _ g = q) (x : G) : q.out⁻¹ * x * q.out = g⁻¹ * x * g := by
  subst hq
  have hr : g * (Quotient.mk (QuotientGroup.rightRel A) g).out⁻¹ ∈ A :=
    QuotientGroup.rightRel_apply.mp (Quotient.mk_out (s := QuotientGroup.rightRel A) g)
  have key : ∀ b ∈ A, ∀ o : G, o = b⁻¹ * g → o⁻¹ * x * o = g⁻¹ * x * g := by
    rintro b hb o rfl
    have hc : x * b = b * x := Subgroup.mem_center_iff.mp (hAc hb) x
    calc (b⁻¹ * g)⁻¹ * x * (b⁻¹ * g) = g⁻¹ * (b * x) * b⁻¹ * g := by group
      _ = g⁻¹ * (x * b) * b⁻¹ * g := by rw [hc]
      _ = g⁻¹ * x * g := by group
  exact key _ hr _ (by group)

end Inversion

section Corollary

variable {G : Type u} [Group G] [MeasurableSpace G] [MeasurableMul G] {M : Subgroup G}
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  {A : Subgroup G} [MeasurableSpace (LeftQuotient A)] {ν : Measure (LeftQuotient A)}
  {ι : Type*} [Countable ι]

/-- **Corollary VIII.3.2 at `h = g⁻¹`**, read through representatives: for central `A`,
`∫_{A\G} |∫_G f₁(q̇⁻¹ g q̇) f₂(g) dg| dν(q) < ∞` under the hypotheses of
`lintegral_lt_top_of_conjugationIntegralBound`, with cells `Ω(i)` whose points are classes of
`(k a_i y)⁻¹` for `k ∈ K'`, `y ∈ Y`. -/
theorem lintegral_conj_out_lt_top (hAc : A ≤ Subgroup.center G) {T : Set M} {e : M → ℝ}
    {σ : G → ℝ} (he : ∀ a ∈ T, 0 < e a) (hσ : ∀ g, 0 ≤ σ g) {f₁ f₂ : G → ℂ}
    {Ω : ι → Set (LeftQuotient A)} (hcover : ∀ q, ∃ i, q ∈ Ω i) {a : ι → M}
    (haT : ∀ i, a i ∈ T) {K' Y : Set G}
    (hcell : ∀ i, ∀ q ∈ Ω i, ∃ k ∈ K', ∃ y ∈ Y, q = Quotient.mk _ (k * a i * y)⁻¹)
    (hfin₁ : (Set.image (fun k => conjFun k f₁) K').Finite)
    (hfin₂ : (Set.image (fun y => conjFun y⁻¹ f₂) Y).Finite)
    (h31 : ∀ k ∈ K', ∀ y ∈ Y, ConjugationIntegralBound μ T (conjFun k f₁) (conjFun y⁻¹ f₂) e σ)
    {C₂ : ℝ} (hm : ∀ i, ν (Ω i) ≤ ENNReal.ofReal (C₂ * (e (a i) ^ 2)⁻¹))
    {r : ℝ} (hsum : Summable fun i => (1 + σ (a i)) ^ (-r)) :
    ∫⁻ q, ‖∫ g, f₁ (q.out⁻¹ * g * q.out) * f₂ g ∂μ‖ₑ ∂ν < ⊤ := by
  refine lintegral_lt_top_of_conjugationIntegralBound (π := fun h => Quotient.mk _ h⁻¹)
    he hσ (fun h => ?_) hcover haT hcell hfin₁ hfin₂ h31 hm hsum
  simp_rw [out_inv_mul_mul_out hAc rfl, inv_inv]

end Corollary

section Assembly

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {A : Subgroup G} (hA : IsClosed (A : Set G))
  [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
  {μA : Measure A} [SFinite μA] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
  {μG : Measure G} [IsFiniteMeasureOnCompacts μG] {ν : Measure (LeftQuotient A)}
  {χ : A →* ℂˣ} {H : Subgroup G} {μH : Measure H} {E : G → ℂ}

variable (A) in
/-- Waldspurger's `ϕ` in the proof of Proposition VIII.4.1: the product of `ψ`
(`diagonalWeight`) with the characteristic function of a subgroup `N` (his `G¹`). -/
def diagonalWeightOn (N : Subgroup G) (μA : Measure A) (χ : A →* ℂˣ) (μH : Measure H) :
    G → ℂ :=
  (N : Set G).indicator (diagonalWeight A μA χ μH)

include hA in
/-- **Proposition VIII.4.1 in abstract form.** Let `V` satisfy the hypotheses of
`isSectionReproducingKernel_kernelAlphaChi` (reproducing kernel `α_χ(·, y) ∈ V` on `A\G`). If
`H` is open with `μ_H` the restriction of `μ_G`, `χ` is trivial on `A ∩ H`, `E` vanishes outside
a normal subgroup `N`, and Corollary VIII.3.2 applies to `f₁ = E` and `f₂ = 1_N ψ` (cells of
`A\G` that are classes of `(k a_i y)⁻¹`, finitely many conjugates, Proposition VIII.3.1 for
their pairs, the measure bound of the cells and the summability), then `V` is finite
dimensional. -/
theorem finiteDimensional_of_conjugationIntegralBound [MeasurableMul A] [SFinite μG]
    [SFinite μH] [MeasurableInv A] [μA.IsInvInvariant] [μA.IsMulLeftInvariant]
    [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] (hν : IsCompatible A μG μA ν)
    (hAc : A ≤ Subgroup.center G) (hχ : IsUnitaryCharacter χ) (hE : ∀ x, conj (E x) = E x)
    (hmes : (μH Set.univ).toReal ≠ 0) {V : Submodule ℂ (G → ℂ)}
    (hV : IsKernelAlphaChiSpace μG μA χ μH E V)
    (hKV : ∀ y, (fun g => kernelAlphaChi μA χ μH E g y) ∈ V)
    (hprod : ∀ f ∈ V, ∀ f' ∈ V,
      Integrable (fun q : LeftQuotient A => f q.out * conj (f' q.out)) ν)
    (hH : IsOpen (H : Set G)) (hμH : μH.map Subtype.val = μG.restrict H)
    (hχH : ∀ a : A, (a : G) ∈ H → χ a = 1) (hfin : μA {a : A | (a : G) ∈ H} ≠ ⊤)
    (hint : ∀ q : LeftQuotient A,
      Integrable (fun x => E (q.out⁻¹ * x * q.out) * centralCharacterExtension A H χ x)
        (μG.restrict (productSet A H)))
    (hmeas : AEStronglyMeasurable
      (fun q : LeftQuotient A => kernelAlphaChi μA χ μH E q.out q.out) ν)
    {N : Subgroup G} [N.Normal] (hEN : ∀ x, x ∉ N → E x = 0)
    {M : Subgroup G} {T : Set M} {e : M → ℝ} {σ : G → ℝ} (he : ∀ a ∈ T, 0 < e a)
    (hσ : ∀ g, 0 ≤ σ g) {ι : Type*} [Countable ι] {Ω : ι → Set (LeftQuotient A)}
    (hcover : ∀ q, ∃ i, q ∈ Ω i) {a : ι → M} (haT : ∀ i, a i ∈ T) {K' Y : Set G}
    (hcell : ∀ i, ∀ q ∈ Ω i, ∃ k ∈ K', ∃ y ∈ Y, q = Quotient.mk _ (k * a i * y)⁻¹)
    (hfin₁ : (Set.image (fun k => conjFun k E) K').Finite)
    (hfin₂ : (Set.image (fun y => conjFun y⁻¹ (diagonalWeightOn A N μA χ μH)) Y).Finite)
    (h31 : ∀ k ∈ K', ∀ y ∈ Y, ConjugationIntegralBound μG T (conjFun k E)
      (conjFun y⁻¹ (diagonalWeightOn A N μA χ μH)) e σ)
    {C₂ : ℝ} (hm : ∀ i, ν (Ω i) ≤ ENNReal.ofReal (C₂ * (e (a i) ^ 2)⁻¹))
    {r : ℝ} (hsum : Summable fun i => (1 + σ (a i)) ^ (-r)) :
    FiniteDimensional ℂ V := by
  refine finiteDimensional_of_kernelAlphaChi hA hν hAc hχ hE hmes hV hKV hprod ?_
  refine integrable_re_kernelAlphaChi_diag hH μG hμH hAc hχH hfin hint hmeas ?_
  simp_rw [integral_conj_mul_eq_indicator hEN μG (diagonalWeight A μA χ μH)]
  exact lintegral_conj_out_lt_top hAc he hσ hcover haT hcell hfin₁ hfin₂ h31 hm hsum

end Assembly

end Langlands.HarishChandraSchwartz
