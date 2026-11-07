import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Group.Quotient
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceOrthogonality
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Twist.SmoothPartDefinitions
import Langlands.Topology.ComplexCharacterExtension

/-! # The scalar of `π[φ]` on irreducible tempered representations (Waldspurger III.7.1)

In the proof of Proposition III.7.1 (printed pp. 274–275), Waldspurger fixes `ω ∈ E₂(G)`, sets
`ψ_H(g) = trace[ω̌(ε_H) ω̌(g) ω̌(ε_H)]`, `φ_H = φ ψ_H` for `φ ∈ C_c(G/G¹)`, defines
`π[φ] v = π(φ_H) v` for `H` fixing `v`, and computes `π[φ]` on an irreducible tempered `π`:
it is the homothety of ratio `P_φ(π) = d(ω)⁻¹ [G : G¹Z_G]⁻¹ Σ_{χ ∈ S(π)} ∫_{G¹\G} φ χ`, with
`S(π) = {χ ∈ X(G); π ≃ ω ⊗ χ}`.

The Library has `π[φ]` as `(traceFamily (contragredientRep ω) …).operator`
(`TraceCoefficientFamily`, `SchwartzActionFamily`) and the Schur step (`TraceOrthogonality`).
This module carries out the computation for an abstract group, with a surjective homomorphism
`p : G →* Λ` onto a commutative group with open kernel in place of `G → G/G¹`, a central
subgroup `A` in place of `A_G` with `Λ / p(A)` finite, and a compatibility constant `m` between
the Haar measure of `G` and the quotient measure on `G / A`:

* `traceFamily_operator_eval_eq_sum`, `traceFamily_operator_eq_smul`: for a character `χ₀` of
  `Λ` with `χ₀(p(a)) cω(a) = cπ(a)` on `A`,
  `π[φ] = m |Q|⁻¹ Σ_η [π ⊗ (χ₀η ∘ p)⁻¹ ≃ ω] d(ω)⁻¹ φ̂(χ₀η) • id`, the sum over the characters
  `η` of `Q = Λ / p(A)` and `φ̂(χ) = Σ_λ φ(λ) χ(λ)`;
* `traceFamily_operator_eval_eq_zero`: `π[φ] = 0` if the central characters differ on
  `A ∩ ker p`;
* `exists_character_comp_eq`: such a `χ₀` exists when they agree on `A ∩ ker p`.

The route is the source's: decomposition of `∫_G` along the fibres of `p`, Fourier inversion on
the finite group `Q` (`card_mul_eq_sum_addChar`), and the Schur orthogonality relations for the
twists `π ⊗ (χ ∘ p)⁻¹` (`integral_twistedTraceIntegrand`). -/

noncomputable section

open MeasureTheory

namespace Langlands.HarishChandraSchwartz

open Langlands.Plancherel

section FiniteFourier

variable {Λ : Type*} [CommGroup Λ] (B : Subgroup Λ)

/-- The character `λ ↦ η(λ B)` of `Λ` defined by a character `η` of the finite quotient. -/
def quotientCharacter (η : AddChar (Additive (Λ ⧸ B)) ℂ) : Λ →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := fun x => η (Additive.ofMul (x : Λ ⧸ B))
      map_one' := by simp
      map_mul' := fun x y => by
        rw [QuotientGroup.mk_mul, ofMul_mul, AddChar.map_add_eq_mul] }

theorem quotientCharacter_apply (η : AddChar (Additive (Λ ⧸ B)) ℂ) (x : Λ) :
    (quotientCharacter B η x : ℂ) = η (Additive.ofMul (x : Λ ⧸ B)) :=
  rfl

theorem quotientCharacter_of_mem (η : AddChar (Additive (Λ ⧸ B)) ℂ) {x : Λ} (hx : x ∈ B) :
    quotientCharacter B η x = 1 := by
  ext
  rw [quotientCharacter_apply, (QuotientGroup.eq_one_iff x).2 hx]
  simp

variable [Fintype (Λ ⧸ B)]

/-- Fourier inversion on the finite quotient `Q = Λ / B`:
`|Q| h(q) = Σ_η η(q) Σ_{q'} η(q')⁻¹ h(q')`. -/
theorem card_mul_eq_sum_addChar (h : Λ ⧸ B → ℂ) (q : Λ ⧸ B) :
    (Nat.card (Λ ⧸ B) : ℂ) * h q = ∑ η : AddChar (Additive (Λ ⧸ B)) ℂ,
      η (Additive.ofMul q) * ∑ q' : Λ ⧸ B, (η (Additive.ofMul q'))⁻¹ * h q' := by
  classical
  have key : ∀ q' : Λ ⧸ B, ∑ η : AddChar (Additive (Λ ⧸ B)) ℂ,
      η (Additive.ofMul q) * (η (Additive.ofMul q'))⁻¹ =
        if q = q' then (Nat.card (Λ ⧸ B) : ℂ) else 0 := by
    intro q'
    have h1 : ∀ η : AddChar (Additive (Λ ⧸ B)) ℂ,
        η (Additive.ofMul q) * (η (Additive.ofMul q'))⁻¹ =
          η (Additive.ofMul q - Additive.ofMul q') := by
      intro η
      rw [AddChar.map_sub_eq_div, div_eq_mul_inv]
    simp_rw [h1]
    rw [AddChar.sum_apply_eq_ite]
    by_cases hq : q = q'
    · subst hq
      simp
    · have hq' : Additive.ofMul q - Additive.ofMul q' ≠ 0 := by
        rwa [sub_ne_zero, ne_eq, EmbeddingLike.apply_eq_iff_eq]
      simp [hq, hq']
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, key, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

end FiniteFourier

section Cosets

open scoped ENNReal Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  {Λ : Type*} [CommGroup Λ] (p : G →* Λ)

omit [MeasurableSpace G] [BorelSpace G] in
/-- The fibres of `p` are open when its kernel is open. -/
theorem isOpen_preimage_singleton (hN : IsOpen (p.ker : Set G)) (l : Λ) :
    IsOpen (p ⁻¹' {l}) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨x • (p.ker : Set G), fun y hy => ?_, hN.leftCoset x,
    Set.mem_smul_set.2 ⟨1, one_mem _, by simp⟩⟩
  obtain ⟨n, hn, rfl⟩ := Set.mem_smul_set.1 hy
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
  rw [smul_eq_mul, map_mul, MonoidHom.mem_ker.1 hn, mul_one, hx]

theorem measurableSet_preimage_singleton (hN : IsOpen (p.ker : Set G)) (l : Λ) :
    MeasurableSet (p ⁻¹' {l}) :=
  (isOpen_preimage_singleton p hN l).measurableSet

variable {μ : Measure G}

/-- `∫_G φ(p(g)) F(g) dg = Σ_λ φ(λ) ∫_{p⁻¹(λ)} F` for a finitely supported `φ` on `Λ`. -/
theorem integral_finsupp_comp_mul (hN : IsOpen (p.ker : Set G)) (φ : Λ →₀ ℂ) {F : G → ℂ}
    (hF : ∀ l ∈ φ.support, IntegrableOn F (p ⁻¹' {l}) μ) :
    ∫ g, φ (p g) * F g ∂μ = ∑ l ∈ φ.support, φ l * ∫ g in p ⁻¹' {l}, F g ∂μ := by
  classical
  have hpt : ∀ g, φ (p g) * F g =
      ∑ l ∈ φ.support, (p ⁻¹' {l}).indicator (fun g => φ l * F g) g := by
    intro g
    by_cases hg : p g ∈ φ.support
    · rw [Finset.sum_eq_single (p g)]
      · rw [Set.indicator_of_mem (by simp)]
      · intro l _ hl
        rw [Set.indicator_of_notMem]
        simpa [eq_comm] using hl
      · intro h
        exact absurd hg h
    · rw [Finsupp.notMem_support_iff.1 hg, zero_mul, Finset.sum_eq_zero]
      intro l hl
      rw [Set.indicator_of_notMem]
      intro hgl
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hgl
      exact hg (hgl ▸ hl)
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_indicator (measurableSet_preimage_singleton p hN l), integral_const_mul]
  · intro l hl
    exact (integrable_indicator_iff (measurableSet_preimage_singleton p hN l)).2
      ((hF l hl).const_mul (φ l))

variable [μ.IsMulLeftInvariant]

/-- If `F(a g) = c F(g)` for all `g`, then `∫_{p⁻¹(p(a) λ)} F = c ∫_{p⁻¹(λ)} F`. -/
theorem setIntegral_preimage_mul_left {F : G → ℂ} {a : G} {c : ℂ}
    (hF : ∀ g, F (a * g) = c * F g) (l : Λ) :
    ∫ g in p ⁻¹' {p a * l}, F g ∂μ = c * ∫ g in p ⁻¹' {l}, F g ∂μ := by
  have hpre : (a * ·) ⁻¹' (p ⁻¹' {p a * l}) = p ⁻¹' {l} := by
    ext g
    simp
  rw [← (measurePreserving_mul_left μ a).setIntegral_preimage_emb
    (measurableEmbedding_mulLeft a), hpre]
  simp_rw [hF]
  exact integral_const_mul c _

variable {A : Subgroup G} [A.Normal] [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  {ν : Measure (G ⧸ A)} [ν.IsMulLeftInvariant] {m : ℝ≥0∞}

/-- Translating the normalization of the measures on `ker p` and on its image in `G / A`
to every fibre of `p`. -/
theorem map_mk_restrict_preimage
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G))) (g : G) :
    Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p ⁻¹' {p g})) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p ⁻¹' {p g})) := by
  have hmk : Measurable (QuotientGroup.mk : G → G ⧸ A) :=
    (show Continuous (QuotientGroup.mk : G → G ⧸ A) from continuous_quot_mk).measurable
  have hpre : (g * ·) ⁻¹' (p ⁻¹' {p g}) = (p.ker : Set G) := by
    ext x
    simp
  have h1 : μ.restrict (p ⁻¹' {p g}) = Measure.map (g * ·) (μ.restrict (p.ker : Set G)) := by
    rw [← hpre, ← (measurableEmbedding_mulLeft g).restrict_map, map_mul_left_eq_self]
  have h2 : (QuotientGroup.mk : G → G ⧸ A) ∘ (g * ·) =
      (((g : G ⧸ A) * ·)) ∘ (QuotientGroup.mk : G → G ⧸ A) := by
    funext x
    simp [QuotientGroup.mk_mul]
  have hT : ((g : G ⧸ A) * ·) ⁻¹' ((QuotientGroup.mk : G → G ⧸ A) '' (p ⁻¹' {p g})) =
      (QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G) := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H y =>
      simp only [Set.mem_preimage, Set.mem_image, SetLike.mem_coe, MonoidHom.mem_ker]
      constructor
      · rintro ⟨x, hx, hxy⟩
        refine ⟨g⁻¹ * x, ?_, ?_⟩
        · simp only [Set.mem_singleton_iff] at hx
          rw [map_mul, map_inv, hx, inv_mul_cancel]
        · rw [QuotientGroup.mk_mul, hxy, QuotientGroup.mk_inv, inv_mul_cancel_left]
      · rintro ⟨x, hx, hxy⟩
        refine ⟨g * x, ?_, ?_⟩
        · simp [hx]
        · rw [QuotientGroup.mk_mul, hxy]
  rw [h1, Measure.map_map hmk (measurable_const_mul g), h2,
    ← Measure.map_map (measurable_const_mul (g : G ⧸ A)) hmk, hcompat, Measure.map_smul,
    ← hT, ← (measurableEmbedding_mulLeft (g : G ⧸ A)).restrict_map, map_mul_left_eq_self]
  exact (measurable_const_mul _).aemeasurable

omit [IsTopologicalGroup G] [A.Normal] in
theorem measurable_quotientMk : Measurable (QuotientGroup.mk : G → G ⧸ A) :=
  (show Continuous (QuotientGroup.mk : G → G ⧸ A) from continuous_quot_mk).measurable

/-- For `H` integrable on `G / A`, `∫_{p⁻¹(p g)} H(xA) dx = m ∫_{(p⁻¹(p g)) A / A} H`. -/
theorem setIntegral_preimage_comp_mk
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G))) (g : G)
    {H : G ⧸ A → ℂ} (hH : Integrable H ν) :
    ∫ x in p ⁻¹' {p g}, H (x : G ⧸ A) ∂μ =
      m.toReal * ∫ y in (QuotientGroup.mk : G → G ⧸ A) '' (p ⁻¹' {p g}), H y ∂ν := by
  have hmeas : AEStronglyMeasurable H
      (Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p ⁻¹' {p g}))) := by
    rw [map_mk_restrict_preimage p hcompat g]
    exact hH.aestronglyMeasurable.restrict.smul_measure _
  rw [← integral_map measurable_quotientMk.aemeasurable hmeas,
    map_mk_restrict_preimage p hcompat g, integral_smul_measure, Complex.real_smul]

/-- On a fibre of `p`, `H ∘ mk` is integrable when `H` is integrable on `G / A`. -/
theorem integrableOn_preimage_comp_mk
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G))) (hm : m ≠ ∞)
    (g : G) {H : G ⧸ A → ℂ} (hH : Integrable H ν) :
    IntegrableOn (fun x : G => H (x : G ⧸ A)) (p ⁻¹' {p g}) μ := by
  have h : Integrable H
      (Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p ⁻¹' {p g}))) := by
    rw [map_mk_restrict_preimage p hcompat g]
    exact hH.restrict.smul_measure hm
  exact (integrable_map_measure h.aestronglyMeasurable
    measurable_quotientMk.aemeasurable).1 h

/-- Summing the fibre integrals over representatives of `Λ / p(A)` gives `m ∫_{G/A} H`. -/
theorem sum_setIntegral_preimage [Fintype (Λ ⧸ A.map p)] (hp : Function.Surjective p)
    (hN : IsOpen (p.ker : Set G))
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    {H : G ⧸ A → ℂ} (hH : Integrable H ν) (r : Λ ⧸ A.map p → Λ)
    (hr : ∀ q, (r q : Λ ⧸ A.map p) = q) :
    ∑ q, ∫ x in p ⁻¹' {r q}, H (x : G ⧸ A) ∂μ = m.toReal * ∫ y, H y ∂ν := by
  choose g hg using fun q => hp (r q)
  let T : Λ ⧸ A.map p → Set (G ⧸ A) := fun q =>
    (QuotientGroup.mk : G → G ⧸ A) '' (p ⁻¹' {r q})
  have hT : ∀ q, MeasurableSet (T q) := fun q =>
    (QuotientGroup.isOpenMap_coe _ (isOpen_preimage_singleton p hN (r q))).measurableSet
  have hd : Pairwise (Function.onFun Disjoint T) := by
    intro q q' hqq'
    refine Set.disjoint_left.2 fun y hy hy' => hqq' ?_
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨x', hx', hxx'⟩ := hy'
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
    have hA : x'⁻¹ * x ∈ A := QuotientGroup.eq.1 hxx'
    rw [← hr q, ← hr q', ← hx, ← hx', eq_comm, QuotientGroup.eq, ← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem p hA
  have hU : (⋃ q, T q) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    induction y using QuotientGroup.induction_on with
    | H x =>
      set q : Λ ⧸ A.map p := (p x : Λ ⧸ A.map p)
      have hq : (p x : Λ ⧸ A.map p) = (r q : Λ ⧸ A.map p) := by rw [hr q]
      obtain ⟨a, ha, hpa⟩ := Subgroup.mem_map.1 (QuotientGroup.eq.1 hq)
      refine Set.mem_iUnion.2 ⟨q, x * a, ?_, ?_⟩
      · simp only [Set.mem_preimage, Set.mem_singleton_iff, map_mul, hpa, mul_inv_cancel_left]
      · exact QuotientGroup.eq.2 (by simpa using ha)
  have hterm : ∀ q, ∫ x in p ⁻¹' {r q}, H (x : G ⧸ A) ∂μ = m.toReal * ∫ y in T q, H y ∂ν := by
    intro q
    have h := setIntegral_preimage_comp_mk p hcompat (g q) hH
    rw [hg q] at h
    exact h
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  congr 1
  have hint : IntegrableOn H (⋃ q, T q) ν := by
    rw [hU]
    exact hH.integrableOn
  rw [← setIntegral_univ, ← hU, integral_iUnion hT hd hint, tsum_fintype]

end Cosets

section Helpers

universe u v w

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Λ : Type*} [CommGroup Λ] (p : G →* Λ)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Conjugation acts trivially on `G / ker p`, since `Λ` is commutative. -/
theorem conj_mk_ker (g x : G) : ((g⁻¹ * x * g : G) : G ⧸ p.ker) = (x : G ⧸ p.ker) := by
  rw [QuotientGroup.eq, MonoidHom.mem_ker]
  simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
  rw [mul_comm (p x)⁻¹ (p g), ← mul_assoc, inv_mul_cancel, one_mul, inv_mul_cancel]

/-- A finitely supported `φ` on `Λ`, as a function on `G / ker p`. -/
def kerLiftFun (φ : Λ →₀ ℂ) : G ⧸ p.ker → ℂ :=
  fun x => φ (QuotientGroup.kerLift p x)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem kerLiftFun_mk (φ : Λ →₀ ℂ) (g : G) : kerLiftFun p φ (g : G ⧸ p.ker) = φ (p g) :=
  rfl

theorem hasCompactSupport_kerLiftFun (hN : IsOpen (p.ker : Set G)) (φ : Λ →₀ ℂ) :
    HasCompactSupport (kerLiftFun p φ) := by
  have : DiscreteTopology (G ⧸ p.ker) := QuotientGroup.discreteTopology hN
  have hfin : (Function.support (kerLiftFun p φ)).Finite := by
    refine (φ.support.finite_toSet.preimage
      (QuotientGroup.kerLift_injective p).injOn).subset fun x hx => ?_
    simpa [kerLiftFun] using hx
  rw [HasCompactSupport, tsupport, closure_discrete]
  exact hfin.isCompact

/-- The pairing `φ̂(χ) = Σ_λ φ(λ) χ(λ)` of a finitely supported `φ` with a character. -/
def finsuppCharacterSum (φ : Λ →₀ ℂ) (χ : Λ →* ℂˣ) : ℂ :=
  φ.sum fun l c => c * (χ l : ℂ)

variable {A : Subgroup G} {V : Type w} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {cπ cω : A →* ℂˣ}

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- If `χ(p(a)) cω(a) = cπ(a)` on `A`, then `π ⊗ (χ ∘ p)⁻¹` acts on `A` by `cω`. -/
theorem twist_inv_comp_central (hπc : ∀ (a : A) (x : V), π a x = (cπ a : ℂ) • x)
    (χ : Λ →* ℂˣ) (hχ : ∀ a : A, χ (p a) * cω a = cπ a) :
    ∀ (a : A) (x : V), twist (χ.comp p)⁻¹ π a x = (cω a : ℂ) • x := by
  intro a x
  change (((χ.comp p)⁻¹ (a : G) : ℂˣ) : ℂ) • π a x = _
  rw [hπc, smul_smul, ← hχ a]
  simp only [MonoidHom.inv_apply, MonoidHom.comp_apply, Units.val_mul]
  rw [Units.inv_mul_cancel_left]

end Helpers

section Orthogonality

universe u v w

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Λ : Type*} [CommGroup Λ] (p : G →* Λ)
  (A : Subgroup G) [A.Normal]
  {W : Type v} [AddCommGroup W] [Module ℂ W] {ω : Representation ℂ G W}
  {V : Type w} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {cπ cω : A →* ℂˣ} (hπc : ∀ (a : A) (x : V), π a x = (cπ a : ℂ) • x)
  (hω : ∀ (a : A) (x : W), ω a x = (cω a : ℂ) • x)

/-- The function `gA ↦ χ(p(g))⁻¹ ψ^{ω̌}_H(g) ℓ(π(g) v)` on `G / A`: the trace integrand of
`π ⊗ (χ ∘ p)⁻¹` against `ω`. -/
def twistedTraceIntegrand (hωa : IsAdmissible ω) (H : CompactOpenSubgroup G) (v : V)
    (ℓ : Module.Dual ℂ V) (χ : Λ →* ℂˣ) (hχ : ∀ a : A, χ (p a) * cω a = cπ a) :
    G ⧸ A → ℂ :=
  traceOrthogonalityIntegrand A (twist_inv_comp_central p hπc χ hχ) hω hωa H v ℓ

omit [A.Normal] in
theorem twistedTraceIntegrand_mk (hωa : IsAdmissible ω) (H : CompactOpenSubgroup G) (v : V)
    (ℓ : Module.Dual ℂ V) (χ : Λ →* ℂˣ) (hχ : ∀ a : A, χ (p a) * cω a = cπ a) (g : G) :
    twistedTraceIntegrand p A hπc hω hωa H v ℓ χ hχ (g : G ⧸ A) =
      (((χ (p g))⁻¹ : ℂˣ) : ℂ) * (traceCoefficient ω hωa.1 H g⁻¹ * ℓ (π g v)) := by
  rw [twistedTraceIntegrand, traceOrthogonalityIntegrand_mk]
  change ℓ ((((χ.comp p)⁻¹ g : ℂˣ) : ℂ) • π g v) * _ = _
  rw [map_smul, smul_eq_mul]
  simp only [MonoidHom.inv_apply, MonoidHom.comp_apply]
  ring

omit [A.Normal] in
theorem isOpen_ker_inv_comp (hN : IsOpen (p.ker : Set G)) (χ : Λ →* ℂˣ) :
    IsOpen (((χ.comp p)⁻¹).ker : Set G) := by
  refine Subgroup.isOpen_mono (fun g hg => ?_) hN
  rw [MonoidHom.mem_ker] at hg ⊢
  simp [hg]

variable [MeasurableSpace (G ⧸ A)] {ν : Measure (G ⧸ A)}

omit [A.Normal] in
theorem integrable_twistedTraceIntegrand (hωa : IsAdmissible ω)
    (hint : ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V), twist χ' π a x = (cω a : ℂ) • x)
      (v₁ : V) (ℓ₁ : SmoothDual (twist χ' π)) (v₂ : W) (ℓ₂ : SmoothDual ω),
        Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν)
    (hN : IsOpen (p.ker : Set G)) (H : CompactOpenSubgroup G) (v : V) (ℓ : SmoothDual π)
    (χ : Λ →* ℂˣ) (hχ : ∀ a : A, χ (p a) * cω a = cπ a) :
    Integrable (twistedTraceIntegrand p A hπc hω hωa H v ℓ.val χ hχ) ν := by
  unfold twistedTraceIntegrand traceOrthogonalityIntegrand
  refine integrable_finsetSum' _ fun i _ => ?_
  exact hint _ (twist_inv_comp_central p hπc χ hχ) v
    ((smoothContragredientTwistEquiv _ π (isOpen_ker_inv_comp p hN χ)).toLinearEquiv.symm ℓ)
    _ _

variable [BorelSpace (G ⧸ A)] [ν.IsHaarMeasure] [ν.IsInvInvariant] (hA : A ≤ Subgroup.center G)
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)

open scoped Classical in
/-- The Schur step of the proof of Proposition III.7.1 for the twist `π ⊗ (χ ∘ p)⁻¹`:
`∫_{G/A} χ(p(g))⁻¹ ψ^{ω̌}_H(g) ℓ(π(g) v) dg` is `d(ω)⁻¹ ℓ(v)` if `π ⊗ (χ ∘ p)⁻¹ ≅ ω` and `0`
otherwise, for `v` fixed by `H`. -/
theorem integral_twistedTraceIntegrand (hsq : IsSquareIntegrableModCentralSubgroup A hA ω ν)
    (hiω : ω.IsIrreducible) (hπa : IsAdmissible π) (hiπ : π.IsIrreducible)
    (hint : ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V), twist χ' π a x = (cω a : ℂ) • x)
      (v₁ : V) (ℓ₁ : SmoothDual (twist χ' π)) (v₂ : W) (ℓ₂ : SmoothDual ω),
        Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν)
    (hN : IsOpen (p.ker : Set G)) (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    (H : CompactOpenSubgroup G) {v : V} (hv : v ∈ fixedVectors π H.toSubgroup)
    (ℓ : SmoothDual π) (χ : Λ →* ℂˣ) (hχ : ∀ a : A, χ (p a) * cω a = cπ a) :
    ∫ q, twistedTraceIntegrand p A hπc hω hsq.1 H v ℓ.val χ hχ q ∂ν =
      if Nonempty ((twist (χ.comp p)⁻¹ π).Equiv ω) then
        ((formalDegree A hA ν hω hcof hsq hiω : ℝ) : ℂ)⁻¹ * ℓ.val v else 0 := by
  have hopen := isOpen_ker_inv_comp p hN χ
  let ℓ' : SmoothDual (twist (χ.comp p)⁻¹ π) :=
    (smoothContragredientTwistEquiv _ π hopen).toLinearEquiv.symm ℓ
  have hHker : H.toSubgroup ≤ ((χ.comp p)⁻¹).ker := fun g hg => by
    have hg' := hHN H hg
    rw [MonoidHom.mem_ker] at hg' ⊢
    simp [hg']
  split_ifs with he
  · obtain ⟨e⟩ := he
    have hv' : v ∈ fixedVectors (twist (χ.comp p)⁻¹ π) H.toSubgroup := by
      rwa [fixedVectors_twist_eq_of_le_ker _ _ _ hHker]
    have hev : e v ∈ fixedVectors ω H.toSubgroup :=
      (fixedVectorsMap e.toIntertwiningMap H.toSubgroup ⟨v, hv'⟩).2
    let ℓω : SmoothDual ω := contragredientMap e.symm.toIntertwiningMap ℓ'
    have hfun : twistedTraceIntegrand p A hπc hω hsq.1 H v ℓ.val χ hχ =
        traceOrthogonalityIntegrand A hω hω hsq.1 H (e v) ℓω.val := by
      funext q
      induction q using QuotientGroup.induction_on with
      | H g =>
        rw [twistedTraceIntegrand, traceOrthogonalityIntegrand_mk,
          traceOrthogonalityIntegrand_mk]
        congr 1
        change ℓ.val (twist (χ.comp p)⁻¹ π g v) = ℓ.val (e.symm (ω g (e v)))
        congr 1
        have h := congrArg (fun T => T (e v)) (e.symm.isIntertwining' g)
        simp only [LinearMap.comp_apply] at h
        change e.symm (ω g (e v)) = twist (χ.comp p)⁻¹ π g (e.symm (e v)) at h
        rw [h, e.symm_apply_apply]
    rw [hfun, integral_traceOrthogonalityIntegrand_eq_formalDegree_of_mem A hω ν hcof hA hsq hiω
      H hev ℓω]
    congr 1
    change ℓ.val (e.symm (e v)) = ℓ.val v
    rw [e.symm_apply_apply]
  · exact integral_traceOrthogonalityIntegrand_eq_zero A (twist_inv_comp_central p hπc χ hχ) hω
      ν hcof ((isAdmissible_twist_iff _ π hopen).2 hπa) hsq.1
      ((isIrreducible_twist_iff _ π).2 hiπ) hiω (not_nonempty_iff.1 he) (hint _ _) H v ℓ'

end Orthogonality

section Central

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

/-- If `a` acts by the scalar `c`, the compressed action satisfies
`e_K ρ(g a) e_K = c e_K ρ(g) e_K`. -/
theorem compressedAction_mul_of_smul (hρ : IsSmooth ρ) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) {a : G} {c : ℂ} (ha : ∀ x, ρ a x = c • x) (g : G) :
    Jacquet.compressedAction ρ hρ K hK (g * a) = c • Jacquet.compressedAction ρ hρ K hK g := by
  ext x
  simp only [Jacquet.compressedAction_apply, map_mul, Module.End.mul_apply, ha, map_smul,
    LinearMap.smul_apply, Submodule.coe_smul]

/-- If `a` acts by the scalar `c`, then `ψ_H(g a) = c ψ_H(g)`. -/
theorem traceCoefficient_mul_of_smul (hρ : IsSmooth ρ) (H : CompactOpenSubgroup G) {a : G}
    {c : ℂ} (ha : ∀ x, ρ a x = c • x) (g : G) :
    traceCoefficient ρ hρ H (g * a) = c * traceCoefficient ρ hρ H g := by
  rw [traceCoefficient, traceCoefficient, compressedAction_mul_of_smul hρ _ _ ha, map_smul,
    smul_eq_mul]

end Central

section Extension

variable {G : Type*} [Group G] {Λ : Type*} [CommGroup Λ] (p : G →* Λ) {A : Subgroup G}

/-- A character of `A` that is trivial on `A ∩ ker p` is the restriction along `p` of a character
of `Λ`. -/
theorem exists_character_comp_eq (ψ : A →* ℂˣ) (hψ : ∀ a : A, p a = 1 → ψ a = 1) :
    ∃ χ₀ : Λ →* ℂˣ, ∀ a : A, χ₀ (p a) = ψ a := by
  let f : A →* Λ := p.comp A.subtype
  have hker : f.ker ≤ ψ.ker := fun a ha => hψ a ha
  let ψ' : f.range →* ℂˣ := (QuotientGroup.lift f.ker ψ hker).comp
    (QuotientGroup.quotientKerEquivRange f).symm.toMonoidHom
  obtain ⟨χ, hχ⟩ := Langlands.Topology.exists_complex_character_extension f.range.subtype
    Subtype.val_injective ψ'
  refine ⟨χ, fun a => (DFunLike.congr_fun hχ ⟨f a, a, rfl⟩).trans ?_⟩
  have he : (QuotientGroup.quotientKerEquivRange f).symm ⟨f a, a, rfl⟩ = (a : A ⧸ f.ker) :=
    (MulEquiv.symm_apply_eq _).2 rfl
  simp only [ψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he]
  exact QuotientGroup.lift_mk _ _ _

end Extension

section Main

universe u v w

open scoped ENNReal

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Nonempty (CompactOpenSubgroup G)] {Ξ σ : G → ℝ}
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {μ : Measure G} [μ.IsHaarMeasure] [SFinite μ] [μ.IsMulRightInvariant]
  {K : Subgroup G} [CompactSpace K]
  {Λ : Type*} [CommGroup Λ] (p : G →* Λ)
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  (ν : Measure (G ⧸ A)) [ν.IsHaarMeasure] [ν.IsInvInvariant]
  (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
  {W : Type v} [AddCommGroup W] [Module ℂ W] {ω : Representation ℂ G W}
  {V : Type w} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {cπ cω : A →* ℂˣ} (hπc : ∀ (a : A) (x : V), π a x = (cπ a : ℂ) • x)
  (hω : ∀ (a : A) (x : W), ω a x = (cω a : ℂ) • x)

/-- The smooth contragredient `ω̌` as a bundled smooth representation. -/
abbrev contragredientRep (ω : Representation ℂ G W) : SmoothRep.{0, u, v} ℂ G :=
  SmoothRep.of (smoothContragredient ω) (isSmooth_smoothContragredient ω)

include hπc in
open scoped Classical in
/-- **The computation in the proof of Waldspurger, Proposition III.7.1**, with a chosen
character `χ₀` of `Λ` extending `cπ cω⁻¹`: for `π` irreducible, admissible and tempered,
`v` fixed by `H` and a smooth functional `ℓ`,
`ℓ(π[φ] v) = m |Q|⁻¹ Σ_η [π ⊗ (χ₀η ∘ p)⁻¹ ≅ ω] d(ω)⁻¹ φ̂(χ₀η) ℓ(v)`, the sum running over the
characters `η` of `Q = Λ / p(A)`. -/
theorem traceFamily_operator_eval_eq_sum [Fintype (Λ ⧸ A.map p)]
    (hp : Function.Surjective p) (hN : IsOpen (p.ker : Set G))
    (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker) {m : ℝ≥0∞} (hm : m ≠ ∞)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hsq : IsSquareIntegrableModCentralSubgroup A hA ω ν) (hiω : ω.IsIrreducible)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (hπa : IsAdmissible π) (hiπ : π.IsIrreducible) (hT : HasTemperedCoefficients Ξ σ π)
    (hint : ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V), twist χ' π a x = (cω a : ℂ) • x)
      (v₁ : V) (ℓ₁ : SmoothDual (twist χ' π)) (v₂ : W) (ℓ₂ : SmoothDual ω),
        Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν)
    (χ₀ : Λ →* ℂˣ) (hχ₀ : ∀ a : A, χ₀ (p a) * cω a = cπ a)
    (φ : Λ →₀ ℂ) (H : CompactOpenSubgroup G) {v : V} (hv : v ∈ fixedVectors π H.toSubgroup)
    (ℓ : SmoothDual π) :
    ℓ.val ((traceFamily (contragredientRep ω)
        (isAdmissible_smoothContragredient_of_compact_cofinal hcof ω hsq.1) hc ht hN hD
        (conj_mk_ker p) hHN (hasCompactSupport_kerLiftFun p hN φ)).operator hw hπa hT v) =
      m.toReal * (Nat.card (Λ ⧸ A.map p) : ℂ)⁻¹ *
        ∑ η : AddChar (Additive (Λ ⧸ A.map p)) ℂ,
          (if Nonempty ((twist ((χ₀ * quotientCharacter (A.map p) η).comp p)⁻¹ π).Equiv ω)
            then ((formalDegree A hA ν hω hcof hsq hiω : ℝ) : ℂ)⁻¹ *
              finsuppCharacterSum φ (χ₀ * quotientCharacter (A.map p) η)
            else 0) * ℓ.val v := by
  set B : Subgroup Λ := A.map p with hB
  have hωa : IsAdmissible ω := hsq.1
  have hχη : ∀ η : AddChar (Additive (Λ ⧸ B)) ℂ, ∀ a : A,
      (χ₀ * quotientCharacter B η) (p a) * cω a = cπ a := by
    intro η a
    rw [MonoidHom.mul_apply, quotientCharacter_of_mem B η (Subgroup.mem_map_of_mem p a.2),
      mul_one, hχ₀]
  let H0 : G ⧸ A → ℂ := twistedTraceIntegrand p A hπc hω hωa H v ℓ.val χ₀ hχ₀
  have hH0 : Integrable H0 ν :=
    integrable_twistedTraceIntegrand p A hπc hω hωa hint hN H v ℓ χ₀ hχ₀
  have hF : ∀ g : G, traceCoefficient ω hωa.1 H g⁻¹ * ℓ.val (π g v) =
      (χ₀ (p g) : ℂ) * H0 (g : G ⧸ A) := by
    intro g
    simp only [H0]
    rw [twistedTraceIntegrand_mk, ← mul_assoc, Units.mul_inv, one_mul]
  -- the fibre integrals `h(λ) = ∫_{p⁻¹(λ)} H0`
  let h : Λ → ℂ := fun l => ∫ x in p ⁻¹' {l}, H0 (x : G ⧸ A) ∂μ
  have hint0 : ∀ l, IntegrableOn (fun x : G => H0 (x : G ⧸ A)) (p ⁻¹' {l}) μ := by
    intro l
    obtain ⟨g₀, rfl⟩ := hp l
    exact integrableOn_preimage_comp_mk p hcompat hm g₀ hH0
  have hfib : ∀ l, ∫ x in p ⁻¹' {l}, (χ₀ (p x) : ℂ) * H0 (x : G ⧸ A) ∂μ =
      (χ₀ l : ℂ) * h l := by
    intro l
    rw [setIntegral_congr_fun (measurableSet_preimage_singleton p hN l)
      (g := fun x : G => (χ₀ l : ℂ) * H0 (x : G ⧸ A)) (fun x hx => by
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
        simp only [hx]), integral_const_mul]
  -- step 0: the integral of `π[φ]` as `∫ φ(p g) χ₀(p g) H0(gA)`
  rw [traceFamily_operator_eval _ _ hc ht hN hD (conj_mk_ker p) hHN _ hw hπa hT hv ℓ]
  have h0 : ∀ g : G, traceCoefficient (contragredientRep ω).representation
      (isAdmissible_smoothContragredient_of_compact_cofinal hcof ω hωa).1 H g *
        kerLiftFun p φ (g : G ⧸ p.ker) * ℓ.val (π g v) =
      φ (p g) * ((χ₀ (p g) : ℂ) * H0 (g : G ⧸ A)) := by
    intro g
    rw [kerLiftFun_mk, ← hF]
    change traceCoefficient (smoothContragredient ω) (isSmooth_smoothContragredient ω) H g *
      _ * _ = _
    rw [traceCoefficient_smoothContragredient ω hωa H g]
    ring
  refine (integral_congr_ae (Filter.Eventually.of_forall h0)).trans ?_
  -- step 1: decomposition along the fibres of `p`
  rw [integral_finsupp_comp_mul p hN φ (F := fun g => (χ₀ (p g) : ℂ) * H0 (g : G ⧸ A))
    (fun l _ => by
      obtain ⟨g₀, rfl⟩ := hp l
      refine IntegrableOn.congr_fun ((hint0 (p g₀)).const_mul (χ₀ (p g₀) : ℂ))
        (fun x hx => ?_) (measurableSet_preimage_singleton p hN _)
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      simp only [hx])]
  simp_rw [hfib]
  -- step 2: `h` is invariant under `p(A)`, hence a function on `Q = Λ / p(A)`
  have hinv : ∀ (a : A) (l : Λ), h (p a * l) = h l := by
    intro a l
    have := setIntegral_preimage_mul_left p (μ := μ) (F := fun x : G => H0 (x : G ⧸ A))
      (a := (a : G)) (c := 1) (fun g => by
        rw [one_mul, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (a : G)).2 a.2, one_mul]) l
    rw [one_mul] at this
    exact this
  let r : Λ ⧸ B → Λ := fun q => q.out
  have hr : ∀ q, (r q : Λ ⧸ B) = q := fun q => QuotientGroup.out_eq' q
  have hhr : ∀ l, h l = h (r (l : Λ ⧸ B)) := by
    intro l
    obtain ⟨a, ha, hpa⟩ := Subgroup.mem_map.1 (QuotientGroup.eq.1 (hr (l : Λ ⧸ B)).symm)
    have hrl : r (l : Λ ⧸ B) = p a * l := by
      rw [hpa, mul_comm l⁻¹, inv_mul_cancel_right]
    rw [hrl, hinv ⟨a, ha⟩ l]
  -- step 3: the Fourier coefficients of `h` are integrals over `G / A`
  let Hb : AddChar (Additive (Λ ⧸ B)) ℂ → G ⧸ A → ℂ := fun η =>
    twistedTraceIntegrand p A hπc hω hωa H v ℓ.val (χ₀ * quotientCharacter B η) (hχη η)
  have hinner : ∀ η : AddChar (Additive (Λ ⧸ B)) ℂ,
      ∑ q : Λ ⧸ B, (η (Additive.ofMul q))⁻¹ * h (r q) = m.toReal * ∫ y, Hb η y ∂ν := by
    intro η
    rw [← sum_setIntegral_preimage p hp hN hcompat
      (integrable_twistedTraceIntegrand p A hπc hω hωa hint hN H v ℓ _ (hχη η)) r hr]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_preimage_singleton p hN _) fun x hx => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp only [H0, twistedTraceIntegrand_mk, hx, MonoidHom.mul_apply, mul_inv,
      Units.val_mul, Units.val_inv_eq_inv_val, quotientCharacter_apply, hr]
    ring
  -- step 4: the Schur orthogonality relations
  have hI : ∀ η : AddChar (Additive (Λ ⧸ B)) ℂ, ∫ y, Hb η y ∂ν =
      if Nonempty ((twist ((χ₀ * quotientCharacter B η).comp p)⁻¹ π).Equiv ω) then
        ((formalDegree A hA ν hω hcof hsq hiω : ℝ) : ℂ)⁻¹ * ℓ.val v else 0 := fun η =>
    integral_twistedTraceIntegrand p A hπc hω hA hcof hsq hiω hπa hiπ hint hN hHN H hv ℓ
      (χ₀ * quotientCharacter B η) (hχη η)
  -- step 5: Fourier inversion on `Q`
  have hc0 : (Nat.card (Λ ⧸ B) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hh : ∀ l, h l = (Nat.card (Λ ⧸ B) : ℂ)⁻¹ *
      ∑ η : AddChar (Additive (Λ ⧸ B)) ℂ,
        η (Additive.ofMul (l : Λ ⧸ B)) * (m.toReal * ∫ y, Hb η y ∂ν) := by
    intro l
    rw [hhr l, eq_inv_mul_iff_mul_eq₀ hc0, card_mul_eq_sum_addChar B (fun q => h (r q))]
    simp only [hinner]
  have hφhat : ∀ η : AddChar (Additive (Λ ⧸ B)) ℂ,
      finsuppCharacterSum φ (χ₀ * quotientCharacter B η) =
        ∑ l ∈ φ.support, φ l * ((χ₀ l : ℂ) * η (Additive.ofMul (l : Λ ⧸ B))) := by
    intro η
    simp only [finsuppCharacterSum, Finsupp.sum, MonoidHom.mul_apply, Units.val_mul,
      quotientCharacter_apply]
  simp_rw [hh, hI]
  calc ∑ l ∈ φ.support, φ l * ((χ₀ l : ℂ) * ((Nat.card (Λ ⧸ B) : ℂ)⁻¹ *
          ∑ η : AddChar (Additive (Λ ⧸ B)) ℂ, η (Additive.ofMul (l : Λ ⧸ B)) *
            (m.toReal * if Nonempty ((twist ((χ₀ * quotientCharacter B η).comp p)⁻¹ π).Equiv ω)
              then ((formalDegree A hA ν hω hcof hsq hiω : ℝ) : ℂ)⁻¹ * ℓ.val v else 0)))
      = ∑ l ∈ φ.support, ∑ η : AddChar (Additive (Λ ⧸ B)) ℂ,
          (m.toReal * (Nat.card (Λ ⧸ B) : ℂ)⁻¹ *
            if Nonempty ((twist ((χ₀ * quotientCharacter B η).comp p)⁻¹ π).Equiv ω)
              then ((formalDegree A hA ν hω hcof hsq hiω : ℝ) : ℂ)⁻¹ * ℓ.val v else 0) *
          (φ l * ((χ₀ l : ℂ) * η (Additive.ofMul (l : Λ ⧸ B)))) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun η _ => ?_
        ring
    _ = ∑ η : AddChar (Additive (Λ ⧸ B)) ℂ, ∑ l ∈ φ.support,
          (m.toReal * (Nat.card (Λ ⧸ B) : ℂ)⁻¹ *
            if Nonempty ((twist ((χ₀ * quotientCharacter B η).comp p)⁻¹ π).Equiv ω)
              then ((formalDegree A hA ν hω hcof hsq hiω : ℝ) : ℂ)⁻¹ * ℓ.val v else 0) *
          (φ l * ((χ₀ l : ℂ) * η (Additive.ofMul (l : Λ ⧸ B)))) := Finset.sum_comm
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun η _ => ?_
        rw [← Finset.mul_sum, ← hφhat]
        split_ifs <;> ring

omit [A.Normal] [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)] in
include hπc hω in
/-- **The vanishing case of the computation in the proof of Proposition III.7.1**: if the central
characters of `π` and `ω` differ at some `a ∈ A ∩ ker p`, then `ℓ(π[φ] v) = 0`. -/
theorem traceFamily_operator_eval_eq_zero (hN : IsOpen (p.ker : Set G))
    (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker)
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hωa : IsAdmissible ω)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (hπa : IsAdmissible π) (hT : HasTemperedCoefficients Ξ σ π) {a : G} (haA : a ∈ A)
    (hpa : p a = 1) (hca : cπ ⟨a, haA⟩ ≠ cω ⟨a, haA⟩) (φ : Λ →₀ ℂ) (H : CompactOpenSubgroup G)
    {v : V} (hv : v ∈ fixedVectors π H.toSubgroup) (ℓ : SmoothDual π) :
    ℓ.val ((traceFamily (contragredientRep ω)
        (isAdmissible_smoothContragredient_of_compact_cofinal hcof ω hωa) hc ht hN hD
        (conj_mk_ker p) hHN (hasCompactSupport_kerLiftFun p hN φ)).operator hw hπa hT v) = 0 := by
  rw [traceFamily_operator_eval _ _ hc ht hN hD (conj_mk_ker p) hHN _ hw hπa hT hv ℓ]
  set I : G → ℂ := fun g => traceCoefficient (contragredientRep ω).representation
    (isAdmissible_smoothContragredient_of_compact_cofinal hcof ω hωa).1 H g *
      kerLiftFun p φ (g : G ⧸ p.ker) * ℓ.val (π g v) with hIdef
  set k : ℂ := (cπ ⟨a, haA⟩ : ℂ) * ((cω ⟨a, haA⟩ : ℂ))⁻¹ with hk
  have hωinv : ∀ x, ω a⁻¹ x = ((cω ⟨a, haA⟩ : ℂ))⁻¹ • x := by
    intro x
    have h := hω ⟨a, haA⟩⁻¹ x
    rw [map_inv, Units.val_inv_eq_inv_val] at h
    exact h
  have hI : ∀ g, I (a * g) = k * I g := by
    intro g
    simp only [hIdef, hk, kerLiftFun_mk]
    change traceCoefficient (smoothContragredient ω) (isSmooth_smoothContragredient ω) H (a * g) *
        _ * _ = _ * (traceCoefficient (smoothContragredient ω) (isSmooth_smoothContragredient ω)
          H g * _ * _)
    rw [traceCoefficient_smoothContragredient ω hωa H,
      traceCoefficient_smoothContragredient ω hωa H, mul_inv_rev, traceCoefficient_mul_of_smul hωa.1 H hωinv, map_mul, hpa, one_mul, map_mul,
      Module.End.mul_apply, hπc ⟨a, haA⟩, map_smul, smul_eq_mul]
    ring
  have hfix : k * ∫ g, I g ∂μ = ∫ g, I g ∂μ := by
    rw [← integral_const_mul]
    simp_rw [← hI]
    exact integral_mul_left_eq_self I a
  have hk1 : k ≠ 1 := by
    intro h1
    apply hca
    apply Units.ext
    rw [hk, mul_inv_eq_one₀ (Units.ne_zero _)] at h1
    exact h1
  have h0 : (k - 1) * ∫ g, I g ∂μ = 0 := by
    rw [sub_mul, hfix, one_mul, sub_self]
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hk1)

include hπc in
open scoped Classical in
/-- **Proposition III.7.1, the scalar `π[φ]`** (operator form of
`traceFamily_operator_eval_eq_sum`): `π[φ] = P • id` with
`P = m |Q|⁻¹ Σ_η [π ⊗ (χ₀η ∘ p)⁻¹ ≅ ω] d(ω)⁻¹ φ̂(χ₀η)`. -/
theorem traceFamily_operator_eq_smul [Fintype (Λ ⧸ A.map p)]
    (hp : Function.Surjective p) (hN : IsOpen (p.ker : Set G))
    (hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ p.ker) {m : ℝ≥0∞} (hm : m ≠ ∞)
    (hcompat : Measure.map (QuotientGroup.mk : G → G ⧸ A) (μ.restrict (p.ker : Set G)) =
      m • ν.restrict ((QuotientGroup.mk : G → G ⧸ A) '' (p.ker : Set G)))
    (hc : ConvolutionWeights μ K Ξ σ) (ht : TranslationWeights Ξ σ) (hw : L2Weights μ Ξ σ)
    (hsq : IsSquareIntegrableModCentralSubgroup A hA ω ν) (hiω : ω.IsIrreducible)
    (hD : HasRapidlyDecreasingCoefficientsOn Ξ σ p.ker (contragredientRep ω).representation)
    (hπa : IsAdmissible π) (hiπ : π.IsIrreducible) (hT : HasTemperedCoefficients Ξ σ π)
    (hint : ∀ (χ' : G →* ℂˣ) (hχ' : ∀ (a : A) (x : V), twist χ' π a x = (cω a : ℂ) • x)
      (v₁ : V) (ℓ₁ : SmoothDual (twist χ' π)) (v₂ : W) (ℓ₂ : SmoothDual ω),
        Integrable (orthogonalityIntegrand A hχ' hω v₁ ℓ₁.val v₂ ℓ₂.val) ν)
    (χ₀ : Λ →* ℂˣ) (hχ₀ : ∀ a : A, χ₀ (p a) * cω a = cπ a) (φ : Λ →₀ ℂ) (v : V) :
    (traceFamily (contragredientRep ω)
        (isAdmissible_smoothContragredient_of_compact_cofinal hcof ω hsq.1) hc ht hN hD
        (conj_mk_ker p) hHN (hasCompactSupport_kerLiftFun p hN φ)).operator hw hπa hT v =
      (m.toReal * (Nat.card (Λ ⧸ A.map p) : ℂ)⁻¹ *
        ∑ η : AddChar (Additive (Λ ⧸ A.map p)) ℂ,
          if Nonempty ((twist ((χ₀ * quotientCharacter (A.map p) η).comp p)⁻¹ π).Equiv ω)
            then ((formalDegree A hA ν hω hcof hsq hiω : ℝ) : ℂ)⁻¹ *
              finsuppCharacterSum φ (χ₀ * quotientCharacter (A.map p) η)
            else 0) • v := by
  obtain ⟨H, hv⟩ := exists_compactOpenSubgroup_fixed hπa.1 v
  refine ext_smoothDual hπa.1 fun ℓ => ?_
  rw [traceFamily_operator_eval_eq_sum p A hA ν hcof hπc hω hp hN hHN hm hcompat hc ht hw hsq hiω
    hD hπa hiπ hT hint χ₀ hχ₀ φ H hv ℓ, map_smul, smul_eq_mul, ← Finset.sum_mul]
  ring

end Main

end Langlands.HarishChandraSchwartz
