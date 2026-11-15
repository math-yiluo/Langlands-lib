import Langlands.Global.Factors.CuspidalPairPartialGammaReduction
import Langlands.Global.RankinSelberg.UnequalAnalyticStatement
import Langlands.Global.RankinSelberg.UnequalUnfoldingStatement
import Langlands.Global.RankinSelberg.UnequalEulerFactorizationStatement
import Langlands.Global.RankinSelberg.UnequalDualEulerFactorizationStatement
import Langlands.Global.RankinSelberg.UnequalSemilocalEquationStatement
import Langlands.Global.RankinSelberg.EqualAnalyticStatement
import Langlands.Global.RankinSelberg.EqualUnfoldingStatement
import Langlands.Global.RankinSelberg.EqualEulerFactorizationStatement
import Langlands.Global.RankinSelberg.EqualDualEulerFactorizationStatement
import Langlands.Global.RankinSelberg.EqualSemilocalEquationStatement
import Langlands.Automorphic.IrreducibleCentralCharacterProof
import Langlands.Automorphic.OperatorDeterminantSliceGeometry
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The partial equation of cuspidal pairs from the global Rankin–Selberg theory

See the paired Markdown.
-/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open NumberField HeckeFunctionalEquation CuspidalPairFunctionalEquation
open CuspidalPairBoundaryNonvanishing
open LocalFactor.Archimedean
open Langlands.Global.CompletionPadic Langlands.ClassField.Global.RelativeWeilGroup
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)
open Filter
open scoped _root_.Topology

namespace CuspidalPairPartialGammaGlobal

/-! ### Analytic helpers -/

/-- A property holding off a discrete set holds at `1 - s` off a discrete set. -/
theorem eventually_codiscrete_one_sub {p : ℂ → Prop}
    (h : ∀ᶠ u in codiscrete ℂ, p u) : ∀ᶠ s in codiscrete ℂ, p (1 - s) := by
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE] at h ⊢
  intro x
  have ht : Tendsto (fun s : ℂ => 1 - s) (𝓝[≠] x) (𝓝[≠] (1 - x)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_const.sub continuous_id).tendsto x).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs ⊢
      exact fun h' => hs (sub_right_injective h')
  exact ht.eventually (h (1 - x))

/-- Meromorphy on `ℂ` passes to a function agreeing off a discrete set. -/
theorem meromorphicOn_univ_of_eventually_eq {f g : ℂ → ℂ} (hf : MeromorphicOn f Set.univ)
    (hfg : ∀ᶠ s in codiscrete ℂ, f s = g s) : MeromorphicOn g Set.univ := by
  rw [eventually_codiscrete_iff_forall_eventually_nhdsNE] at hfg
  intro x _
  exact (hf x (Set.mem_univ x)).congr (hfg x)

/-- A finite product of reciprocals of entire denominators is meromorphic on `ℂ`. -/
theorem meromorphicOn_prod_inv_denominator {ι : Type*} (s : Finset ι)
    (D : ι → LocalFactor.ReciprocalEntire) :
    MeromorphicOn (fun z => ∏ v ∈ s, ((D v).denominator z)⁻¹) Set.univ :=
  MeromorphicOn.fun_prod fun v _ z _ => ((D v).entire.analyticAt z).meromorphicAt.inv

/-- A function holomorphic off a finite set `P`, with at most simple poles at the points of
`P`, is meromorphic on `ℂ`. -/
theorem meromorphicOn_of_hasAtMostSimplePolesIn {f : ℂ → ℂ} {P : Set ℂ} (hP : P.Finite)
    (hf : RankinSelbergGlobal.HasAtMostSimplePolesIn f P) : MeromorphicOn f Set.univ := by
  intro x _
  have hPc : IsOpen Pᶜ := hP.isClosed.isOpen_compl
  have hnear : ∀ᶠ z in 𝓝[≠] x, z ∉ P :=
    (eventually_codiscrete_iff_forall_eventually_nhdsNE.mp hP.compl_mem_codiscrete) x
  by_cases hx : x ∈ P
  · obtain ⟨ε, hε, C, hC⟩ := hf.2 x hx
    refine ⟨2, ?_⟩
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [hnear] with z hz
      exact ((differentiableAt_id.sub_const x).pow 2).smul
        (hf.1.differentiableAt (hPc.mem_nhds hz))
    · have h0 : (x - x) ^ 2 • f x = 0 := by simp
      rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero' (g := fun z => max C 0 * ‖z - x‖)
        (Eventually.of_forall fun z => norm_nonneg _) ?_ ?_
      · filter_upwards [Metric.ball_mem_nhds x hε] with z hz
        by_cases hzx : z = x
        · subst hzx
          simp
        · have hb := hC z hzx (by simpa [dist_eq_norm] using hz)
          calc ‖(z - x) ^ 2 • f z‖ = ‖z - x‖ * ‖(z - x) * f z‖ := by
                rw [smul_eq_mul, pow_two, mul_assoc, norm_mul]
            _ ≤ ‖z - x‖ * max C 0 :=
                mul_le_mul_of_nonneg_left (hb.trans (le_max_left _ _)) (norm_nonneg _)
            _ = max C 0 * ‖z - x‖ := mul_comm _ _
      · have ht : Tendsto (fun z : ℂ => ‖z - x‖) (𝓝 x) (𝓝 0) := by
          simpa using ((continuous_id.sub (continuous_const (y := x))).norm.tendsto x)
        simpa using ht.const_mul (max C 0)
  · exact (hf.1.analyticAt (hPc.mem_nhds hx)).meromorphicAt

/-- Patching: a meromorphic function `L I / A` that equals `L` times a convergent Euler
product on a right half-plane, off the zeros of `A`, can be modified on a discrete set so
that it equals `L` times the Euler product on the whole half-plane. -/
theorem exists_patch {ι : Type*} {f : ι → ℂ → ℂ} {L I A : ℂ → ℂ} {σ : ℝ}
    (hL : MeromorphicOn L Set.univ) (hI : MeromorphicOn I Set.univ)
    (hA : MeromorphicOn A Set.univ) (hA0 : ∀ᶠ s in codiscrete ℂ, A s ≠ 0)
    (hf : ∀ s : ℂ, σ < s.re → ∃ p, HasProd (fun v => f v s) p ∧ I s = A s * p) :
    ∃ Λ : ℂ → ℂ, MeromorphicOn Λ Set.univ ∧
      (∀ s : ℂ, σ < s.re → ∀ p, HasProd (fun v => f v s) p → Λ s = L s * p) ∧
      ∀ᶠ s in codiscrete ℂ, Λ s = L s * I s / A s := by
  classical
  let Λ : ℂ → ℂ := fun s => if σ < s.re then L s * ∏' v, f v s else L s * I s / A s
  have hΛe : ∀ᶠ s in codiscrete ℂ, Λ s = L s * I s / A s := by
    filter_upwards [hA0] with s hs
    by_cases hσ : σ < s.re
    · obtain ⟨p, hp, hIp⟩ := hf s hσ
      simp only [Λ, hσ, ↓reduceIte, hp.tprod_eq, hIp]
      field_simp
    · simp only [Λ, hσ, ↓reduceIte]
  refine ⟨Λ, ?_, ?_, hΛe⟩
  · have hm : MeromorphicOn (fun s => L s * I s / A s) Set.univ :=
      fun x hx => ((hL x hx).mul (hI x hx)).div (hA x hx)
    exact meromorphicOn_univ_of_eventually_eq hm (hΛe.mono fun s hs => hs.symm)
  · intro s hσ p hp
    simp only [Λ, hσ, ↓reduceIte, hp.tprod_eq]

/-- The abstract form of the partial equation: from meromorphic continuations `I`, `J` of
the global integrals with `I(s) = J(1 - s)`, their Euler factorizations on a right
half-plane through meromorphic semi-local factors `A`, `B`, and the semi-local equation
`L(s) B(1 - s) = c(s) Ld(1 - s) A(s)`, the completed partial functions satisfy
`Λ(s) = c(s) Λd(1 - s)` off a discrete set. -/
theorem exists_partialEquation {ι : Type*} {f fd : ι → ℂ → ℂ} {L Ld I J A B : ℂ → ℂ} {σ : ℝ}
    (hL : MeromorphicOn L Set.univ) (hLd : MeromorphicOn Ld Set.univ)
    (hI : MeromorphicOn I Set.univ) (hJ : MeromorphicOn J Set.univ)
    (hA : MeromorphicOn A Set.univ) (hB : MeromorphicOn B Set.univ)
    (hA0 : ∀ᶠ s in codiscrete ℂ, A s ≠ 0) (hB0 : ∀ᶠ s in codiscrete ℂ, B s ≠ 0)
    (hIJ : ∀ᶠ s in codiscrete ℂ, I s = J (1 - s))
    (hf : ∀ s : ℂ, σ < s.re → ∃ p, HasProd (fun v => f v s) p ∧ I s = A s * p)
    (hfd : ∀ s : ℂ, σ < s.re → ∃ p, HasProd (fun v => fd v s) p ∧ J s = B s * p) :
    ∃ Λ Λd : ℂ → ℂ, MeromorphicOn Λ Set.univ ∧ MeromorphicOn Λd Set.univ ∧
      (∀ s : ℂ, σ < s.re → ∀ p, HasProd (fun v => f v s) p → Λ s = L s * p) ∧
      (∀ s : ℂ, σ < s.re → ∀ p, HasProd (fun v => fd v s) p → Λd s = Ld s * p) ∧
      ∀ c : ℂ → ℂ, (∀ᶠ s in codiscrete ℂ, L s * B (1 - s) = c s * Ld (1 - s) * A s) →
        ∀ᶠ s in codiscrete ℂ, Λ s = c s * Λd (1 - s) := by
  obtain ⟨Λ, hΛm, hΛ1, hΛe⟩ := exists_patch hL hI hA hA0 hf
  obtain ⟨Λd, hΛdm, hΛd1, hΛde⟩ := exists_patch hLd hJ hB hB0 hfd
  refine ⟨Λ, Λd, hΛm, hΛdm, hΛ1, hΛd1, fun c hc => ?_⟩
  filter_upwards [hΛe, eventually_codiscrete_one_sub hΛde, hA0,
    eventually_codiscrete_one_sub hB0, hIJ, hc] with s h1 h2 h3 h4 h5 h6
  rw [h1, h2, h5]
  field_simp
  linear_combination J (1 - s) * h6

/-! ### Symmetry of the pair factors -/

section Symmetry

/-- The unramified pair Euler polynomial is symmetric in the two Satake multisets. -/
theorem pairEulerPolynomial_comm {n m : ℕ} (a : Unramified.Eigenvalues n)
    (b : Unramified.Eigenvalues m) : pairEulerPolynomial a b = pairEulerPolynomial b a := by
  unfold pairEulerPolynomial
  rw [← Multiset.map_swap_product (b : Multiset ℂˣ) (a : Multiset ℂˣ), Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]
  rw [mul_comm (z.2 : ℂ) (z.1 : ℂ)]

/-- The unramified pair Euler factor is symmetric in the two presentations. -/
theorem partialEulerFactor_comm {F : Type u} [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] {r t : ℕ} {T : CuspidalOperatorRealization F r}
    {T' : CuspidalOperatorRealization F t} (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T') {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S) :
    partialEulerFactor P P' hP hP' = partialEulerFactor P' P hP' hP := by
  funext v s
  simp only [partialEulerFactor]
  rw [pairEulerPolynomial_comm]

/-- A product over a `flatMap` is the product of the partial products. -/
theorem prod_map_flatMap {α β M : Type*} [CommMonoid M] (l : List α) (f : α → List β)
    (g : β → M) : ((l.flatMap f).map g).prod = (l.map fun a => ((f a).map g).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, List.prod_append, ih, List.map_cons, List.prod_cons]

/-- Exchanging the order of a double product over two lists. -/
theorem prod_map_prod_map_comm {α β M : Type*} [CommMonoid M] (l : List α) (l' : List β)
    (f : α → β → M) :
    (l.map fun a => (l'.map fun b => f a b).prod).prod =
      (l'.map fun b => (l.map fun a => f a b).prod).prod := by
  induction l' with
  | nil => simp
  | cons b l' ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [List.prod_map_mul, ih]

/-- The product of real characters is commutative. -/
theorem realCharacterData_mul_comm (c d : RealCharacterData) : c.mul d = d.mul c := by
  cases c
  cases d
  simp only [RealCharacterData.mul, RealCharacterData.mk.injEq, add_comm, and_true]
  exact ContinuousMonoidHom.ext fun x => by
    simp only [ContinuousMonoidHom.mul_apply]
    exact mul_comm _ _

/-- The product of complex characters is commutative. -/
theorem complexCharacterData_mul_comm (c d : ComplexCharacterData) : c.mul d = d.mul c := by
  cases c
  cases d
  simp only [ComplexCharacterData.mul, ComplexCharacterData.mk.injEq, add_comm, and_true]
  exact ContinuousMonoidHom.ext fun x => by
    simp only [ContinuousMonoidHom.mul_apply]
    exact mul_comm _ _

theorem exponent_mul_conj (d e : ComplexCharacterData) :
    (d.mul e.conj).exponent = (e.mul d.conj).exponent :=
  add_comm d.exponent e.exponent

theorem natAbs_weight_mul_conj (d e : ComplexCharacterData) :
    (d.mul e.conj).weight.natAbs = (e.mul d.conj).weight.natAbs := by
  show (d.weight + -e.weight).natAbs = (e.weight + -d.weight).natAbs
  rw [← Int.natAbs_neg (d.weight + -e.weight)]
  congr 1
  ring

theorem character_mul_conj_realToComplex (d e : ComplexCharacterData) (a : ℝˣ) :
    (d.mul e.conj).character (realToComplex a) = (e.mul d.conj).character (realToComplex a) := by
  have hc : complexConjugation (realToComplex a) = realToComplex a := by
    ext
    simp [realToComplex]
  show d.character (realToComplex a) * e.character (complexConjugation (realToComplex a)) =
    e.character (realToComplex a) * d.character (complexConjugation (realToComplex a))
  rw [hc, mul_comm]

/-- The induced blocks `Ind(d ē)` and `Ind(e d̄)` have the same `L`-factor. -/
theorem lFactor_induced_mul_conj (d e : ComplexCharacterData) :
    (RealBlock.induced (d.mul e.conj)).lFactor = (RealBlock.induced (e.mul d.conj)).lFactor := by
  rw [RealBlock.lFactor_induced, RealBlock.lFactor_induced, exponent_mul_conj,
    natAbs_weight_mul_conj]

/-- The induced blocks `Ind(d ē)` and `Ind(e d̄)` have the same `ε`-factor. -/
theorem epsilon_induced_mul_conj (d e : ComplexCharacterData) (a : ℝˣ) (c : NNReal)
    (hc : 0 < c) (s : ℂ) :
    (RealBlock.induced (d.mul e.conj)).epsilon a c hc s =
      (RealBlock.induced (e.mul d.conj)).epsilon a c hc s := by
  apply Units.ext
  rw [RealBlock.coe_epsilon, RealBlock.coe_epsilon, RealBlock.coe_determinant_induced,
    RealBlock.coe_determinant_induced, RealBlock.coe_standardEpsilon_induced,
    RealBlock.coe_standardEpsilon_induced, character_mul_conj_realToComplex,
    natAbs_weight_mul_conj]
  rfl

/-- A multiplicative function on real blocks that does not distinguish `Ind(d ē)` from
`Ind(e d̄)` takes the same value on `x ⊗ y` and `y ⊗ x`. -/
theorem prod_map_tensor_comm {M : Type*} [CommMonoid M] (g : RealBlock → M)
    (hind : ∀ d e : ComplexCharacterData,
      g (RealBlock.induced (d.mul e.conj)) = g (RealBlock.induced (e.mul d.conj)))
    (x y : RealBlock) : ((x.tensor y).map g).prod = ((y.tensor x).map g).prod := by
  cases x with
  | character c =>
    cases y with
    | character d => simp only [RealBlock.tensor, realCharacterData_mul_comm c d]
    | induced d => rfl
  | induced d =>
    cases y with
    | character c => rfl
    | induced e =>
      simp only [RealBlock.tensor, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        complexCharacterData_mul_comm d e, hind d e]

theorem prod_map_realPairBlocks_eq {M : Type*} [CommMonoid M] (g : RealBlock → M)
    (xs ys : List RealBlock) : ((realPairBlocks xs ys).map g).prod =
      (xs.map fun x => (ys.map fun y => ((x.tensor y).map g).prod).prod).prod := by
  rw [realPairBlocks, prod_map_flatMap]
  congr 1
  exact List.map_congr_left fun x _ => prod_map_flatMap ys x.tensor g

/-- Such a function has the same product over the blocks of `xs ⊗ ys` and of `ys ⊗ xs`. -/
theorem prod_map_realPairBlocks_comm {M : Type*} [CommMonoid M] (g : RealBlock → M)
    (hind : ∀ d e : ComplexCharacterData,
      g (RealBlock.induced (d.mul e.conj)) = g (RealBlock.induced (e.mul d.conj)))
    (xs ys : List RealBlock) :
    ((realPairBlocks xs ys).map g).prod = ((realPairBlocks ys xs).map g).prod := by
  rw [prod_map_realPairBlocks_eq, prod_map_realPairBlocks_eq, prod_map_prod_map_comm]
  congr 1
  refine List.map_congr_left fun y _ => ?_
  congr 1
  exact List.map_congr_left fun x _ => prod_map_tensor_comm g hind x y

/-- The real pair `L`-factor is symmetric. -/
theorem realPairLFactor_denominator_comm (xs ys : List RealBlock) (z : ℂ) :
    (realPairLFactor xs ys).denominator z = (realPairLFactor ys xs).denominator z := by
  simp only [realPairLFactor, denominator_realLFactor]
  exact prod_map_realPairBlocks_comm (fun x => x.lFactor.denominator z)
    (fun d e => congrArg (·.denominator z) (lFactor_induced_mul_conj d e)) xs ys

/-- The real pair `ε`-factor is symmetric. -/
theorem realPairEpsilon_comm (xs ys : List RealBlock) (a : ℝˣ) (c : NNReal) (hc : 0 < c)
    (s : ℂ) : realPairEpsilon xs ys a c hc s = realPairEpsilon ys xs a c hc s :=
  prod_map_realPairBlocks_comm (fun x => x.epsilon a c hc s)
    (fun d e => epsilon_induced_mul_conj d e a c hc s) xs ys

theorem prod_map_complexPairBlocks_eq {M : Type*} [CommMonoid M]
    (g : ComplexCharacterData → M) (xs ys : List ComplexCharacterData) :
    ((complexPairBlocks xs ys).map g).prod =
      (xs.map fun x => (ys.map fun y => g (x.mul y)).prod).prod := by
  rw [complexPairBlocks, prod_map_flatMap]
  congr 1
  exact List.map_congr_left fun x _ => by rw [List.map_map]; rfl

/-- Every function has the same product over the blocks of `xs ⊗ ys` and of `ys ⊗ xs`. -/
theorem prod_map_complexPairBlocks_comm {M : Type*} [CommMonoid M]
    (g : ComplexCharacterData → M) (xs ys : List ComplexCharacterData) :
    ((complexPairBlocks xs ys).map g).prod = ((complexPairBlocks ys xs).map g).prod := by
  rw [prod_map_complexPairBlocks_eq, prod_map_complexPairBlocks_eq, prod_map_prod_map_comm]
  congr 1
  refine List.map_congr_left fun y _ => ?_
  congr 1
  exact List.map_congr_left fun x _ => congrArg g (complexCharacterData_mul_comm x y)

/-- The complex pair `L`-factor is symmetric. -/
theorem complexPairLFactor_denominator_comm (xs ys : List ComplexCharacterData) (z : ℂ) :
    (complexPairLFactor xs ys).denominator z = (complexPairLFactor ys xs).denominator z := by
  simp only [complexPairLFactor, denominator_complexLFactor]
  exact prod_map_complexPairBlocks_comm (fun d => d.lFactor.denominator z) xs ys

/-- The complex pair `ε`-factor is symmetric. -/
theorem complexPairEpsilon_comm (xs ys : List ComplexCharacterData) (a : ℂˣ) (c : NNReal)
    (hc : 0 < c) (s : ℂ) :
    complexPairEpsilon xs ys a c hc s = complexPairEpsilon ys xs a c hc s :=
  prod_map_complexPairBlocks_comm (fun d => d.epsilon a c hc s) xs ys

end Symmetry

/-! ### The pole set of the equal-rank integrals is finite -/

section PoleSet

open scoped CategoryTheory.MonObj

local instance poleSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (RankinSelbergGlobal.Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance poleSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (RankinSelbergGlobal.Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

/-- The exponent `w` of a power `z ↦ |det z|^w` of the idele norm is determined by it. -/
theorem detPower_injective {w₁ w₂ : ℂ}
    (h : ∀ z : RankinSelbergGlobal.Points F 1,
      RankinSelbergGlobal.detPower F 1 z w₁ = RankinSelbergGlobal.detPower F 1 z w₂) :
    w₁ = w₂ := by
  have hexp : ∀ L : ℝ, Complex.exp ((w₁ - w₂) * L) = 1 := by
    intro L
    obtain ⟨z, hz⟩ := Automorphic.OperatorDeterminantSlice.exists_scalar_determinantNorm F 1
      one_ne_zero (Units.mk0 (Real.toNNReal (Real.exp L)) (by simp [Real.exp_pos]))
    have hg := h ((GeneralLinearGroupPoints.adelicEquiv F 1).symm (AdelicGL.scalar F 1 z))
    have hn : RankinSelbergGlobal.detNorm F 1
        ((GeneralLinearGroupPoints.adelicEquiv F 1).symm (AdelicGL.scalar F 1 z)) =
          Real.exp L := by
      simp only [RankinSelbergGlobal.detNorm, MulEquiv.apply_symm_apply, hz, Units.val_mk0]
      exact Real.coe_toNNReal _ (Real.exp_pos L).le
    simp only [RankinSelbergGlobal.detPower, hn, Real.log_exp] at hg
    rw [sub_mul, Complex.exp_sub, hg, div_self (Complex.exp_ne_zero _)]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp (by simpa using hexp 1)
  by_cases hk0 : k = 0
  · rw [hk0, Int.cast_zero, zero_mul] at hk
    exact sub_eq_zero.mp hk
  · exfalso
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
    have h2 := hexp (1 / (2 * k))
    rw [hk] at h2
    have h3 : (k : ℂ) * (2 * Real.pi * Complex.I) * ((1 / (2 * k) : ℝ) : ℂ) =
        Real.pi * Complex.I := by
      push_cast
      field_simp
    rw [h3, Complex.exp_pi_mul_I] at h2
    norm_num at h2

/-- The set `P(χ)` of possible poles of the equal-rank integrals is finite. -/
theorem equalPoleSet_finite (n : ℕ) (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) :
    (RankinSelbergGlobal.equalPoleSet F n χ).Finite := by
  by_cases hw : ∃ w : ℂ, ∀ z : RankinSelbergGlobal.Points F 1,
      (Automorphic.centralIdeleCharacter F χ (RankinSelbergGlobal.ideleOf F z) : ℂ) =
        RankinSelbergGlobal.detPower F 1 z w
  · obtain ⟨w₀, hw₀⟩ := hw
    refine (Set.toFinite ({-w₀ / n, 1 - w₀ / n} : Set ℂ)).subset ?_
    rintro s ⟨w, hw, hs⟩
    have hww : w = w₀ := detPower_injective F fun z => (hw z).symm.trans (hw₀ z)
    subst hww
    rcases hs with hs | hs <;> simp [hs]
  · convert Set.finite_empty
    ext s
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨w, hw', -⟩
    exact hw ⟨w, hw'⟩

end PoleSet

/-! ### The unequal-rank and equal-rank packages -/

/-- The complex-valued form of a unitary character of `𝔸` trivial on `F` is a standard
additive character. -/
theorem isStandardAdditiveCharacter_complex {F : Type u} [Field F] [NumberField F]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hdiag : ∀ x : F, ψ (diagonal F x) = 1) :
    RankinSelbergGlobal.IsStandardAdditiveCharacter F ψ.complex := by
  refine ⟨ψ.continuous_complex, fun h1 => ψ.nontrivial ?_, fun x => ?_, ψ.norm_complex⟩
  · ext x
    have hx := congrArg (fun χ : AddChar (Adeles F) ℂ => χ x) h1
    simp only [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
      AddChar.one_apply] at hx
    rw [AddChar.one_apply, Circle.coe_one]
    exact hx
  · rw [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply]
    have hx := hdiag x
    simp only [diagonal] at hx
    rw [hx, Circle.coe_one]

/-- What the five unequal-rank premises give for `t < r`: meromorphic continuations `I`,
`J` of the global integral and of its dual with `I(s) = J(1 - s)`, meromorphic semi-local
factors `A`, `B`, nonzero off a discrete set, the partial Euler factorizations
`I = A ∏_(v ∉ S) L_v`, `J = B ∏_(v ∉ S) L∨_v` on a right half-plane, and the semi-local
equation `L_∞(s) B(1 - s) = (∏_(v ∈ S) γ_v(s)) ε_∞(s) L∨_∞(1 - s) A(s)`. -/
def UnequalPackageStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (diagonal F x) = 1) →
  ∀ (r t : ℕ) (_h : t < r) (T Td : CuspidalOperatorRealization F r)
    (T' Td' : CuspidalOperatorRealization F t),
    OperatorRealization.IsContragredientOf Td.realization T.realization →
    OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : CuspidalSpectralPresentation.{u, uQ} Td')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S),
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ),
    (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
  ∀ (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ),
    (∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)) →
  ∀ (dR dR' dRd dRd' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
    (∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td.realization v (dRd v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td'.realization v (dRd' v)) →
  ∀ (dC dC' dCd dCd' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
    (∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter Td.realization v (dCd v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter Td'.realization v (dCd' v)) →
  let infiniteL (s : ℂ) : ℂ :=
    (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
      ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹
  let dualInfiniteL (s : ℂ) : ℂ :=
    (∏ v, ((realPairLFactor (dRd v) (dRd' v)).denominator s)⁻¹) *
      ∏ v, ((complexPairLFactor (dCd v) (dCd' v)).denominator s)⁻¹
  let infiniteEpsilon (s : ℂ) : ℂ :=
    (∏ v, (realPairEpsilon (dR v) (dR' v) (aR v) (NNReal.sqrt ‖((aR v : ℝ))‖₊)
        (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ)) *
      ∏ v, (complexPairEpsilon (dC v) (dC' v) (aC v) ‖((aC v : ℂ))‖₊
        (nnnorm_pos.mpr (aC v).ne_zero) s : ℂ)
  ∃ (σ : ℝ) (I J A B : ℂ → ℂ),
    MeromorphicOn I Set.univ ∧ MeromorphicOn J Set.univ ∧
    MeromorphicOn A Set.univ ∧ MeromorphicOn B Set.univ ∧
    (∀ᶠ s in codiscrete ℂ, A s ≠ 0) ∧ (∀ᶠ s in codiscrete ℂ, B s ≠ 0) ∧
    (∀ᶠ s in codiscrete ℂ, I s = J (1 - s)) ∧
    (∀ s : ℂ, σ < s.re → ∃ p : ℂ,
      HasProd (fun v => partialEulerFactor P P' hP hP' v s) p ∧ I s = A s * p) ∧
    (∀ s : ℂ, σ < s.re → ∃ p : ℂ,
      HasProd (fun v => partialEulerFactor Pd Pd' hPd hPd' v s) p ∧ J s = B s * p) ∧
    ∀ (ψv : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v)),
      (∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψv v)) →
    ∀ (νv : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v)),
      (∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψv v) (νv v)) →
    ∀ G : FinitePlace F → RankinSelberg.RationalFunctions,
      (∀ v ∈ S,
        letI := (padicField v).canonicalTopologicalData.topology
        letI := (padicField v).canonicalGeneralLinearTopology (r + 1)
        letI := (padicField v).canonicalGeneralLinearTopology (t + 1)
        RankinSelberg.IsPadicSymmetricGammaFactor (padicField v) (ψv v) (νv v)
          ((P.localComponent v).padicObject (h v).1 (h v).2).obj.representation
          ((P'.localComponent v).padicObject (h' v).1 (h' v).2).obj.representation (G v)) →
    ∀ᶠ s in codiscrete ℂ,
      infiniteL s * B (1 - s) =
        (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
          (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) *
          infiniteEpsilon s * dualInfiniteL (1 - s) * A s

/-- The five unequal-rank premises give the unequal-rank package. -/
theorem unequalPackage (hA : RankinSelbergGlobal.UnequalAnalyticStatement.{u})
    (hU : RankinSelbergGlobal.UnequalUnfoldingStatement.{u})
    (hE : RankinSelbergGlobal.UnequalEulerFactorizationStatement.{u, uQ})
    (hD : RankinSelbergGlobal.UnequalDualEulerFactorizationStatement.{u, uQ})
    (hS : RankinSelbergGlobal.UnequalSemilocalEquationStatement.{u, uQ}) :
    UnequalPackageStatement.{u, uQ} := by
  intro F _ _ _ ψ hdiag r t hrt T Td T' Td' hTd hTd' P P' Pd Pd' h h' S hP hP' hPd hPd'
    hsupp aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd
    hdCd'
  have hstd := isStandardAdditiveCharacter_complex ψ hdiag
  obtain ⟨x, x', hx, hx', σS, A, B, hAm, hBm, hAeq, hBeq, hA0, hB0, hsem⟩ :=
    hS F ψ hdiag r t hrt T Td T' Td' hTd hTd' P P' h h' S hP hP' hsupp aR haR aC haC
      dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
  obtain ⟨C, -, hC⟩ := hU F r t hrt T T'
  obtain ⟨σE, hσE⟩ := hE F ψ hdiag r t hrt T T' P P' S hP hP' hsupp
  obtain ⟨σD, hσD⟩ := hD F ψ hdiag r t hrt T Td T' Td' hTd hTd' Pd Pd' S hPd hPd' hsupp
  obtain ⟨-, -, hIdiff, -, hIdual⟩ := hA F r t hrt T T' ψ.complex hstd x x'
  obtain ⟨hU1, hU2⟩ := hC ψ.complex hstd x x'
  let I : ℂ → ℂ := RankinSelbergGlobal.unequalIntegral F hrt ψ.complex
    (RankinSelbergGlobal.cuspFunction F T x) (RankinSelbergGlobal.cuspFunction F T' x')
  have hIdiff' : Differentiable ℂ I := hIdiff
  refine ⟨max (max C σE) (max (1 + C) (max σD σS)), I, fun u => I (1 - u), A, B,
    fun z _ => (hIdiff'.analyticAt z).meromorphicAt,
    fun z _ => ((hIdiff'.comp ((differentiable_const 1).sub differentiable_id)).analyticAt
      z).meromorphicAt,
    hAm, hBm, hA0, hB0, Eventually.of_forall fun s => by simp only [sub_sub_cancel],
    ?_, ?_, hsem⟩
  · intro s hσ
    simp only [max_lt_iff] at hσ
    obtain ⟨⟨hCs, hEs⟩, -, -, hSs⟩ := hσ
    obtain ⟨-, -, p, hp, hWp⟩ := hσE x x' hx hx' s hEs
    refine ⟨p, hp, ?_⟩
    rw [hAeq s hSs]
    exact (hU1 s hCs).2.trans hWp
  · intro u hσ
    simp only [max_lt_iff] at hσ
    obtain ⟨-, h1C, hDu, hSu⟩ := hσ
    obtain ⟨-, -, p, hp, hWp⟩ := hσD x x' hx hx' u hDu
    refine ⟨p, hp, ?_⟩
    have hu1 : (1 - u).re < -C := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have e1 := hIdual (1 - u)
    have e2 := (hU2 (1 - u) hu1).2
    rw [sub_sub_cancel] at e1 e2
    rw [hBeq u hSu]
    exact e1.trans (e2.trans hWp)

/-- What the five equal-rank premises give for `t = r`, in the form of
`UnequalPackageStatement`. -/
def EqualPackageStatement : Prop := by
  classical
  exact
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (diagonal F x) = 1) →
  ∀ (r : ℕ) (T Td : CuspidalOperatorRealization F r) (T' Td' : CuspidalOperatorRealization F r),
    OperatorRealization.IsContragredientOf Td.realization T.realization →
    OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (Pd : CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : CuspidalSpectralPresentation.{u, uQ} Td')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S),
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ (aR : {v : InfinitePlace F // v.IsReal} → ℝˣ),
    (∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)) →
  ∀ (aC : {v : InfinitePlace F // v.IsComplex} → ℂˣ),
    (∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)) →
  ∀ (dR dR' dRd dRd' : {v : InfinitePlace F // v.IsReal} → List RealBlock),
    (∀ v, OperatorRealization.HasRealPlaceParameter T.realization v (dR v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td.realization v (dRd v)) →
    (∀ v, OperatorRealization.HasRealPlaceParameter Td'.realization v (dRd' v)) →
  ∀ (dC dC' dCd dCd' : {v : InfinitePlace F // v.IsComplex} → List ComplexCharacterData),
    (∀ v, OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter Td.realization v (dCd v)) →
    (∀ v, OperatorRealization.HasComplexPlaceParameter Td'.realization v (dCd' v)) →
  let infiniteL (s : ℂ) : ℂ :=
    (∏ v, ((realPairLFactor (dR v) (dR' v)).denominator s)⁻¹) *
      ∏ v, ((complexPairLFactor (dC v) (dC' v)).denominator s)⁻¹
  let dualInfiniteL (s : ℂ) : ℂ :=
    (∏ v, ((realPairLFactor (dRd v) (dRd' v)).denominator s)⁻¹) *
      ∏ v, ((complexPairLFactor (dCd v) (dCd' v)).denominator s)⁻¹
  let infiniteEpsilon (s : ℂ) : ℂ :=
    (∏ v, (realPairEpsilon (dR v) (dR' v) (aR v) (NNReal.sqrt ‖((aR v : ℝ))‖₊)
        (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ)) *
      ∏ v, (complexPairEpsilon (dC v) (dC' v) (aC v) ‖((aC v : ℂ))‖₊
        (nnnorm_pos.mpr (aC v).ne_zero) s : ℂ)
  ∃ (σ : ℝ) (I J A B : ℂ → ℂ),
    MeromorphicOn I Set.univ ∧ MeromorphicOn J Set.univ ∧
    MeromorphicOn A Set.univ ∧ MeromorphicOn B Set.univ ∧
    (∀ᶠ s in codiscrete ℂ, A s ≠ 0) ∧ (∀ᶠ s in codiscrete ℂ, B s ≠ 0) ∧
    (∀ᶠ s in codiscrete ℂ, I s = J (1 - s)) ∧
    (∀ s : ℂ, σ < s.re → ∃ p : ℂ,
      HasProd (fun v => partialEulerFactor P P' hP hP' v s) p ∧ I s = A s * p) ∧
    (∀ s : ℂ, σ < s.re → ∃ p : ℂ,
      HasProd (fun v => partialEulerFactor Pd Pd' hPd hPd' v s) p ∧ J s = B s * p) ∧
    ∀ (ψv : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v)),
      (∀ v, IsCanonicalFiniteAdditiveComponent ψ v (ψv v)) →
    ∀ (νv : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v)),
      (∀ v, Correspondence.IsSelfDualMeasure (padicField v) (ψv v) (νv v)) →
    ∀ G : FinitePlace F → RankinSelberg.RationalFunctions,
      (∀ v ∈ S,
        letI := (padicField v).canonicalTopologicalData.topology
        letI := (padicField v).canonicalGeneralLinearTopology (r + 1)
        RankinSelberg.IsPadicSymmetricGammaFactor (padicField v) (ψv v) (νv v)
          ((P.localComponent v).padicObject (h v).1 (h v).2).obj.representation
          ((P'.localComponent v).padicObject (h' v).1 (h' v).2).obj.representation (G v)) →
    ∀ᶠ s in codiscrete ℂ,
      infiniteL s * B (1 - s) =
        (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
          (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) *
          infiniteEpsilon s * dualInfiniteL (1 - s) * A s

/-- The five equal-rank premises give the equal-rank package. -/
theorem equalPackage (hA : RankinSelbergGlobal.EqualAnalyticStatement.{u})
    (hU : RankinSelbergGlobal.EqualUnfoldingStatement.{u})
    (hE : RankinSelbergGlobal.EqualEulerFactorizationStatement.{u, uQ})
    (hD : RankinSelbergGlobal.EqualDualEulerFactorizationStatement.{u, uQ})
    (hS : RankinSelbergGlobal.EqualSemilocalEquationStatement.{u, uQ}) :
    EqualPackageStatement.{u, uQ} := by
  intro F _ _ _ ψ hdiag r T Td T' Td' hTd hTd' P P' Pd Pd' h h' S hP hP' hPd hPd'
    hsupp aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd
    hdCd'
  have hstd := isStandardAdditiveCharacter_complex ψ hdiag
  obtain ⟨ω, hω, -⟩ :=
    OperatorRealization.existsUnique_hasCentralCharacter T.realization T.irreducible
  obtain ⟨ω', hω', -⟩ :=
    OperatorRealization.existsUnique_hasCentralCharacter T'.realization T'.irreducible
  obtain ⟨x, x', Φ, hx, hx', hΦ, hΦS, σS, A, B, hAm, hBm, hAeq, hBeq, hA0, hB0, hsem⟩ :=
    hS F ψ hdiag r T Td T' Td' hTd hTd' P P' h h' S hP hP' hsupp aR haR aC haC
      dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
  obtain ⟨C, -, hC⟩ := hU F r T T' ω ω' hω hω'
  obtain ⟨σE, hσE⟩ := hE F ψ hdiag r T T' P P' S hP hP' hsupp
  obtain ⟨σD, hσD⟩ := hD F ψ hdiag r T Td T' Td' hTd hTd' Pd Pd' S hPd hPd' hsupp
  obtain ⟨σ₀, I, Idual, hI0, hIpoles, hIdpoles, -, hIeq⟩ :=
    hA F r T T' ω ω' hω hω' ψ.complex hstd x x' Φ hΦ
  obtain ⟨hU1, hU2⟩ := hC ψ.complex hstd x x' Φ hΦ
  have hfin := equalPoleSet_finite F (r + 1) (ω * ω')
  have hfin' := equalPoleSet_finite F (r + 1) (ω * ω')⁻¹
  refine ⟨max (max σ₀ (1 + C)) (max σE (max σD σS)), I, Idual, A, B,
    meromorphicOn_of_hasAtMostSimplePolesIn hfin hIpoles,
    meromorphicOn_of_hasAtMostSimplePolesIn hfin' hIdpoles, hAm, hBm, hA0, hB0, ?_, ?_, ?_,
    hsem⟩
  · filter_upwards [hfin.compl_mem_codiscrete] with s hs using hIeq s hs
  · intro s hσ
    simp only [max_lt_iff] at hσ
    obtain ⟨⟨h0s, hCs⟩, hEs, -, hSs⟩ := hσ
    obtain ⟨-, -, p, hp, hWp⟩ := hσE x x' Φ hx hx' hΦ hΦS s hEs
    refine ⟨p, hp, ?_⟩
    rw [hAeq s hSs, (hI0 s h0s).2.2.1]
    exact (hU1 s (by linarith)).2.2.trans hWp
  · intro u hσ
    simp only [max_lt_iff] at hσ
    obtain ⟨⟨h0u, hCu⟩, -, hDu, hSu⟩ := hσ
    obtain ⟨-, -, p, hp, hWp⟩ := hσD x x' Φ hx hx' hΦ hΦS u hDu
    refine ⟨p, hp, ?_⟩
    have hu1 : (1 - u).re < -C := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have e2 := (hU2 (1 - u) hu1).2.2
    rw [sub_sub_cancel] at e2
    rw [hBeq u hSu, (hI0 u h0u).2.2.2]
    exact e2.trans hWp

end CuspidalPairPartialGammaGlobal

/-! ### The reduction -/

/-- The ten premises of the global Rankin–Selberg theory (Cogdell 2004, §§2–4) imply the
partial equation of cuspidal pairs with integral gamma factors. -/
def CuspidalPairPartialGammaGlobalReductionStatement : Prop :=
  RankinSelbergGlobal.UnequalAnalyticStatement.{u} →
    RankinSelbergGlobal.UnequalUnfoldingStatement.{u} →
    RankinSelbergGlobal.UnequalEulerFactorizationStatement.{u, uQ} →
    RankinSelbergGlobal.UnequalDualEulerFactorizationStatement.{u, uQ} →
    RankinSelbergGlobal.UnequalSemilocalEquationStatement.{u, uQ} →
    RankinSelbergGlobal.EqualAnalyticStatement.{u} →
    RankinSelbergGlobal.EqualUnfoldingStatement.{u} →
    RankinSelbergGlobal.EqualEulerFactorizationStatement.{u, uQ} →
    RankinSelbergGlobal.EqualDualEulerFactorizationStatement.{u, uQ} →
    RankinSelbergGlobal.EqualSemilocalEquationStatement.{u, uQ} →
    CuspidalPairPartialGammaEquationStatement.{u, uQ}

open CuspidalPairPartialGammaGlobal in
/-- The reduction of the partial equation of cuspidal pairs to the global Rankin–Selberg
theory. -/
theorem cuspidalPairPartialGammaGlobalReduction :
    CuspidalPairPartialGammaGlobalReductionStatement.{u, uQ} := by
  intro hUA hUU hUE hUD hUS hEA hEU hEE hED hES
  have hUP := unequalPackage hUA hUU hUE hUD hUS
  have hEP := equalPackage hEA hEU hEE hED hES
  classical
  intro F _ _ _ ψ _hψ hdiag r t T Td T' Td' hTd hTd' P P' Pd Pd' h h' _hd _hd' S hP hP' hPd
    hPd' hsupp aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC'
    hdCd hdCd' infiniteL dualInfiniteL infiniteEpsilon
  have hL : MeromorphicOn infiniteL Set.univ := fun z hz =>
    ((meromorphicOn_prod_inv_denominator Finset.univ
      fun v => realPairLFactor (dR v) (dR' v)) z hz).mul
      ((meromorphicOn_prod_inv_denominator Finset.univ
        fun v => complexPairLFactor (dC v) (dC' v)) z hz)
  have hLd : MeromorphicOn dualInfiniteL Set.univ := fun z hz =>
    ((meromorphicOn_prod_inv_denominator Finset.univ
      fun v => realPairLFactor (dRd v) (dRd' v)) z hz).mul
      ((meromorphicOn_prod_inv_denominator Finset.univ
        fun v => complexPairLFactor (dCd v) (dCd' v)) z hz)
  rcases lt_trichotomy t r with hlt | heq | hgt
  · obtain ⟨σ, I, J, A, B, hI, hJ, hA, hB, hA0, hB0, hIJ, hf, hfd, hsem⟩ :=
      hUP F ψ hdiag r t hlt T Td T' Td' hTd hTd' P P' Pd Pd' h h' S hP hP' hPd hPd' hsupp
        aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
    obtain ⟨Λ, Λd, hΛ, hΛd, h1, h2, h3⟩ :=
      exists_partialEquation hL hLd hI hJ hA hB hA0 hB0 hIJ hf hfd
    exact ⟨σ, Λ, Λd, hΛ, hΛd, h1, h2, fun ψv hψv νv hνv G hG =>
      h3 (fun s => (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) * infiniteEpsilon s)
        (hsem ψv hψv νv hνv G hG)⟩
  · subst heq
    obtain ⟨σ, I, J, A, B, hI, hJ, hA, hB, hA0, hB0, hIJ, hf, hfd, hsem⟩ :=
      hEP F ψ hdiag t T Td T' Td' hTd hTd' P P' Pd Pd' h h' S hP hP' hPd hPd' hsupp
        aR haR aC haC dR dR' dRd dRd' hdR hdR' hdRd hdRd' dC dC' dCd dCd' hdC hdC' hdCd hdCd'
    obtain ⟨Λ, Λd, hΛ, hΛd, h1, h2, h3⟩ :=
      exists_partialEquation hL hLd hI hJ hA hB hA0 hB0 hIJ hf hfd
    exact ⟨σ, Λ, Λd, hΛ, hΛd, h1, h2, fun ψv hψv νv hνv G hG =>
      h3 (fun s => (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) * infiniteEpsilon s)
        (hsem ψv hψv νv hνv G hG)⟩
  · obtain ⟨σ, I, J, A, B, hI, hJ, hA, hB, hA0, hB0, hIJ, hf, hfd, hsem⟩ :=
      hUP F ψ hdiag t r hgt T' Td' T Td hTd' hTd P' P Pd' Pd h' h S hP' hP hPd' hPd hsupp
        aR haR aC haC dR' dR dRd' dRd hdR' hdR hdRd' hdRd dC' dC dCd' dCd hdC' hdC hdCd' hdCd
    rw [partialEulerFactor_comm P' P hP' hP] at hf
    rw [partialEulerFactor_comm Pd' Pd hPd' hPd] at hfd
    obtain ⟨Λ, Λd, hΛ, hΛd, h1, h2, h3⟩ :=
      exists_partialEquation hL hLd hI hJ hA hB hA0 hB0 hIJ hf hfd
    refine ⟨σ, Λ, Λd, hΛ, hΛd, h1, h2, fun ψv hψv νv hνv G hG => h3
      (fun s => (∏ v ∈ S, RatFunc.eval (RingHom.id ℂ)
        (RankinSelberg.spectralPoint (residueCardinality v) s) (G v)) * infiniteEpsilon s) ?_⟩
    filter_upwards [hsem ψv hψv νv hνv G fun v hv => by
      have hv' := hG v hv
      simp only [RankinSelberg.IsPadicSymmetricGammaFactor, not_le.mpr hgt, hgt.le,
        ↓reduceIte] at hv' ⊢
      exact hv'] with s hs
    simp only [realPairLFactor_denominator_comm (dR' _) (dR _),
      complexPairLFactor_denominator_comm (dC' _) (dC _),
      realPairLFactor_denominator_comm (dRd' _) (dRd _),
      complexPairLFactor_denominator_comm (dCd' _) (dCd _),
      realPairEpsilon_comm (dR' _) (dR _), complexPairEpsilon_comm (dC' _) (dC _)] at hs
    exact hs

end Langlands.Global
