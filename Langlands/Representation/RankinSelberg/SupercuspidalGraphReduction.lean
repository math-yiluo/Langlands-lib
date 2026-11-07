import Langlands.Representation.RankinSelberg.SupercuspidalProductGamma
import Langlands.Representation.RankinSelberg.SupercuspidalProductCompletenessStatement
import Langlands.Representation.RankinSelberg.LocalConverseStatement
import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.Parabolic.InverseTransposeProductProof
import Langlands.Representation.Classification.SupercuspidalInverseTranspose
import Langlands.Group.GL.MirabolicProjection
import Langlands.Representation.Whittaker.SupercuspidalKirillovProof
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Group.GL.MirabolicGeneration
import Langlands.Representation.RankinSelberg.UnipotentQuotient
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity

/-!
# The graph argument for the supercuspidal local converse theorem

Henniart 1993, section 3.1, reduces the local converse theorem to the
completeness of Whittaker functions (Lemme 2.1). This module carries out the
reduction for irreducible supercuspidal representations.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW uX uY

section InverseTransposeClosure

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  {X : Type uX} [AddCommGroup X] [Module ℂ X] {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]

/-- The functional `ℓt ∘ Φ⁻¹ ∘ σ(w)` on `σ`, for an equivalence `Φ` from the
inverse-transpose pullback of `τ` to `σ`. -/
def transportedDualFunctional
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) X)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) Y)
    (Φ : Representation.Equiv (inverseTransposePullback τ) σ)
    (ℓt : Module.Dual ℂ X) : Module.Dual ℂ Y :=
  ℓt ∘ₗ Φ.symm.toLinearMap ∘ₗ σ (weylLong (n + 1) F)

theorem transportedDualFunctional_apply
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) X)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) Y)
    (Φ : Representation.Equiv (inverseTransposePullback τ) σ)
    (ℓt : Module.Dual ℂ X) (g : Langlands.GeneralLinear (n + 1) F) (z : Y) :
    transportedDualFunctional τ σ Φ ℓt (σ g z) =
      dualFunction n (fun h => ℓt (τ h (Φ.symm z))) g := by
  have hΦ := Representation.IntertwiningMap.isIntertwining _ _ Φ.symm.toIntertwiningMap
    (weylLong (n + 1) F * g) z
  simp only [Representation.Equiv.coe_toIntertwiningMap] at hΦ
  rw [dualFunction_apply]
  change ℓt (Φ.symm (σ (weylLong (n + 1) F) (σ g z))) = _
  rw [← Module.End.mul_apply, ← map_mul, hΦ, inverseTransposePullback_apply, map_mul,
    inverseTranspose_weylLong]

/-- The transported functional transforms by the inverse standard character
for `ψ`. -/
theorem transportedDualFunctional_mem (ψ : UnitaryAdditiveCharacter F)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) X)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) Y)
    (Φ : Representation.Equiv (inverseTransposePullback τ) σ)
    (ℓt : glInverseFunctionals (ψ.scale (-1)) n τ) :
    transportedDualFunctional τ σ Φ ℓt.val ∈ glInverseFunctionals ψ n σ := by
  intro u z
  have key : ∀ g, transportedDualFunctional τ σ Φ ℓt.val (σ g z) =
      dualFunction n (coefficientMap τ ℓt (Φ.symm z)).val g :=
    fun g => transportedDualFunctional_apply τ σ Φ ℓt.val g z
  have h0 : transportedDualFunctional τ σ Φ ℓt.val z =
      dualFunction n (coefficientMap τ ℓt (Φ.symm z)).val 1 := by
    rw [← key 1, map_one, Module.End.one_apply]
  have hφ := dualFunction_inverse_mem (ψ.scale (-1))
    (coefficientMap τ ℓt (Φ.symm z)).property u 1
  rw [mul_one, standardCharacter_scale_neg_one] at hφ
  rw [key u.val, h0]
  exact hφ

/-- Every coefficient of the test `τ` for an inverse-character functional of
`ψ.scale (-1)` is the second dual function of a coefficient of `σ`, whenever
the inverse-transpose pullback of `τ` is equivalent to `σ`. -/
theorem exists_secondDualFunction_eq (ψ : UnitaryAdditiveCharacter F)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) X)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) Y)
    (Φ : Representation.Equiv (inverseTransposePullback τ) σ)
    (ℓt : glInverseFunctionals (ψ.scale (-1)) n τ)
    (f : (coefficientModel τ ℓt).toSubmodule) :
    ∃ (ℓ : glInverseFunctionals ψ n σ) (f' : (coefficientModel σ ℓ).toSubmodule),
      (ℓt.val ≠ 0 → ℓ.val ≠ 0) ∧ secondDualFunction ψ n f'.val = f.val := by
  obtain ⟨x, hx⟩ := f.property
  let ℓ : glInverseFunctionals ψ n σ :=
    ⟨transportedDualFunctional τ σ Φ ℓt.val, transportedDualFunctional_mem ψ τ σ Φ ℓt⟩
  refine ⟨ℓ, ⟨coefficientMap σ ℓ (Φ x), ⟨Φ x, rfl⟩⟩, ?_, ?_⟩
  · intro hne hzero
    apply hne
    ext y
    have hy := LinearMap.congr_fun hzero (σ (weylLong (n + 1) F) (Φ y))
    change ℓt.val (Φ.symm (σ (weylLong (n + 1) F) (σ (weylLong (n + 1) F) (Φ y)))) = 0 at hy
    rw [← Module.End.mul_apply, ← map_mul, weylLong_mul_self, map_one, Module.End.one_apply,
      Representation.Equiv.symm_apply_apply] at hy
    exact hy
  · apply Subtype.ext
    rw [← hx]
    funext g
    change transportedDualFunctional τ σ Φ ℓt.val
        (σ (weylLong (n + 1) F * inverseTranspose (n + 1) F g) (Φ x)) = ℓt.val (τ g x)
    rw [transportedDualFunctional_apply, Representation.Equiv.symm_apply_apply,
      dualFunction_apply]
    change ℓt.val (τ (weylInverseTranspose (n + 1) F (weylInverseTranspose (n + 1) F g)) x) = _
    rw [weylInverseTranspose_involutive]

end InverseTransposeClosure

section Kirillov

variable {p : ℕ} [hp : Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V' : Type uV} [AddCommGroup V'] [Module ℂ V']

/-- The entrywise covariance of a standard Whittaker functional. -/
theorem glFunctionals_entrywise (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ r π) :
    ∀ g : Langlands.GeneralLinear (r + 1) F.Carrier,
      ((∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1) →
      ∀ v, ℓ.val (π g v) =
        (∏ i : Fin r, ψ.complex (g.val i.castSucc i.succ)) * ℓ.val v := by
  intro g hg v
  exact (mem_glFunctionals_iff_entrywise ψ π ℓ.val).mp ℓ.property g hg.1 hg.2 v

theorem unitaryAdditiveCharacter_complex_ne_one (ψ : UnitaryAdditiveCharacter F.Carrier) :
    ψ.complex ≠ 1 := by
  intro hz
  apply ψ.nontrivial
  ext x
  exact DFunLike.congr_fun hz x

/-- Supercuspidal Kirillov injectivity: a vector is determined by its Whittaker
function on the mirabolic subgroup. -/
theorem eq_of_mirabolic_coefficient_eq (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hπ : GeneralLinear.IsSupercuspidal π) (hirr : Representation.IsIrreducible π)
    (ℓ : glFunctionals ψ r π) (hℓ : ℓ.val ≠ 0) {v w : V}
    (h : ∀ q ∈ mirabolic r F.Carrier, ℓ.val (π q v) = ℓ.val (π q w)) : v = w := by
  have hK := (Langlands.supercuspidalKirillov.{uF, uV} p hp F r V π ψ.complex
    ψ.continuous_complex (unitaryAdditiveCharacter_complex_ne_one F ψ) ψ.norm_complex
    hπ hirr).2 ℓ.val hℓ (glFunctionals_entrywise F ψ π ℓ)
  obtain ⟨v0, -, huniq⟩ := hK.2 (fun g => ℓ.val (π g v)) (hK.1 v)
  exact (huniq v fun q _ => rfl).trans (huniq w fun q hq => (h q hq).symm).symm

/-- Supercuspidal Kirillov transfer: the mirabolic Whittaker function of a vector
of `π` is the mirabolic Whittaker function of a vector of `π'`. -/
theorem exists_mirabolic_coefficient_eq (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V')
    (hπ : GeneralLinear.IsSupercuspidal π) (hirr : Representation.IsIrreducible π)
    (hπ' : GeneralLinear.IsSupercuspidal π') (hirr' : Representation.IsIrreducible π')
    (ℓ : glFunctionals ψ r π) (hℓ : ℓ.val ≠ 0)
    (ℓ' : glFunctionals ψ r π') (hℓ' : ℓ'.val ≠ 0) (v : V) :
    ∃ v' : V', ∀ q ∈ mirabolic r F.Carrier, ℓ'.val (π' q v') = ℓ.val (π q v) := by
  have hK := (Langlands.supercuspidalKirillov.{uF, uV} p hp F r V π ψ.complex
    ψ.continuous_complex (unitaryAdditiveCharacter_complex_ne_one F ψ) ψ.norm_complex
    hπ hirr).2 ℓ.val hℓ (glFunctionals_entrywise F ψ π ℓ)
  have hK' := (Langlands.supercuspidalKirillov.{uF, uV} p hp F r V' π' ψ.complex
    ψ.continuous_complex (unitaryAdditiveCharacter_complex_ne_one F ψ) ψ.norm_complex
    hπ' hirr').2 ℓ'.val hℓ' (glFunctionals_entrywise F ψ π' ℓ')
  obtain ⟨v', hv', -⟩ := hK'.2 (fun g => ℓ.val (π g v)) (hK.1 v)
  exact ⟨v', hv'⟩

/-- An irreducible supercuspidal representation has a nonzero standard Whittaker
functional. -/
theorem exists_glFunctional_ne_zero (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hπ : GeneralLinear.IsSupercuspidal π) (hirr : Representation.IsIrreducible π) :
    ∃ ℓ : glFunctionals ψ r π, ℓ.val ≠ 0 := by
  obtain ⟨ℓ, hℓ, hcov⟩ := (Langlands.supercuspidalKirillov.{uF, uV} p hp F r V π ψ.complex
    ψ.continuous_complex (unitaryAdditiveCharacter_complex_ne_one F ψ) ψ.norm_complex
    hπ hirr).1
  exact ⟨⟨ℓ, (mem_glFunctionals_iff_entrywise ψ π ℓ).mpr fun g hlow hdiag v =>
    hcov g ⟨hlow, hdiag⟩ v⟩, hℓ⟩

end Kirillov

section Graph

variable {G : Type*} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V' : Type uW} [AddCommGroup V'] [Module ℂ V']

/-- The abstract graph argument. A linear relation `S` between `V` and `V'` that
is the graph of a bijection, is stable under a set `A`, and is contained in a
relation `D` that is a graph and is stable under a set `B` gives an equivalence
of representations, provided `A ∪ B` generates the group. -/
theorem nonempty_equiv_of_graph (π : Representation ℂ G V) (π' : Representation ℂ G V')
    (S D : V → V' → Prop) (A B : Set G)
    (hS_total : ∀ v, ∃ v', S v v') (hS_func : ∀ v v₁ v₂, S v v₁ → S v v₂ → v₁ = v₂)
    (hS_surj : ∀ v', ∃ v, S v v') (hS_inj : ∀ v₁ v₂ v', S v₁ v' → S v₂ v' → v₁ = v₂)
    (hS_add : ∀ v₁ v₂ v₁' v₂', S v₁ v₁' → S v₂ v₂' → S (v₁ + v₂) (v₁' + v₂'))
    (hS_smul : ∀ (c : ℂ) v v', S v v' → S (c • v) (c • v'))
    (hS_A : ∀ g ∈ A, ∀ v v', S v v' → S (π g v) (π' g v'))
    (hSD : ∀ v v', S v v' → D v v') (hD_func : ∀ v v₁ v₂, D v v₁ → D v v₂ → v₁ = v₂)
    (hD_B : ∀ g ∈ B, ∀ v v', D v v' → D (π g v) (π' g v'))
    (hgen : ∀ H : Subgroup G, A ⊆ H → B ⊆ H → H = ⊤) :
    Nonempty (π.Equiv π') := by
  classical
  choose J hJ using hS_total
  have hJeq : ∀ v v', S v v' → J v = v' := fun v v' h => hS_func v _ _ (hJ v) h
  let L : V →ₗ[ℂ] V' :=
    { toFun := J
      map_add' := fun v₁ v₂ => hJeq _ _ (hS_add _ _ _ _ (hJ v₁) (hJ v₂))
      map_smul' := fun c v => hJeq _ _ (hS_smul c _ _ (hJ v)) }
  have hbij : Function.Bijective L := by
    refine ⟨fun v₁ v₂ h => hS_inj v₁ v₂ (J v₁) (hJ v₁) ?_, fun v' => ?_⟩
    · change J v₁ = J v₂ at h
      rw [h]
      exact hJ v₂
    · obtain ⟨v, hv⟩ := hS_surj v'
      exact ⟨v, hJeq v v' hv⟩
  let H : Subgroup G :=
    { carrier := {g | ∀ v, J (π g v) = π' g (J v)}
      one_mem' := by
        intro v
        simp
      mul_mem' := by
        intro g h hg hh v
        rw [map_mul, Module.End.mul_apply, hg, hh, map_mul, Module.End.mul_apply]
      inv_mem' := by
        intro g hg v
        have h := hg (π g⁻¹ v)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply] at h
        rw [h, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply] }
  have hA : A ⊆ H := fun g hg v => hJeq _ _ (hS_A g hg v (J v) (hJ v))
  have hB : B ⊆ H := fun g hg v =>
    hD_func _ _ _ (hSD _ _ (hJ (π g v))) (hD_B g hg v (J v) (hSD _ _ (hJ v)))
  have htop := hgen H hA hB
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofBijective L hbij) fun g => ?_⟩
  apply LinearMap.ext
  intro v
  have hg : g ∈ H := htop ▸ Subgroup.mem_top g
  exact hg v

end Graph

section GammaEquation

/-- A function that is pointwise the difference of two integrable functions with
equal integrals has integral zero. -/
theorem integral_eq_zero_of_eq_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {φ φ₁ φ₂ : α → ℂ} (h : ∀ q, φ q = φ₁ q - φ₂ q) (h₁ : Integrable φ₁ μ)
    (h₂ : Integrable φ₂ μ) (heq : ∫ q, φ₁ q ∂μ = ∫ q, φ₂ q ∂μ) : ∫ q, φ q ∂μ = 0 := by
  rw [show φ = fun q => φ₁ q - φ₂ q from funext h, integral_sub h₁ h₂, heq, sub_self]

/-- Two dual continuations in gamma functional equations with the same gamma
factor, scalar and forward continuation are equal. -/
theorem GammaFunctionalEquation.dual_unique {q : ℕ} (hq : 1 < q) {ζ : ℂˣ} {e : ℕ}
    {G R Rd Rd' : RationalFunctions} (h : GammaFunctionalEquation q ζ e G R Rd)
    (h' : GammaFunctionalEquation q ζ e G R Rd') : Rd = Rd' := by
  set bad : Set ℝ :=
    {t | R.denom.eval (spectralPoint q t) = 0} ∪ {t | G.denom.eval (spectralPoint q t) = 0} ∪
      {t | Rd.denom.eval (spectralPoint q (1 - (t : ℂ))) = 0} ∪
      {t | Rd'.denom.eval (spectralPoint q (1 - (t : ℂ))) = 0} with hbad_def
  have hbad : bad.Finite :=
    (((finite_spectralPoint_roots hq (RatFunc.denom_ne_zero R)).union
      (finite_spectralPoint_roots hq (RatFunc.denom_ne_zero G))).union
      (finite_reflected_spectralPoint_roots hq (RatFunc.denom_ne_zero Rd))).union
      (finite_reflected_spectralPoint_roots hq (RatFunc.denom_ne_zero Rd'))
  have hinj : Function.Injective (fun t : ℝ => spectralPoint q (1 - (t : ℂ))) := by
    intro a b hab
    have hab' : spectralPoint q ((1 - a : ℝ) : ℂ) = spectralPoint q ((1 - b : ℝ) : ℂ) := by
      push_cast
      exact hab
    have := spectralPoint_ofReal_injective hq hab'
    linarith
  have hU : ((fun t : ℝ => spectralPoint q (1 - (t : ℂ))) '' badᶜ).Infinite :=
    hbad.infinite_compl.image hinj.injOn
  have hgood : ∀ t ∈ badᶜ, R.denom.eval (spectralPoint q t) ≠ 0 ∧
      G.denom.eval (spectralPoint q t) ≠ 0 ∧
      Rd.denom.eval (spectralPoint q (1 - (t : ℂ))) ≠ 0 ∧
      Rd'.denom.eval (spectralPoint q (1 - (t : ℂ))) ≠ 0 := by
    intro t ht
    simp only [hbad_def, Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or] at ht
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := ht
    exact ⟨h1, h2, h3, h4⟩
  apply rationalFunction_eq_of_infinite_eval_eq Rd Rd' _ hU
  · rintro x ⟨t, ht, rfl⟩
    exact (hgood t ht).2.2.1
  · rintro x ⟨t, ht, rfl⟩
    exact (hgood t ht).2.2.2
  · rintro x ⟨t, ht, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := hgood t ht
    exact (h t h1 h3 h2).trans (h' t h1 h4 h2).symm

/-- Two functions with the same rational continuation, each given everywhere by
a Laurent polynomial in the spectral variable, agree everywhere. -/
theorem eq_of_laurent_of_rationalContinuation {q : ℕ} (hq : 1 < q) {D₁ D₂ : ℂ → ℂ}
    {R : RationalFunctions} (h₁ : HasRationalContinuation q D₁ R)
    (h₂ : HasRationalContinuation q D₂ R) {L₁ L₂ : LaurentCoefficients}
    (hL₁ : ∀ s, D₁ s = laurentEval (spectralUnit (zero_lt_one.trans hq) s) L₁)
    (hL₂ : ∀ s, D₂ s = laurentEval (spectralUnit (zero_lt_one.trans hq) s) L₂) (s : ℂ) :
    D₁ s = D₂ s := by
  have hcont : ∀ (D : ℂ → ℂ) (L : LaurentCoefficients),
      (∀ s, D s = laurentEval (spectralUnit (zero_lt_one.trans hq) s) L) →
        HasRationalContinuation q D (laurentToRatFunc L) := by
    intro D L hL
    refine ⟨0, fun s _ => ?_⟩
    have hx := laurentToRatFunc_regular_and_eval (spectralUnit (zero_lt_one.trans hq) s) L
    rw [coe_spectralUnit] at hx
    exact ⟨hx.1, by rw [hx.2, hL]⟩
  have e₁ := h₁.unique hq (hcont D₁ L₁ hL₁)
  have e₂ := h₂.unique hq (hcont D₂ L₂ hL₂)
  rw [hL₁, hL₂, ← eval_laurentToRatFunc, ← eval_laurentToRatFunc, ← e₁, ← e₂]

end GammaEquation

section Restriction

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem weylLong_rankOne : weylLong 1 F = 1 := by
  apply Units.ext
  ext i j
  rw [weylLong_entry]
  simp [Subsingleton.elim j.rev i, Subsingleton.elim i j]

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- In corank one the block Weyl representative is the identity. -/
theorem blockWeylAt_succ_self (n : ℕ) (h : n < n + 1) :
    blockWeylAt (F := F) n (n + 1) h = 1 := by
  have hw : ∀ m (_ : m = 1), weylLong m F = 1 := by
    rintro m rfl
    exact weylLong_rankOne
  unfold blockWeylAt
  rw [hw (n + 1 - n) (by omega)]
  rw [show ((1 : Langlands.GeneralLinear (n + 1) F), (1 : Langlands.GeneralLinear (n + 1 - n) F))
    = 1 from rfl, map_one, map_one]

/-- Restriction of a Whittaker function along `g ↦ diag(g, I_d)`. -/
def appendRestriction (ψ : UnitaryAdditiveCharacter F) (n d : ℕ) :
    WhittakerFunctions ψ (n + d) →ₗ[ℂ] WhittakerFunctions ψ n where
  toFun φ := ⟨fun g => φ.val (appendIdentity n d g), by
    intro u g
    change φ.val (appendIdentity n d (u.val * g)) =
      (standardCharacter ψ n u : ℂ) * φ.val (appendIdentity n d g)
    rw [map_mul, ← appendUnipotent_val, φ.property, appendUnipotent_character]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsTopologicalRing F] in
@[simp] theorem appendRestriction_apply (ψ : UnitaryAdditiveCharacter F) (n d : ℕ)
    (φ : WhittakerFunctions ψ (n + d)) (g : Langlands.GeneralLinear (n + 1) F) :
    (appendRestriction ψ n d φ).val g = φ.val (appendIdentity n d g) := rfl

omit [IsTopologicalRing F] in
/-- Two Whittaker functions agreeing on `diag(g, 1)` agree on the mirabolic subgroup. -/
theorem eq_on_mirabolic_of_appendIdentity (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    (φ₁ φ₂ : WhittakerFunctions ψ (n + 1))
    (h : ∀ g : Langlands.GeneralLinear (n + 1) F,
      φ₁.val (appendIdentity n 1 g) = φ₂.val (appendIdentity n 1 g)) :
    ∀ q ∈ mirabolic (n + 1) F, φ₁.val q = φ₂.val q := by
  intro q hq
  have hdec := congrArg Subtype.val
    (Mirabolic.eq_radicalElement_mul_levi (⟨q, hq⟩ : mirabolic (n + 1) F))
  change q = (Mirabolic.radicalToUpperUnipotent
      (Mirabolic.radicalElement (Mirabolic.lastColumn ⟨q, hq⟩))).val *
    appendIdentity n 1 (Mirabolic.projection ⟨q, hq⟩) at hdec
  rw [hdec, φ₁.property, φ₂.property, h]

omit [IsTopologicalRing F] in
/-- `g ↦ diag(g, 1)` is continuous. -/
theorem continuous_appendIdentity_one (n : ℕ) :
    Continuous (appendIdentity (F := F) n 1) :=
  (GeneralLinear.rankInclusionContinuous 1).continuous

omit [TopologicalSpace F] [IsTopologicalRing F] in
theorem appendIdentity_one_mem_mirabolic (n : ℕ) (g : Langlands.GeneralLinear (n + 1) F) :
    appendIdentity n 1 g ∈ mirabolic (n + 1) F :=
  appendIdentity_succ_lastRow n 0 g

omit [IsTopologicalRing F] in
theorem translateWhittaker_one (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (φ : WhittakerFunctions ψ n) : translateWhittaker ψ n φ 1 = φ := by
  apply Subtype.ext
  funext g
  exact congrArg φ.val (mul_one g)

omit [IsTopologicalRing F] in
/-- The corank-one integrand only depends on the values `W(diag(g, 1))`. -/
theorem unequalRankIntegrand_zero_congr (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {n : ℕ} {W₁ W₂ : WhittakerFunctions ψ (n + (0 + 0 + 1))}
    (W' : InverseWhittakerFunctions ψ n)
    (h : ∀ g : Langlands.GeneralLinear (n + 1) F,
      W₁.val (appendIdentity n (0 + 0 + 1) g) = W₂.val (appendIdentity n (0 + 0 + 1) g))
    (s : ℂ) (x : Matrix (Fin 0) (Fin (n + 1)) F) :
    unequalRankIntegrand ψ abv 0 0 W₁ W' s x = unequalRankIntegrand ψ abv 0 0 W₂ W' s x := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [unequalRankIntegrand_mk, unequalRankIntegrand_mk, unequalRankMatrix_zero_rows, h]

end Restriction

section Padic

variable {p : ℕ} [hp : Fact p.Prime] {F : PadicField.{uF} p}

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

/-- For a mirabolic test function `φ` and a continuous `φ'`, the corank-one
integrand is integrable for every `s`, and the integral is one Laurent
polynomial in `q^(-s)`. -/
theorem mirabolicTest_integrable_and_laurent {n : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure (LeftUnipotentQuotient n F.Carrier)) [IsFiniteMeasureOnCompacts μ]
    (φ : WhittakerFunctions ψ (n + (0 + 0 + 1)))
    (hφ : IsMirabolicTestFunction ψ (n + (0 + 0 + 1)) φ)
    (φ' : InverseWhittakerFunctions ψ n) (hφ' : Continuous φ'.val) :
    (∀ s : ℂ, Integrable (unequalRankIntegrand ψ abv 0 0 φ φ' s 0) μ) ∧
      ∃ L : LaurentCoefficients, ∀ s : ℂ,
        unequalRankIntegral ψ abv 0 0 μ (Measure.dirac 0) φ φ' s =
          laurentEval (spectralUnit (zeroBlock_residueCardinality_pos F) s) L := by
  have hdet : Continuous (fun g : Langlands.GeneralLinear (n + 1) F.Carrier =>
      abv (Matrix.det g.val)) :=
    (NNReal.continuous_coe.comp F.canonicalTopologicalData.continuous_normalizedAbsHom).comp
      Units.continuous_val.matrix_det
  have hcont : ∀ s : ℂ, Continuous (unequalRankIntegrand ψ abv 0 0 φ φ' s 0) := by
    intro s
    have hweight : Continuous (fun g : Langlands.GeneralLinear (n + 1) F.Carrier =>
        determinantWeight abv g (s - ((0 + 0 + 1 : ℕ) : ℂ) / 2)) := by
      apply (Complex.continuous_ofReal.comp hdet).cpow continuous_const
      intro g
      exact Complex.ofReal_mem_slitPlane.mpr
        ((normalizedAbsoluteValue F.canonicalTopologicalData).pos g.det_ne_zero)
    apply (leftQuotient_isOpenQuotientMap
      (upperUnipotent (n + 1) F.Carrier)).isQuotientMap.continuous_iff.mpr
    change Continuous (fun g => φ.val (unequalRankMatrix 0 0 g 0) * φ'.val g *
      determinantWeight abv g (s - ((0 + 0 + 1 : ℕ) : ℂ) / 2))
    simp only [unequalRankMatrix_zero_rows]
    exact ((continuous_appendIdentity_of_mirabolicTest F 0 ψ φ hφ).mul hφ').mul hweight
  obtain ⟨C, hC, hsupp⟩ := exists_compact_appendIdentity_of_mirabolicTest F 0 ψ φ hφ
  refine ⟨fun s => ?_, exists_laurent_unequalRankIntegral_zero F 0 ψ μ φ φ' hcont C hC hsupp⟩
  have : T2Space (LeftUnipotentQuotient n F.Carrier) :=
    leftQuotient_t2Space _ UpperUnipotent.isClosed
  obtain ⟨C', hC', hC'supp⟩ := exists_compact_appendIdentity_support n (0 + 0 + 1) C hC
  refine (hcont s).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (hC'.image continuous_quotient_mk') ?_)
  intro q hq
  induction q using Quotient.inductionOn with
  | h g =>
    rw [unequalRankIntegrand_mk, unequalRankMatrix_zero_rows]
    by_contra hne
    have hW : φ.val (appendIdentity n (0 + 0 + 1) g) ≠ 0 := fun h =>
      hne (by rw [h, zero_mul, zero_mul])
    obtain ⟨u, c, hu1, hu2, hc, hgu⟩ := hsupp g hW
    obtain ⟨v, c', hc', hg⟩ := hC'supp g u c hu1 hu2 hc hgu
    apply hq
    refine ⟨c', hc', Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)⟩
    rw [hg, mul_inv_cancel_right]
    exact v.property

/-- In corank one the dual integral has no Weyl translation and no rectangular
variable. -/
theorem unequalRankIntegral_blockWeylAt_succ_self {n : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure (LeftUnipotentQuotient n F.Carrier)) (ν : AdditiveHaarMeasure F.Carrier)
    (h : n < n + 1) (W : WhittakerFunctions ψ (n + 1)) (W' W'' : InverseWhittakerFunctions ψ n)
    (hW : W' = W'') :
    unequalRankIntegral ψ abv 0 0 μ (rectangularMeasure ν 0 (n + 1))
        (translateWhittaker ψ (n + 1) W (blockWeylAt n (n + 1) h)) W' =
      unequalRankIntegral ψ abv 0 0 μ (Measure.dirac 0) W W'' := by
  rw [blockWeylAt_succ_self n h, translateWhittaker_one, hW, rectangularMeasure_zero_rows]

/-- With no rectangular rows the unequal-rank integral is the quotient integral
of the integrand at the zero matrix. -/
theorem unequalRankIntegral_dirac_zero {n : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure (LeftUnipotentQuotient n F.Carrier)) (W : WhittakerFunctions ψ (n + (0 + 0 + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    unequalRankIntegral ψ abv 0 0 μ (Measure.dirac 0) W W' s =
      ∫ q, unequalRankIntegrand ψ abv 0 0 W W' s 0 q ∂μ := by
  unfold unequalRankIntegral
  simp_rw [integral_dirac_zeroRows F]

/-- The restriction along `g ↦ diag(g, 1)` of a difference of two mirabolic test
functions is a compact Whittaker test function. -/
theorem isCompactWhittakerTestFunction_appendRestriction_sub {n : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier) (φ₁ φ₂ : WhittakerFunctions ψ (n + 1))
    (hφ₁ : IsMirabolicTestFunction ψ (n + 1) φ₁)
    (hφ₂ : IsMirabolicTestFunction ψ (n + 1) φ₂) :
    IsCompactWhittakerTestFunction ψ n (appendRestriction ψ n 1 (φ₁ - φ₂)) := by
  obtain ⟨K₁, hK₁⟩ := hφ₁.1
  obtain ⟨K₂, hK₂⟩ := hφ₂.1
  obtain ⟨C₁, hC₁, hsupp₁⟩ := exists_compact_appendIdentity_of_mirabolicTest F 0 ψ φ₁ hφ₁
  obtain ⟨C₂, hC₂, hsupp₂⟩ := exists_compact_appendIdentity_of_mirabolicTest F 0 ψ φ₂ hφ₂
  obtain ⟨C₁', hC₁', hC₁'supp⟩ := exists_compact_appendIdentity_support n (0 + 0 + 1) C₁ hC₁
  obtain ⟨C₂', hC₂', hC₂'supp⟩ := exists_compact_appendIdentity_support n (0 + 0 + 1) C₂ hC₂
  refine ⟨⟨(K₁ ⊓ K₂).comap (appendIdentity n 1) (continuous_appendIdentity_one n), ?_⟩,
    ⟨C₁' ∪ C₂', hC₁'.union hC₂', ?_⟩⟩
  · intro g x hx
    have hx' : appendIdentity n 1 x ∈ K₁ ⊓ K₂ := hx
    change (φ₁ - φ₂).val (appendIdentity n 1 (g * x)) = (φ₁ - φ₂).val (appendIdentity n 1 g)
    rw [map_mul]
    change φ₁.val _ - φ₂.val _ = φ₁.val _ - φ₂.val _
    rw [hK₁ _ _ (appendIdentity_one_mem_mirabolic n g) (appendIdentity_one_mem_mirabolic n x)
        (Subgroup.mem_inf.mp hx').1,
      hK₂ _ _ (appendIdentity_one_mem_mirabolic n g) (appendIdentity_one_mem_mirabolic n x)
        (Subgroup.mem_inf.mp hx').2]
  · intro g hg
    change φ₁.val (appendIdentity n 1 g) - φ₂.val (appendIdentity n 1 g) ≠ 0 at hg
    by_cases h₁ : φ₁.val (appendIdentity n 1 g) = 0
    · rw [h₁, zero_sub, neg_ne_zero] at hg
      obtain ⟨u, c, hu1, hu2, hc, hgu⟩ := hsupp₂ g hg
      obtain ⟨v, c', hc', hgv⟩ := hC₂'supp g u c hu1 hu2 hc hgu
      exact ⟨v, c', Or.inr hc', hgv⟩
    · obtain ⟨u, c, hu1, hu2, hc, hgu⟩ := hsupp₁ g h₁
      obtain ⟨v, c', hc', hgv⟩ := hC₁'supp g u c hu1 hu2 hc hgu
      exact ⟨v, c', Or.inl hc', hgv⟩

/-- First dual functions of supercuspidal coefficients are mirabolic test
functions for the inverse character. -/
theorem isMirabolicTestFunction_firstDualFunction (ψ : UnitaryAdditiveCharacter F.Carrier)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
    (hπ : GeneralLinear.IsSupercuspidal π) (hirr : Representation.IsIrreducible π)
    (ℓ : glFunctionals ψ r π) (hℓ : ℓ.val ≠ 0) (v : V) :
    IsMirabolicTestFunction (ψ.scale (-1)) r (firstDualFunction ψ r (coefficientMap π ℓ v)) := by
  rw [firstDualFunction_coefficient]
  exact isMirabolicTestFunction_of_supercuspidalKirillov Langlands.supercuspidalKirillov.{uF, uV}
    F r V (inverseTransposePullback π) (ψ.scale (-1))
    (GeneralLinear.isSupercuspidal_comp_inverseTranspose π hπ)
    ((CuspidalSupport.isIrreducible_comp_mulEquiv_iff π _).mpr hirr)
    (firstDualFunctional ψ π ℓ) (firstDualFunctional_ne_zero ψ π hℓ) ⟨_, v, rfl⟩

/-- The dual-side vanishing behind Henniart's inclusion `S ⊆ D` (section 3.1):
if the Whittaker functions of `v` and `v'` agree on every `diag(g, 1)`, then the
restriction of the difference of their first dual functions is orthogonal to
every coefficient of every normalized product of supercuspidals, for the
inverse character. -/
theorem integral_appendRestriction_firstDual_sub_eq_zero
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    {k : ℕ} {V V' : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {π : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V}
    {π' : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V'}
    (hπ : GeneralLinear.IsSupercuspidal π) (hirr : Representation.IsIrreducible π)
    (hπ' : GeneralLinear.IsSupercuspidal π') (hirr' : Representation.IsIrreducible π')
    (hG : SameProductGammaFactors.{uF, uV, uW} F ψ ν k π π')
    (ℓ : glFunctionals ψ (k + 1) π) (hℓ : ℓ.val ≠ 0)
    (ℓ' : glFunctionals ψ (k + 1) π') (hℓ' : ℓ'.val ≠ 0) (v : V) (v' : V')
    (hS : ∀ g : Langlands.GeneralLinear (k + 1) F.Carrier,
      ℓ.val (π (appendIdentity k 1 g) v) = ℓ'.val (π' (appendIdentity k 1 g) v'))
    {b : ℕ} (m : Fin b → ℕ) (h : ∑ i, (m i + 1) = k + 1)
    (W : Fin b → Type uW) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (τ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hsm : ∀ i, IsSmooth (τ i)) (hirrτ : ∀ i, Representation.IsIrreducible (τ i))
    (hscτ : ∀ i, GeneralLinear.IsSupercuspidal (τ i))
    (ℓt : glInverseFunctionals (ψ.scale (-1)) k
      (F.canonicalNormalizedProductInduced (succBlockShape m h) τ))
    (f : (coefficientModel _ ℓt).toSubmodule) :
    ∫ q, whittakerProductIntegrand (ψ.scale (-1))
        (appendRestriction (ψ.scale (-1)) k 1
          (firstDualFunction ψ (k + 1) (coefficientMap π ℓ v) -
            firstDualFunction ψ (k + 1) (coefficientMap π' ℓ' v'))) f.val q
      ∂(unipotentQuotientHaar F.Carrier k) = 0 := by
  classical
  set μ := unipotentQuotientHaar F.Carrier k with hμ_def
  set cd := firstDualFunction ψ (k + 1) (coefficientMap π ℓ v) with hcd_def
  set cd' := firstDualFunction ψ (k + 1) (coefficientMap π' ℓ' v') with hcd'_def
  have hq : 1 < qF := F.canonicalTopologicalData.residueCardinality_gt_one
  have hnr : k < k + 1 := Nat.lt_succ_self k
  have hTsm : IsSmooth (F.canonicalNormalizedProductInduced (succBlockShape m h) τ) :=
    F.canonicalTopologicalData.isSmooth_normalizedProductInduced (succBlockShape m h) τ
  obtain ⟨x, hx⟩ := f.property
  have hfcont : Continuous f.val.val := by
    rw [← hx]
    exact (Langlands.matrixCoefficient_isLocallyConstant
      (F.canonicalNormalizedProductInduced (succBlockShape m h) τ) ℓt.val x (hTsm x)).continuous
  by_cases hℓt : ℓt.val = 0
  · have hf0 : ∀ q, whittakerProductIntegrand (ψ.scale (-1))
        (appendRestriction (ψ.scale (-1)) k 1 (cd - cd')) f.val q = 0 := by
      intro q
      induction q using Quotient.inductionOn with
      | h g =>
        rw [whittakerProductIntegrand_mk, ← hx]
        change _ * ℓt.val ((F.canonicalNormalizedProductInduced (succBlockShape m h) τ) g x) = 0
        rw [hℓt, LinearMap.zero_apply, mul_zero]
    simp only [hf0, integral_zero]
  -- The inverse-transpose pullback of the test is a product of supercuspidals.
  have h' : ∑ i : Fin b, (m i.rev + 1) = k + 1 :=
    (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h
  have hsm' : ∀ i : Fin b, IsSmooth
      ((τ i.rev).comp (inverseTranspose (m i.rev + 1) F.Carrier).toMonoidHom) :=
    fun i => Langlands.isSmooth_comp _ (continuous_inverseTranspose _ F.Carrier) (hsm i.rev)
  let τ'' : ∀ i : Fin b,
      GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := m i.rev + 1) :=
    fun i => ⟨SmoothRep.of _ (hsm' i),
      (CuspidalSupport.isIrreducible_comp_mulEquiv_iff (τ i.rev) _).mpr (hirrτ i.rev),
      GeneralLinear.isSupercuspidal_comp_inverseTranspose _ (hscτ i.rev)⟩
  obtain ⟨G, hGπ, hGπ'⟩ := hG b (fun i => m i.rev) h' τ''
  set σ := F.canonicalNormalizedProductInduced (succBlockShape (fun i => m i.rev) h')
    (fun i => (τ'' i).obj.representation) with hσ
  obtain ⟨Φ⟩ := (Parabolic.inverseTransposeProduct.{uF, uW}.1 p F
    F.canonicalTopologicalData).1 (k + 1) (Nat.succ_pos k) (succBlockShape m h) W τ hsm
  have Φ' : Representation.Equiv (inverseTransposePullback
      (F.canonicalNormalizedProductInduced (succBlockShape m h) τ)) σ := Φ
  obtain ⟨ℓσ, f', hℓσ, hsec⟩ := exists_secondDualFunction_eq ψ
    (F.canonicalNormalizedProductInduced (succBlockShape m h) τ) σ Φ' ℓt f
  have hℓσ0 := hℓσ hℓt
  -- The two gamma equations with the common gamma factor.
  have hGπ0 : IsPairGammaFactor qF ψ abv ν π σ G := hGπ
  have hGπ0' : IsPairGammaFactor qF ψ abv ν π' σ G := hGπ'
  obtain ⟨-, -, -, hall⟩ := (isPairGammaFactor_of_lt hnr).mp hGπ0
  obtain ⟨-, -, -, hall'⟩ := (isPairGammaFactor_of_lt hnr).mp hGπ0'
  have hμ := unipotentQuotientHaar_isCompatible F.Carrier k
  obtain ⟨ζ, hζ, hE⟩ := hall μ hμ ℓ ℓσ hℓ hℓσ0
  obtain ⟨ζ', hζ', hE'⟩ := hall' μ hμ ℓ' ℓσ hℓ' hℓσ0
  obtain rfl := HasModelMinusOneScalar.unique hℓσ0 hζ hζ'
  have hr : k + 1 = k + (0 + 0 + 1) := rfl
  obtain ⟨R₁, Rd₁, hR₁, hRd₁, hN₁⟩ := (hE 0 0 hr).2 ⟨coefficientMap π ℓ v, v, rfl⟩ f'
  obtain ⟨R₂, Rd₂, hR₂, hRd₂, hN₂⟩ := (hE' 0 0 hr).2 ⟨coefficientMap π' ℓ' v', v', rfl⟩ f'
  -- The forward integrals agree, hence so do the dual continuations.
  have hfwd : unequalRankIntegralAt 0 0 hr ψ abv μ (rectangularMeasure ν 0 (k + 1))
      (coefficientMap π ℓ v) f'.val =
      unequalRankIntegralAt 0 0 hr ψ abv μ (rectangularMeasure ν 0 (k + 1))
      (coefficientMap π' ℓ' v') f'.val := by
    funext s
    change ∫ q, ∫ y, unequalRankIntegrand ψ abv 0 0 (coefficientMap π ℓ v) f'.val s y q
        ∂(rectangularMeasure ν 0 (k + 1)) ∂μ =
      ∫ q, ∫ y, unequalRankIntegrand ψ abv 0 0 (coefficientMap π' ℓ' v') f'.val s y q
        ∂(rectangularMeasure ν 0 (k + 1)) ∂μ
    have hW : ∀ y, unequalRankIntegrand ψ abv 0 0 (coefficientMap π ℓ v) f'.val s y =
        unequalRankIntegrand ψ abv 0 0 (coefficientMap π' ℓ' v') f'.val s y :=
      unequalRankIntegrand_zero_congr ψ abv f'.val hS s
    simp only [hW]
  rw [hfwd] at hR₁
  obtain rfl := HasRationalContinuation.unique hq hR₁ hR₂
  obtain rfl := GammaFunctionalEquation.dual_unique hq hN₁ hN₂
  -- The dual integrals are block-zero integrals of the first dual functions.
  have hD₁ : dualUnequalRankModelIntegralAt hnr 0 0 hr ψ abv μ ν π σ ℓ ℓσ
      ⟨coefficientMap π ℓ v, v, rfl⟩ f' =
      unequalRankIntegral (ψ.scale (-1)) abv 0 0 μ (Measure.dirac 0) cd f.val := by
    funext s
    change unequalRankIntegral (ψ.scale (-1)) abv 0 0 μ (rectangularMeasure ν 0 (k + 1))
      (translateWhittaker (ψ.scale (-1)) (k + 1) cd (blockWeylAt k (k + 1) hnr))
      (secondDualFunction ψ k f'.val) s = _
    exact congrFun (unequalRankIntegral_blockWeylAt_succ_self (ψ.scale (-1)) μ ν hnr cd _ _ hsec) s
  have hD₂ : dualUnequalRankModelIntegralAt hnr 0 0 hr ψ abv μ ν π' σ ℓ' ℓσ
      ⟨coefficientMap π' ℓ' v', v', rfl⟩ f' =
      unequalRankIntegral (ψ.scale (-1)) abv 0 0 μ (Measure.dirac 0) cd' f.val := by
    funext s
    change unequalRankIntegral (ψ.scale (-1)) abv 0 0 μ (rectangularMeasure ν 0 (k + 1))
      (translateWhittaker (ψ.scale (-1)) (k + 1) cd' (blockWeylAt k (k + 1) hnr))
      (secondDualFunction ψ k f'.val) s = _
    exact congrFun (unequalRankIntegral_blockWeylAt_succ_self (ψ.scale (-1)) μ ν hnr cd' _ _ hsec) s
  rw [hD₁] at hRd₁
  rw [hD₂] at hRd₂
  obtain ⟨hint, L, hL⟩ := mirabolicTest_integrable_and_laurent (ψ.scale (-1)) μ cd
    (isMirabolicTestFunction_firstDualFunction ψ hπ hirr ℓ hℓ v) f.val hfcont
  obtain ⟨hint', L', hL'⟩ := mirabolicTest_integrable_and_laurent (ψ.scale (-1)) μ cd'
    (isMirabolicTestFunction_firstDualFunction ψ hπ' hirr' ℓ' hℓ' v') f.val hfcont
  have hhalf := eq_of_laurent_of_rationalContinuation hq hRd₁ hRd₂ hL hL' (1 / 2)
  -- At `s = 1/2` the dual integrals are the pairings with the restrictions.
  have hpt : ∀ q, whittakerProductIntegrand (ψ.scale (-1))
      (appendRestriction (ψ.scale (-1)) k 1 (cd - cd')) f.val q =
      unequalRankIntegrand (ψ.scale (-1)) abv 0 0 cd f.val (1 / 2) 0 q -
        unequalRankIntegrand (ψ.scale (-1)) abv 0 0 cd' f.val (1 / 2) 0 q := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [whittakerProductIntegrand_mk, unequalRankIntegrand_mk, unequalRankIntegrand_mk,
        unequalRankMatrix_zero_rows]
      have hw : determinantWeight abv g (1 / 2 - ((0 + 0 + 1 : ℕ) : ℂ) / 2) = 1 := by
        unfold determinantWeight
        norm_num
      rw [hw]
      change (cd.val (appendIdentity k 1 g) - cd'.val (appendIdentity k 1 g)) * f.val.val g = _
      ring
  exact integral_eq_zero_of_eq_sub hpt (hint (1 / 2)) (hint' (1 / 2))
    ((unequalRankIntegral_dirac_zero (ψ.scale (-1)) μ cd f.val (1 / 2)).symm.trans
      (hhalf.trans (unequalRankIntegral_dirac_zero (ψ.scale (-1)) μ cd' f.val (1 / 2))))

/-- Henniart's inclusion `S ⊆ D` (section 3.1) on the blocks `diag(g, 1)`: given
completeness against normalized products of supercuspidals, if the Whittaker
functions of `v` and `v'` agree on every `diag(g, 1)`, then so do their first
dual functions. -/
theorem firstDual_appendIdentity_eq
    (hC : SupercuspidalProductCompletenessStatement.{uF, uW})
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    {k : ℕ} {V V' : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {π : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V}
    {π' : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V'}
    (hπ : GeneralLinear.IsSupercuspidal π) (hirr : Representation.IsIrreducible π)
    (hπ' : GeneralLinear.IsSupercuspidal π') (hirr' : Representation.IsIrreducible π')
    (hG : SameProductGammaFactors.{uF, uV, uW} F ψ ν k π π')
    (ℓ : glFunctionals ψ (k + 1) π) (hℓ : ℓ.val ≠ 0)
    (ℓ' : glFunctionals ψ (k + 1) π') (hℓ' : ℓ'.val ≠ 0) (v : V) (v' : V')
    (hS : ∀ g : Langlands.GeneralLinear (k + 1) F.Carrier,
      ℓ.val (π (appendIdentity k 1 g) v) = ℓ'.val (π' (appendIdentity k 1 g) v'))
    (g : Langlands.GeneralLinear (k + 1) F.Carrier) :
    (firstDualFunction ψ (k + 1) (coefficientMap π ℓ v)).val (appendIdentity k 1 g) =
      (firstDualFunction ψ (k + 1) (coefficientMap π' ℓ' v')).val (appendIdentity k 1 g) := by
  have hH := isCompactWhittakerTestFunction_appendRestriction_sub (ψ.scale (-1)) _ _
    (isMirabolicTestFunction_firstDualFunction ψ hπ hirr ℓ hℓ v)
    (isMirabolicTestFunction_firstDualFunction ψ hπ' hirr' ℓ' hℓ' v')
  have h0 := hC p F (ψ.scale (-1)) k (unipotentQuotientHaar F.Carrier k)
    (unipotentQuotientHaar_isCompatible F.Carrier k) _ hH (by
      intro b m h W _ _ τ hsm hirrτ hscτ ℓt f
      exact integral_appendRestriction_firstDual_sub_eq_zero ψ ν hπ hirr hπ' hirr' hG ℓ hℓ
        ℓ' hℓ' v v' hS m h W τ hsm hirrτ hscτ ℓt f)
  have hg := congrArg (fun φ : WhittakerFunctions (ψ.scale (-1)) k => φ.val g) h0
  exact sub_eq_zero.mp hg

/-- Henniart's graph argument (section 3.1): irreducible supercuspidal
representations of `GL_(k+2)` with common gamma factors against all normalized
products of supercuspidals of total rank `k+1` are equivalent, given
completeness against those products. -/
theorem nonempty_equiv_of_sameProductGammaFactors
    (hC : SupercuspidalProductCompletenessStatement.{uF, uW})
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    {k : ℕ} {V V' : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {π : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V}
    {π' : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V'}
    (hπ : GeneralLinear.IsSupercuspidal π) (hirr : Representation.IsIrreducible π)
    (hπ' : GeneralLinear.IsSupercuspidal π') (hirr' : Representation.IsIrreducible π')
    (hG : SameProductGammaFactors.{uF, uV, uW} F ψ ν k π π') :
    Nonempty (π.Equiv π') := by
  obtain ⟨ℓ, hℓ⟩ := exists_glFunctional_ne_zero F ψ π hπ hirr
  obtain ⟨ℓ', hℓ'⟩ := exists_glFunctional_ne_zero F ψ π' hπ' hirr'
  have hπd := GeneralLinear.isSupercuspidal_comp_inverseTranspose π' hπ'
  have hirrd : Representation.IsIrreducible (inverseTransposePullback π') :=
    (CuspidalSupport.isIrreducible_comp_mulEquiv_iff π'
      (inverseTranspose (k + 1 + 1) F.Carrier)).mpr hirr'
  refine nonempty_equiv_of_graph π π'
    (fun v v' => ∀ q ∈ mirabolic (k + 1) F.Carrier, ℓ.val (π q v) = ℓ'.val (π' q v'))
    (fun v v' => ∀ q ∈ mirabolic (k + 1) F.Carrier,
      (firstDualFunctional ψ π ℓ).val (inverseTransposePullback π q v) =
        (firstDualFunctional ψ π' ℓ').val (inverseTransposePullback π' q v'))
    (mirabolic (k + 1) F.Carrier : Set (Langlands.GeneralLinear (k + 1 + 1) F.Carrier))
    (inverseTranspose (k + 1 + 1) F.Carrier '' (mirabolic (k + 1) F.Carrier : Set _))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro v
    obtain ⟨v', hv'⟩ := exists_mirabolic_coefficient_eq F ψ π π' hπ hirr hπ' hirr' ℓ hℓ ℓ' hℓ' v
    exact ⟨v', fun q hq => (hv' q hq).symm⟩
  · intro v v₁ v₂ h₁ h₂
    exact eq_of_mirabolic_coefficient_eq F ψ π' hπ' hirr' ℓ' hℓ' fun q hq =>
      (h₁ q hq).symm.trans (h₂ q hq)
  · intro v'
    exact exists_mirabolic_coefficient_eq F ψ π' π hπ' hirr' hπ hirr ℓ' hℓ' ℓ hℓ v'
  · intro v₁ v₂ v' h₁ h₂
    exact eq_of_mirabolic_coefficient_eq F ψ π hπ hirr ℓ hℓ fun q hq =>
      (h₁ q hq).trans (h₂ q hq).symm
  · intro v₁ v₂ v₁' v₂' h₁ h₂ q hq
    simp only [map_add, h₁ q hq, h₂ q hq]
  · intro c v v' h q hq
    simp only [map_smul, h q hq]
  · intro g hg v v' h q hq
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    exact h (q * g) (mul_mem hq hg)
  · intro v v' h q hq
    have hS : ∀ g : Langlands.GeneralLinear (k + 1) F.Carrier,
        ℓ.val (π (appendIdentity k 1 g) v) = ℓ'.val (π' (appendIdentity k 1 g) v') :=
      fun g => h _ (appendIdentity_one_mem_mirabolic k g)
    have hmir := eq_on_mirabolic_of_appendIdentity (ψ.scale (-1)) _ _
      (firstDual_appendIdentity_eq hC ψ ν hπ hirr hπ' hirr' hG ℓ hℓ ℓ' hℓ' v v' hS) q hq
    rw [firstDualFunction_coefficient, firstDualFunction_coefficient] at hmir
    exact hmir
  · intro v v₁ v₂ h₁ h₂
    exact eq_of_mirabolic_coefficient_eq F (ψ.scale (-1)) (inverseTransposePullback π') hπd
      hirrd (firstDualFunctional ψ π' ℓ') (firstDualFunctional_ne_zero ψ π' hℓ') fun q hq =>
        (h₁ q hq).symm.trans (h₂ q hq)
  · rintro _ ⟨q₀, hq₀, rfl⟩ v v' h q hq
    change (firstDualFunctional ψ π ℓ).val
        (inverseTransposePullback π q (inverseTransposePullback π q₀ v)) =
      (firstDualFunctional ψ π' ℓ').val
        (inverseTransposePullback π' q (inverseTransposePullback π' q₀ v'))
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    exact h (q * q₀) (mul_mem hq hq₀)
  · intro H hA hB
    exact eq_top_of_mirabolic_le_of_inverseTranspose_mem (Nat.succ_pos k) H
      (fun x hx => hA hx) (fun g hg => hB ⟨g, hg, rfl⟩)

end Padic

/-- Henniart's supercuspidal local converse theorem (1993, Corollary on printed
page 340), conditional on completeness against normalized products of
supercuspidals. -/
theorem supercuspidalLocalConverse_of_completeness
    (hC : SupercuspidalProductCompletenessStatement.{uF, uW}) :
    SupercuspidalLocalConverseStatement.{uF, uV, uW} := by
  intro p _ F ψ ν k π π' hsame
  induction π using Quotient.inductionOn with
  | h A =>
    induction π' using Quotient.inductionOn with
    | h A' =>
      have hsame' := (sameClassEpsilonFactors_mk_iff F ψ ν.val k A A').mp hsame
      have hG := hsame'.productGammaFactors Langlands.supercuspidalKirillov.{uF, uV}
        Langlands.supercuspidalKirillov.{uF, uW} ν A.property.2 A.property.1 A'.property.2
        A'.property.1
      obtain ⟨e⟩ := nonempty_equiv_of_sameProductGammaFactors hC ψ ν.val A.property.2
        A.property.1 A'.property.2 A'.property.1 hG
      let _ : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
      exact Quotient.sound ⟨CategoryTheory.ObjectProperty.isoMk _ (SmoothRep.mkIso e)⟩

end Langlands.RankinSelberg
