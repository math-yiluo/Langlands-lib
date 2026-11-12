import Langlands.Representation.Derivative.MirabolicPhiMinusNondegeneratePairing
import Langlands.Representation.Derivative.MirabolicPhiMinusUnitarityStatement
import Langlands.Representation.Unitary.ConjugateSpace
import Langlands.Representation.Unitary.CountableDualAdmissible

/-!
# Normalized `Φ⁻` preserves unitarizability

Let `X` be a smooth representation of `P_(m+2)` with an invariant positive definite
Hermitian form `⟪·, ·⟫`. On the radical relations `X(V) = span {u x - x}` the radical
coefficients `c ↦ ⟪y, u(c) x⟫` have compact support, so
`I(x, y) = ∫ ψ(-c_last) ⟪x, u(c) y⟫ dc` is defined on `X(V)`. It is Hermitian, descends to
the `θ_ψ`-coinvariants `Φ⁻ X(V) ≅ Φ⁻ X`, and has covariance `|det|` under the successor
action, which the normalizing twists `|det|^(-1/2)` cancel. Positivity: replacing `x` by its
`θ_ψ`-average `x'` over a radical box `B` outside of which `⟪x, u(c) x⟫` vanishes does not
change its class, and `⟪x', u(c) x'⟫` is `ψ(c_last) ⟪x', x'⟫` on `B` and zero off `B`, so
`I(x, x) = vol(B) ⟪x', x'⟫`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis RankinSelberg Topology MeasureTheory
open Jacquet.Localization
open scoped Matrix NNReal ComplexConjugate

universe uF uV

/-! ### Descent of a Hermitian form to a quotient -/

section Descent

variable {V : Type*} {Q : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup Q] [Module ℂ Q]

/-- A Hermitian form, additive in the first variable, whose right kernel contains the kernel
of `q` depends only on the classes of both arguments. -/
theorem descended_eq (q : V →ₗ[ℂ] Q) (I : V → V → ℂ)
    (hadd : ∀ x x' y, I (x + x') y = I x y + I x' y)
    (hsymm : ∀ x y, conj (I y x) = I x y)
    (hker : ∀ x y, q y = 0 → I x y = 0) {x x' y y' : V}
    (hx : q x = q x') (hy : q y = q y') : I x y = I x' y' := by
  have hright : ∀ a b b', q b = q b' → I a b = I a b' := by
    intro a b b' hb
    have h1 : I a b = I a (b - b') + I a b' := by
      rw [← hsymm a (b - b'), ← hsymm a b', ← map_add, ← hadd, sub_add_cancel, hsymm]
    rw [h1, hker a (b - b') (by rw [map_sub, hb, sub_self]), zero_add]
  rw [hright x y y' hy, ← hsymm x' y', ← hsymm x y', hright y' x x' hx]

/-- The inner product on `Q` induced by a positive semidefinite Hermitian form on `V` whose
null vectors are exactly the kernel of the surjection `q`. -/
@[instance_reducible]
def descendedCore (q : V →ₗ[ℂ] Q) (hq : Function.Surjective q) (I : V → V → ℂ)
    (hadd : ∀ x x' y, I (x + x') y = I x y + I x' y)
    (hsmul : ∀ (r : ℂ) x y, I (r • x) y = conj r * I x y)
    (hsymm : ∀ x y, conj (I y x) = I x y)
    (hker : ∀ x y, q y = 0 → I x y = 0)
    (hpos : ∀ x, 0 ≤ (I x x).re) (hdef : ∀ x, I x x = 0 → q x = 0) :
    InnerProductSpace.Core ℂ Q where
  inner a a' := I (Function.surjInv hq a) (Function.surjInv hq a')
  conj_inner_symm a a' := hsymm _ _
  re_inner_nonneg a := hpos _
  add_left a a' a'' := by
    change I _ _ = I _ _ + I _ _
    rw [← hadd]
    exact descended_eq q I hadd hsymm hker
      (by rw [map_add, Function.surjInv_eq hq, Function.surjInv_eq hq, Function.surjInv_eq hq])
      rfl
  smul_left a a' r := by
    change I _ _ = conj r * I _ _
    rw [← hsmul]
    exact descended_eq q I hadd hsymm hker
      (by rw [map_smul, Function.surjInv_eq hq, Function.surjInv_eq hq]) rfl
  definite a ha := by
    have h := hdef _ ha
    rwa [Function.surjInv_eq hq] at h

theorem descendedCore_inner (q : V →ₗ[ℂ] Q) (hq : Function.Surjective q) (I : V → V → ℂ)
    (hadd : ∀ x x' y, I (x + x') y = I x y + I x' y)
    (hsmul : ∀ (r : ℂ) x y, I (r • x) y = conj r * I x y)
    (hsymm : ∀ x y, conj (I y x) = I x y)
    (hker : ∀ x y, q y = 0 → I x y = 0)
    (hpos : ∀ x, 0 ≤ (I x x).re) (hdef : ∀ x, I x x = 0 → q x = 0) (x y : V) :
    (descendedCore q hq I hadd hsmul hsymm hker hpos hdef).inner (q x) (q y) = I x y :=
  descended_eq q I hadd hsymm hker (Function.surjInv_eq hq _) (Function.surjInv_eq hq _)

end Descent

/-! ### Hermitian forms as pairings with the conjugate space -/

section ConjPairing

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A Hermitian form as the bilinear pairing `β(y, x̄) = ⟪x, y⟫` of `V` with `V̄`. -/
def conjPairing (c : InnerProductSpace.Core ℂ V) : V →ₗ[ℂ] ConjSpace V →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun y w => c.inner ((ConjSpace.equiv V).symm w) y)
    (fun y₁ y₂ w => CountableDual.inner_add_right c _ y₁ y₂)
    (fun r y w => CountableDual.inner_smul_right c _ y r)
    (fun y w₁ w₂ => by
      rw [map_add]
      exact c.add_left _ _ _)
    (fun r y w => by
      rw [map_smulₛₗ, c.smul_left, Complex.conj_conj, smul_eq_mul])

theorem conjPairing_apply (c : InnerProductSpace.Core ℂ V) (x y : V) :
    conjPairing c y (ConjSpace.equiv V x) = c.inner x y := rfl

/-- An invariant form gives an invariant pairing of `ρ` with `ρ̄`. -/
theorem conjPairing_invariant {G : Type*} [Monoid G] {ρ : Representation ℂ G V}
    (b : InvariantPositiveForm ρ) (g : G) (y : V) (w : ConjSpace V) :
    conjPairing b.toInnerProductCore (ρ g y) (ConjSpace.rep ρ g w) =
      conjPairing b.toInnerProductCore y w :=
  b.invariant g ((ConjSpace.equiv V).symm w) y

/-- The conjugate of a smooth representation is smooth. -/
theorem isSmooth_conjRep {G : Type*} [Group G] [TopologicalSpace G]
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) : IsSmooth (ConjSpace.rep ρ) := by
  intro v
  obtain ⟨H, hH⟩ := hρ ((ConjSpace.equiv V).symm v)
  refine ⟨H, (Representation.mem_invariants _ v).mpr fun h => ?_⟩
  exact congrArg (ConjSpace.equiv V) ((Representation.mem_invariants _ _).mp hH h)

/-- An invariant positive form restricted to a stable submodule. -/
def restrictForm {G : Type*} [Monoid G] {ρ : Representation ℂ G V}
    (b : InvariantPositiveForm ρ) (S : Submodule ℂ V) (hS : ∀ g, S ≤ S.comap (ρ g)) :
    InvariantPositiveForm (ρ.subrepresentation S hS) where
  inner x y := b.inner x y
  conj_inner_symm x y := b.conj_inner_symm x y
  re_inner_nonneg x := b.re_inner_nonneg x
  add_left x y z := b.add_left x y z
  smul_left x y r := b.smul_left x y r
  definite x hx := Subtype.ext (b.definite x hx)
  invariant g x y := b.invariant g x y

end ConjPairing

/-- `conj ψ(t) = ψ(-t)`. -/
theorem conj_complex_apply {K : Type*} [AddGroup K] [TopologicalSpace K]
    (ψ : UnitaryAdditiveCharacter K) (t : K) : conj (ψ.complex t) = ψ.complex (-t) := by
  rw [UnitaryAdditiveCharacter.complex_apply, UnitaryAdditiveCharacter.complex_apply,
    AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

/-- The two normalizing twists `|det h|^(-1/2)` cancel the covariance `|det h|`. -/
theorem phiMinusCharacter_conj_mul_mul {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {m : ℕ} (h : mirabolic m F.Carrier) :
    conj (realPowerCharacter ((T.determinantNorm (m + 1)).comp (mirabolic m F.Carrier).subtype)
        (-(1 / 2 : ℝ)) h : ℂ) *
      (realPowerCharacter ((T.determinantNorm (m + 1)).comp (mirabolic m F.Carrier).subtype)
        (-(1 / 2 : ℝ)) h : ℂ) *
      ((((T.determinantNorm (m + 1)) h.val : ℝ≥0) : ℝ) : ℂ) = 1 := by
  set x : ℝ := (((T.determinantNorm (m + 1)) h.val : ℝ≥0) : ℝ) with hxdef
  have hx : 0 < x := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  rw [coe_realPowerCharacter, MonoidHom.comp_apply, Subgroup.coe_subtype, ← hxdef,
    Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
  congr 1
  rw [← Real.rpow_add hx, ← Real.rpow_add_one hx.ne']
  norm_num

/-! ### The Hermitian transfer form on the coinvariants -/

section Coinvariant

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {m : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- An invariant positive form on a smooth representation of `P_(m+2)` whose radical
coefficients have compact support gives an inner product on the `θ_ψ`-coinvariants with
covariance `|det|` under the successor action. -/
theorem exists_coinvariantCore (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (ξ : Representation ℂ (mirabolic (m + 1) F.Carrier) V) (b : InvariantPositiveForm ξ) :
    letI := T.topology
    IsSmooth ξ →
      (∀ x y : V, ∃ N : ℤ, ∀ c ∉ latticeBox T (m + 1) N,
        b.inner y (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) x) = 0) →
      ∃ B : InnerProductSpace.Core ℂ
          (Coinvariants ξ (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m)),
        ∀ (h : mirabolic m F.Carrier) (x y : V),
          B.inner (mk ξ _ (T.mirabolicTheta ψ m) (ξ (successor h) x))
              (mk ξ _ (T.mirabolicTheta ψ m) (ξ (successor h) y)) =
            ((((T.determinantNorm (m + 1)) h.val : ℝ≥0) : ℝ) : ℂ) *
              B.inner (mk ξ _ (T.mirabolicTheta ψ m) x) (mk ξ _ (T.mirabolicTheta ψ m) y) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  have : SecondCountableTopology F.Carrier := T.secondCountableTopology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  intro hs hsupp
  let abv := normalizedAbsoluteValue T
  let μ : Measure (Fin (m + 1) → F.Carrier) := Measure.addHaar
  let β := conjPairing b.toInnerProductCore
  -- Haar scaling on the radical coordinates.
  have hχ (a : F.Carrier) (ha : a ≠ 0) :
      (Measure.addHaar : Measure F.Carrier).map (fun x => a * x) =
        (T.normalizedAbsHom a)⁻¹ • Measure.addHaar :=
    HarmonicAnalysis.padicScalarHaarScaling F T Measure.addHaar (Units.mk0 a ha)
  have hscale : ∀ k : Langlands.GeneralLinear (m + 1) F.Carrier,
      μ.map (fun x => k.val *ᵥ x) = (T.normalizedAbsHom (Matrix.det k.val))⁻¹ • μ := by
    intro k
    have h := HarmonicAnalysis.haarMeasure_map_matrix (Measure.addHaar : Measure F.Carrier)
      T.normalizedAbsHom hχ μ (EqualRankFrobenius.det_ne_zero k)
    have e : (fun x => k.val *ᵥ x) = ⇑(Matrix.toLin' k.val) := by
      funext x
      rw [Matrix.toLin'_apply]
    rw [e, h]
  have habv : ∀ a, (T.normalizedAbsHom a : ℝ) = abv a := fun _ => rfl
  -- Continuity and compact support of the radical coefficients.
  have hcont : ∀ v w, Continuous fun c : Fin (m + 1) → F.Carrier =>
      β (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) v) w := by
    intro v w
    obtain ⟨l, hl⟩ := exists_latticeBox_fixes T ξ hs v
    exact continuous_of_forall_add_eq ((isOpen_latticeBox T (m + 1) l).mem_nhds (zero_mem _))
      fun c d hd => by rw [← rep_radicalElement_mul, hl d hd]
  have hcpt : ∀ v w, HasCompactSupport fun c : Fin (m + 1) → F.Carrier =>
      β (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) v) w := by
    intro v w
    obtain ⟨N, hN⟩ := hsupp v ((ConjSpace.equiv V).symm w)
    exact HasCompactSupport.intro (isCompact_latticeBox T (m + 1) N) hN
  -- The Hermitian transfer form `I(x, y) = ∫ ψ(-c_last) ⟪x, u(c) y⟫ dc`.
  let L := transferForm μ ψ ξ β hcont hcpt
  let I : V → V → ℂ := fun x y => L y (ConjSpace.equiv V x)
  have hI : ∀ x y, I x y = ∫ c, ψ.complex (-(c (Fin.last m))) *
      b.inner x (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) y) ∂μ := fun _ _ => rfl
  have hadd : ∀ x x' y, I (x + x') y = I x y + I x' y := by
    intro x x' y
    change L y (ConjSpace.equiv V (x + x')) = L y (ConjSpace.equiv V x) + L y (ConjSpace.equiv V x')
    rw [map_add, map_add]
  have hsmul : ∀ (r : ℂ) x y, I (r • x) y = conj r * I x y := by
    intro r x y
    change L y (ConjSpace.equiv V (r • x)) = conj r * L y (ConjSpace.equiv V x)
    rw [map_smulₛₗ, map_smul, smul_eq_mul]
  have hsymm : ∀ x y, conj (I y x) = I x y := by
    intro x y
    rw [hI, hI, ← integral_conj]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)).trans
      (integral_neg_eq_self _ μ)
    rw [map_mul, conj_complex_apply, b.conj_inner_symm, Pi.neg_apply,
      ← b.invariant (radicalElement (-c) : mirabolic (m + 1) F.Carrier)
        (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) x) y,
      rep_radicalElement_mul, neg_add_cancel, rep_radicalElement_zero]
  set θ := T.mirabolicTheta ψ m with hθdef
  have hθ : IsOpen (θ.ker : Set (radical (m + 1) F.Carrier)) := T.mirabolicTheta_isOpen_ker ψ m
  have hθu : ∀ d : Fin (m + 1) → F.Carrier,
      (θ (radicalElement d) : ℂ) = ψ.complex (d (Fin.last m)) :=
    fun d => theta_radicalElement ψ m d
  have hker : ∀ x y, mk ξ _ θ y = 0 → I x y = 0 := by
    intro x y hy
    rw [mk_eq_zero] at hy
    have hle := (relations_le_ker_iff ξ _ θ (L.flip (ConjSpace.equiv V x))).2 (fun u v => by
      obtain ⟨d, rfl⟩ : ∃ d, radicalElement d = u := ⟨_, radicalElement_coordinates u⟩
      rw [LinearMap.flip_apply, LinearMap.flip_apply, transferForm_apply, transferForm_apply,
        transferIntegral_radical_left, hθu, smul_eq_mul])
    exact LinearMap.mem_ker.mp (hle hy)
  have hwd : ∀ {x x' y y' : V}, mk ξ _ θ x = mk ξ _ θ x' → mk ξ _ θ y = mk ξ _ θ y' →
      I x y = I x' y' := fun hx hy => descended_eq (mk ξ _ θ) I hadd hsymm hker hx hy
  -- Positivity: `I(x, x) = vol(B) ⟪x', x'⟫` for the `θ_ψ`-average `x'` of `x` over a box `B`.
  have hself : ∀ x : V, ∃ x' : V, mk ξ _ θ x = mk ξ _ θ x' ∧
      ∃ r : ℝ, 0 < r ∧ I x' x' = (r : ℂ) * b.inner x' x' := by
    intro x
    obtain ⟨N, hN⟩ := hsupp x x
    let H := radicalBox T m N
    have hH := isCompact_radicalBox T m N
    set x' := characterAverage hs hθ H hH x with hx'def
    have hxinv : ∀ d ∈ latticeBox T (m + 1) N,
        ξ (radicalElement d : mirabolic (m + 1) F.Carrier) x' =
          ψ.complex (d (Fin.last m)) • x' := by
      intro d hd
      have hmem := Compact.averageMap_mem_fixedVectors (twistedRestriction ξ _ θ)
        (isSmooth_twistedRestriction hs hθ) H hH x
      have hu : radicalElement d ∈ H := by
        rw [mem_radicalBox, radicalCoordinates_element]
        exact hd
      have h1 : twistedRestriction ξ _ θ (radicalElement d) x' = x' :=
        (Representation.mem_invariants _ _).mp hmem ⟨_, hu⟩
      rw [twistedRestriction_apply] at h1
      calc ξ (radicalElement d : mirabolic (m + 1) F.Carrier) x' =
            (θ (radicalElement d) : ℂ) • ((θ (radicalElement d) : ℂ)⁻¹ •
              ξ (radicalElement d : mirabolic (m + 1) F.Carrier) x') := by
            rw [smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
        _ = _ := by rw [h1, hθu]
    -- Off the box the coefficient `⟪x', u(c) x'⟫` vanishes.
    have hout : ∀ c ∉ latticeBox T (m + 1) N,
        b.inner x' (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) x') = 0 := by
      intro c hc
      have hA : b.inner x' (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) x') =
          b.inner x' (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) x) := by
        refine apply_characterAverage hs hθ H hH
          ((CountableDual.rightFunctional b.toInnerProductCore x') ∘ₗ
            ξ (radicalElement c : mirabolic (m + 1) F.Carrier)) x (fun n hn => ?_)
        obtain ⟨d, rfl⟩ : ∃ d, radicalElement d = n := ⟨_, radicalElement_coordinates n⟩
        have hd : d ∈ latticeBox T (m + 1) N := by
          rw [mem_radicalBox, radicalCoordinates_element] at hn
          exact hn
        change b.inner x' (ξ (radicalElement c : mirabolic (m + 1) F.Carrier)
            (ξ (radicalElement d : mirabolic (m + 1) F.Carrier) x)) =
          (θ (radicalElement d) : ℂ) *
            b.inner x' (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) x)
        rw [rep_radicalElement_mul,
          ← b.invariant (radicalElement (-d) : mirabolic (m + 1) F.Carrier) x'
            (ξ (radicalElement (c + d) : mirabolic (m + 1) F.Carrier) x),
          hxinv (-d) (neg_mem hd), rep_radicalElement_mul, b.smul_left, conj_complex_apply, hθu,
          Pi.neg_apply, neg_neg, show -d + (c + d) = c from by abel]
      have hB : b.inner x (ξ (radicalElement (-c) : mirabolic (m + 1) F.Carrier) x') = 0 := by
        let ℓ := (CountableDual.rightFunctional b.toInnerProductCore x) ∘ₗ
          ξ (radicalElement (-c) : mirabolic (m + 1) F.Carrier)
        have := finite_orbit_twistedRestriction hs hθ H hH x
        have hmem : x' ∈ LinearMap.ker ℓ := by
          rw [hx'def, characterAverage_eq_orbitMean]
          refine orbitMean_mem _ x _ fun g => ?_
          obtain ⟨d, hd⟩ : ∃ d, radicalElement d = (g : radical (m + 1) F.Carrier) :=
            ⟨_, radicalElement_coordinates _⟩
          have hdN : d ∈ latticeBox T (m + 1) N := by
            have hg : (g : radical (m + 1) F.Carrier) ∈ radicalBox T m N := g.property
            rw [← hd, mem_radicalBox, radicalCoordinates_element] at hg
            exact hg
          rw [LinearMap.mem_ker]
          change b.inner x (ξ (radicalElement (-c) : mirabolic (m + 1) F.Carrier)
            (twistedRestriction ξ _ θ (g : radical (m + 1) F.Carrier) x)) = 0
          rw [twistedRestriction_apply, map_smul, CountableDual.inner_smul_right, ← hd,
            rep_radicalElement_mul, hN, mul_zero]
          intro hmem
          apply hc
          rw [show c = d - (-c + d) from by abel]
          exact sub_mem hdN hmem
        exact hmem
      rw [hA, ← b.conj_inner_symm,
        ← b.invariant (radicalElement (-c) : mirabolic (m + 1) F.Carrier),
        rep_radicalElement_mul, neg_add_cancel, rep_radicalElement_zero, hB, map_zero]
    have hint : I x' x' =
        ((μ.real (latticeBox T (m + 1) N : Set (Fin (m + 1) → F.Carrier)) : ℝ) : ℂ) *
          b.inner x' x' := by
      have hpt : ∀ c : Fin (m + 1) → F.Carrier,
          ψ.complex (-(c (Fin.last m))) *
              b.inner x' (ξ (radicalElement c : mirabolic (m + 1) F.Carrier) x') =
            (latticeBox T (m + 1) N : Set (Fin (m + 1) → F.Carrier)).indicator
              (fun _ => b.inner x' x') c := by
        intro c
        by_cases hc : c ∈ latticeBox T (m + 1) N
        · rw [Set.indicator_of_mem (show c ∈ (latticeBox T (m + 1) N : Set _) from hc),
            hxinv c hc, CountableDual.inner_smul_right, ← mul_assoc,
            ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
        · rw [Set.indicator_of_notMem (show c ∉ (latticeBox T (m + 1) N : Set _) from hc),
            hout c hc, mul_zero]
      rw [hI, integral_congr_ae (Filter.Eventually.of_forall hpt),
        integral_indicator_const _ (isOpen_latticeBox T (m + 1) N).measurableSet,
        Complex.real_smul]
    have hvol : 0 < μ.real (latticeBox T (m + 1) N : Set (Fin (m + 1) → F.Carrier)) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos
        ((isOpen_latticeBox T (m + 1) N).measure_ne_zero μ ⟨0, zero_mem _⟩)
        (isCompact_latticeBox T (m + 1) N).measure_lt_top.ne
    refine ⟨x', ?_, _, hvol, hint⟩
    rw [mk_eq_iff]
    exact sub_characterAverage_mem hs hθ H hH x
  have hpos : ∀ x, 0 ≤ (I x x).re := by
    intro x
    obtain ⟨x', hx, r, hr, hrx⟩ := hself x
    rw [hwd hx hx, hrx, Complex.re_ofReal_mul]
    exact mul_nonneg hr.le (b.re_inner_nonneg x')
  have hdef : ∀ x, I x x = 0 → mk ξ _ θ x = 0 := by
    intro x h0
    obtain ⟨x', hx, r, hr, hrx⟩ := hself x
    rw [hwd hx hx, hrx] at h0
    have h1 : b.inner x' x' = 0 :=
      (mul_eq_zero.mp h0).resolve_left (Complex.ofReal_ne_zero.mpr hr.ne')
    rw [hx, b.definite x' h1, map_zero]
  -- Covariance under the successor action.
  have hdet : ∀ h : mirabolic m F.Carrier,
      ((abv (Matrix.det (h : Langlands.GeneralLinear (m + 1) F.Carrier).val) : ℝ) : ℂ) =
        ((((T.determinantNorm (m + 1)) h.val : ℝ≥0) : ℝ) : ℂ) := by
    intro h
    rw [T.determinantNorm_coe]
    rfl
  have hβ : ∀ (g : mirabolic (m + 1) F.Carrier) (v : V) (w : ConjSpace V),
      β (ξ g v) (ConjSpace.rep ξ g w) = determinantWeight abv g.val (-0) * β v w := by
    intro g v w
    rw [neg_zero, determinantWeight, Complex.cpow_zero, one_mul]
    exact conjPairing_invariant b g v w
  have hlevi : ∀ (h : mirabolic m F.Carrier) x y,
      I (ξ (successor h) x) (ξ (successor h) y) =
        ((((T.determinantNorm (m + 1)) h.val : ℝ≥0) : ℝ) : ℂ) * I x y := by
    intro h x y
    have h1 := transferIntegral_levi μ ψ ξ (ConjSpace.rep ξ) β abv T.normalizedAbsHom habv
      hscale 0 hβ hcont (h : Langlands.GeneralLinear (m + 1) F.Carrier) y (ConjSpace.equiv V x)
    change transferIntegral μ ψ ξ β (ξ (levi (h : Langlands.GeneralLinear (m + 1) F.Carrier)) y)
        (ConjSpace.rep ξ (levi (h : Langlands.GeneralLinear (m + 1) F.Carrier))
          (ConjSpace.equiv V x)) = _ * transferIntegral μ ψ ξ β y (ConjSpace.equiv V x)
    rw [h1]
    simp only [mulVec_last]
    rw [neg_zero, determinantWeight, Complex.cpow_zero, one_mul, hdet h]
    rfl
  refine ⟨descendedCore (mk ξ _ θ) (mk_surjective ξ _ θ) I hadd hsmul hsymm hker hpos hdef,
    fun h x y => ?_⟩
  rw [descendedCore_inner, descendedCore_inner, hlevi]

end Coinvariant

/-! ### Transport to `Φ⁻ X` -/

/-- An inner product pulled back along a linear equivalence. -/
@[instance_reducible]
def coreComap {Q Q' : Type*} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q']
    (B : InnerProductSpace.Core ℂ Q) (e : Q' ≃ₗ[ℂ] Q) : InnerProductSpace.Core ℂ Q' where
  inner a a' := B.inner (e a) (e a')
  conj_inner_symm a a' := B.conj_inner_symm _ _
  re_inner_nonneg a := B.re_inner_nonneg _
  add_left a a' a'' := by
    change B.inner (e (a + a')) (e a'') = B.inner (e a) (e a'') + B.inner (e a') (e a'')
    rw [map_add]
    exact B.add_left _ _ _
  smul_left a a' r := by
    change B.inner (e (r • a)) (e a') = conj r * B.inner (e a) (e a')
    rw [map_smul]
    exact B.smul_left _ _ _
  definite a ha := e.injective ((B.definite _ ha).trans (map_zero e).symm)

section Transport

theorem coreComap_inner {Q Q' : Type*} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q']
    [Module ℂ Q'] (B : InnerProductSpace.Core ℂ Q) (e : Q' ≃ₗ[ℂ] Q) (a a' : Q') :
    (coreComap B e).inner a a' = B.inner (e a) (e a') := rfl

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {m : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- On the radical relations `X(V)` of a smooth representation, the radical coefficients of
an invariant form have compact support. -/
theorem restrictForm_radical_support (ρ : Representation ℂ (mirabolic (m + 1) F.Carrier) V)
    (b : InvariantPositiveForm ρ) :
    letI := T.topology
    IsSmooth ρ → ∀ x y : relations ρ (radical (m + 1) F.Carrier) 1, ∃ N : ℤ,
      ∀ c ∉ latticeBox T (m + 1) N,
        (restrictForm b _ (radicalRelations_stable ρ)).inner y
          (radicalPart ρ (radicalElement c : mirabolic (m + 1) F.Carrier) x) = 0 := by
  let := T.topology
  intro hρ x y
  have hβ : ∀ (g : mirabolic (m + 1) F.Carrier) (v : V) (w : ConjSpace V),
      conjPairing b.toInnerProductCore (ρ g v) (ConjSpace.rep ρ g w) =
        determinantWeight (normalizedAbsoluteValue T) g.val (-0) *
          conjPairing b.toInnerProductCore v w := by
    intro g v w
    rw [neg_zero, determinantWeight, Complex.cpow_zero, one_mul]
    exact conjPairing_invariant b g v w
  obtain ⟨N, hN⟩ := exists_coefficient_support_of_mem T ρ (ConjSpace.rep ρ)
    (conjPairing b.toInnerProductCore) 0 hβ hρ (isSmooth_conjRep hρ) x x.property
    (ConjSpace.equiv V (y : V))
  exact ⟨N, fun c hc => hN c hc⟩

/-- The isomorphism `Φ⁻ X(V) ≅ Φ⁻ X` induced by the inclusion of the radical relations. -/
def radicalPartEquiv (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (ρ : Representation ℂ (mirabolic (m + 1) F.Carrier) V) (hρ : letI := T.topology; IsSmooth ρ) :
    Coinvariants (radicalPart ρ) (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m) ≃ₗ[ℂ]
      Coinvariants ρ (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m) :=
  LinearEquiv.ofBijective (radicalPartMap T ψ ρ)
    (⟨radicalPartMap_injective T ψ ρ hρ, radicalPartMap_surjective T ψ ρ⟩ :
      Function.Bijective (radicalPartMap T ψ ρ))

theorem radicalPartEquiv_symm_mk (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (ρ : Representation ℂ (mirabolic (m + 1) F.Carrier) V) (hρ : letI := T.topology; IsSmooth ρ)
    (v : V) (x₀ : relations ρ (radical (m + 1) F.Carrier) 1)
    (hx : mk ρ _ (T.mirabolicTheta ψ m) (x₀ : V) = mk ρ _ (T.mirabolicTheta ψ m) v) :
    (radicalPartEquiv T ψ ρ hρ).symm (mk ρ _ (T.mirabolicTheta ψ m) v) =
      mk (radicalPart ρ) _ (T.mirabolicTheta ψ m) x₀ := by
  rw [LinearEquiv.symm_apply_eq]
  exact hx.symm.trans (radicalPartMap_mk T ψ ρ x₀).symm

theorem radicalPartEquiv_symm_mk_successor (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (ρ : Representation ℂ (mirabolic (m + 1) F.Carrier) V) (hρ : letI := T.topology; IsSmooth ρ)
    (h : mirabolic m F.Carrier) (v : V) (x₀ : relations ρ (radical (m + 1) F.Carrier) 1)
    (hx : mk ρ _ (T.mirabolicTheta ψ m) (x₀ : V) = mk ρ _ (T.mirabolicTheta ψ m) v) :
    (radicalPartEquiv T ψ ρ hρ).symm (mk ρ _ (T.mirabolicTheta ψ m) (ρ (successor h) v)) =
      mk (radicalPart ρ) _ (T.mirabolicTheta ψ m) (radicalPart ρ (successor h) x₀) := by
  let := T.topology
  apply radicalPartEquiv_symm_mk
  rw [mk_eq_iff, radicalPart_apply, ← map_sub]
  exact relations_stable ρ _ _ (successorSubgroup m F.Carrier)
    successorSubgroup_le_normalizer (theta_isInvariant ψ m) ⟨successor h, h, rfl⟩
    ((mk_eq_iff ρ _ _ _ _).mp hx)

/-- A smooth representation of `P_(m+2)` with an invariant positive form has an inner product
on its `θ_ψ`-coinvariants with covariance `|det|` under the successor action. -/
theorem exists_phiMinusCore (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (ρ : Representation ℂ (mirabolic (m + 1) F.Carrier) V) (b : InvariantPositiveForm ρ) :
    letI := T.topology
    IsSmooth ρ →
      ∃ B : InnerProductSpace.Core ℂ
          (Coinvariants ρ (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m)),
        ∀ (h : mirabolic m F.Carrier) (v w : V),
          B.inner (mk ρ _ (T.mirabolicTheta ψ m) (ρ (successor h) v))
              (mk ρ _ (T.mirabolicTheta ψ m) (ρ (successor h) w)) =
            ((((T.determinantNorm (m + 1)) h.val : ℝ≥0) : ℝ) : ℂ) *
              B.inner (mk ρ _ (T.mirabolicTheta ψ m) v) (mk ρ _ (T.mirabolicTheta ψ m) w) := by
  let := T.topology
  intro hρ
  have hξ : IsSmooth (radicalPart ρ) :=
    isSmooth_subrepresentation ρ _ (radicalRelations_stable ρ) hρ
  obtain ⟨B, hB⟩ := exists_coinvariantCore T ψ (radicalPart ρ)
    (restrictForm b _ (radicalRelations_stable ρ)) hξ (restrictForm_radical_support T ρ b hρ)
  refine ⟨coreComap B (radicalPartEquiv T ψ ρ hρ).symm, fun h v w => ?_⟩
  obtain ⟨x₀, hx₀⟩ := exists_mk_radicalRelations_eq T ψ ρ v
  obtain ⟨y₀, hy₀⟩ := exists_mk_radicalRelations_eq T ψ ρ w
  rw [coreComap_inner, coreComap_inner]
  -- Explicit congruences: `rw` here is very slow.
  exact (congrArg₂ (fun a a' => B.inner a a')
      (radicalPartEquiv_symm_mk_successor T ψ ρ hρ h v x₀ hx₀)
      (radicalPartEquiv_symm_mk_successor T ψ ρ hρ h w y₀ hy₀)).trans
    ((hB h x₀ y₀).trans (congrArg (fun z => _ * z) (congrArg₂ (fun a a' => B.inner a a')
      (radicalPartEquiv_symm_mk T ψ ρ hρ v x₀ hx₀)
      (radicalPartEquiv_symm_mk T ψ ρ hρ w y₀ hy₀)).symm))

end Transport

/-- Bernstein 1984, §9.3(ii): normalized `Φ⁻` preserves unitarizability. -/
theorem mirabolicPhiMinusUnitarity {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : MirabolicPhiMinusUnitarity.{uF, uV} F T := by
  let := T.topology
  intro ψ m X hX
  obtain ⟨b⟩ := hX
  obtain ⟨B, hB⟩ := exists_phiMinusCore T ψ X.representation b X.isSmooth
  refine ⟨{ toInnerProductCore := B, invariant := fun h a a' => ?_ }⟩
  obtain ⟨v, rfl⟩ := phiMinusQuotient_surjective T ψ m X a
  obtain ⟨w, rfl⟩ := phiMinusQuotient_surjective T ψ m X a'
  rw [phiMinus_action, phiMinus_action]
  change B.inner ((phiMinusCharacter T m h : ℂ) • _) ((phiMinusCharacter T m h : ℂ) • _) = _
  rw [B.smul_left, CountableDual.inner_smul_right, hB, ← mul_assoc, ← mul_assoc,
    phiMinusCharacter_conj_mul_mul T h, one_mul]

end Langlands.Derivative.Mirabolic
