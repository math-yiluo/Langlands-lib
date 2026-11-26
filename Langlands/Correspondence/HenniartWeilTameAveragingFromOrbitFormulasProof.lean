import Langlands.GroupTheory.TwistedBurnsideProof
import Langlands.Correspondence.HenniartTameOrbitFormula
import Langlands.Weil.Local.DegreeFrobenius

/-!
# The fixed-cutoff tame average from the orbit formulas

A proof of `WeilTameAveragingFromOrbitFormulasStatement`: the Frobenius coset parametrization,
the orbit formula over the base field and the fixed-point formula over the tame fields give
`WeilTameAveragingStatement`. This is the averaging over the Frobenius cosets in Koch (1984), §8.

The counting step is a twisted form of Burnside's lemma (`nonempty_twistedFixed_equiv`), applied
to the action of the finite quotient of inertia by the common kernel on the tame wild classes
(`sum_encard_cosetFixed`).
-/

noncomputable section

namespace Langlands.Henniart

open MulAction

universe uK uW

/-! ## A twisted form of Burnside's lemma -/

section TwistedBurnside

variable {G Y : Type*} [Group G] [MulAction G Y]

/-- For a map `σ` carrying orbits into orbits, the points `y` such that some group element
carries `σ y` back to `y`, as a sub-`G`-set. -/
def twistedStablePoints (σ : Y → Y) (hσ : ∀ (g : G) (y : Y), ∃ g' : G, σ (g • y) = g' • σ y) :
    SubMulAction G Y where
  carrier := {y | ∃ g : G, g • σ y = y}
  smul_mem' g y := by
    rintro ⟨u, hu⟩
    obtain ⟨g', hg'⟩ := hσ g y
    refine ⟨g * u * g'⁻¹, ?_⟩
    rw [hg', smul_smul, inv_mul_cancel_right, mul_smul, hu]

/-- Twisted Burnside bijection: the pairs `(g, y)` with `g • σ y = y` correspond to the pairs
consisting of an orbit of twisted-stable points and a group element. -/
theorem nonempty_twistedFixed_equiv (σ : Y → Y)
    (hσ : ∀ (g : G) (y : Y), ∃ g' : G, σ (g • y) = g' • σ y) :
    Nonempty ({p : G × Y // p.1 • σ p.2 = p.2} ≃
      orbitRel.Quotient G (twistedStablePoints σ hσ) × G) := by
  classical
  let S := twistedStablePoints σ hσ
  have mem : ∀ (g : G) (y : Y), g • σ y = y → y ∈ S := fun g y h => ⟨g, h⟩
  let u : S → G := fun y => Classical.choose y.2
  have hu : ∀ y : S, u y • σ y = y := fun y => Classical.choose_spec y.2
  have hu' : ∀ y : S, (u y)⁻¹ • (y : Y) = σ y := fun y => by
    rw [inv_smul_eq_iff, hu]
  let e : {p : G × Y // p.1 • σ p.2 = p.2} ≃ {q : G × S // q.1 • q.2 = q.2} :=
    { toFun := fun p => ⟨(p.1.1 * (u ⟨p.1.2, mem _ _ p.2⟩)⁻¹, ⟨p.1.2, mem _ _ p.2⟩), by
        apply Subtype.ext
        change (p.1.1 * (u ⟨p.1.2, mem _ _ p.2⟩)⁻¹) • p.1.2 = p.1.2
        rw [mul_smul, hu' ⟨p.1.2, mem _ _ p.2⟩]
        exact p.2⟩
      invFun := fun q => ⟨(q.1.1 * u q.1.2, (q.1.2 : Y)), by
        change (q.1.1 * u q.1.2) • σ q.1.2 = q.1.2
        rw [mul_smul, hu]
        exact congrArg Subtype.val q.2⟩
      left_inv := fun p => by
        apply Subtype.ext
        exact Prod.ext (inv_mul_cancel_right _ _) rfl
      right_inv := fun q => by
        apply Subtype.ext
        exact Prod.ext (mul_inv_cancel_right _ _) rfl }
  exact ⟨e.trans ((Equiv.subtypeProdEquivSigmaSubtype fun (g : G) (y : S) => g • y = y).trans
    (MulAction.sigmaFixedByEquivOrbitsProdGroup G S))⟩

/-- Twisted Burnside count in `ℕ∞`. -/
theorem enatCard_twistedFixed (σ : Y → Y)
    (hσ : ∀ (g : G) (y : Y), ∃ g' : G, σ (g • y) = g' • σ y) :
    ENat.card {p : G × Y // p.1 • σ p.2 = p.2} =
      ENat.card (orbitRel.Quotient G (twistedStablePoints σ hσ)) * ENat.card G := by
  obtain ⟨e⟩ := nonempty_twistedFixed_equiv σ hσ
  rw [ENat.card_congr e, ENat.card_prod]

end TwistedBurnside

/-! ## Averaging over the cosets of a normal subgroup of finite index -/

section Cosets

variable {W X : Type*} [Group W] [MulAction W X]

/-- A `W`-stable subset, as a sub-`W`-set. -/
def stableSubMulAction (T : Set X) (hT : ∀ (w : W) (c : X), c ∈ T → w • c ∈ T) :
    SubMulAction W X where
  carrier := T
  smul_mem' w c hc := hT w c hc

variable (I J : Subgroup W) (T : Set X) (hT : ∀ (w : W) (c : X), c ∈ T → w • c ∈ T)
  (hJ : ∀ c ∈ T, ∀ g ∈ J, g • c = c)

include hJ in
/-- `J ∩ I` acts trivially on `T`. -/
theorem subgroupOf_le_ker_toPermHom :
    J.subgroupOf I ≤ (MulAction.toPermHom I (stableSubMulAction T hT)).ker := by
  intro h hh
  rw [MonoidHom.mem_ker]
  apply Equiv.ext
  intro y
  apply Subtype.ext
  exact hJ y.1 y.2 (h : W) hh

/-- The action of the quotient `I ⧸ (J ∩ I)` on `T`, through the action of `I`. -/
abbrev cosetMulAction [J.Normal] :
    MulAction (I ⧸ J.subgroupOf I) (stableSubMulAction T hT) :=
  MulAction.compHom _
    (QuotientGroup.lift (J.subgroupOf I) (MulAction.toPermHom I (stableSubMulAction T hT))
      (subgroupOf_le_ker_toPermHom I J T hT hJ))

include hT hJ in
/-- Averaging over the cosets of `J ∩ I` in `I`: if `I` and `J` are normal, `T` is `W`-stable
and fixed pointwise by `J`, and the `g i` represent each coset of `J ∩ I` in `I` once, then the
sum over `i` of the number of points of `T` fixed by `g i * φ` is the number of cosets times the
number of `I`-orbits that meet `T` and are mapped to themselves by `φ`. -/
theorem sum_encard_cosetFixed [I.Normal] [J.Normal] (φ : W) {ι : Type*} [Fintype ι]
    (g : ι → I)
    (hg : Function.Bijective fun i => (QuotientGroup.mk (g i) : I ⧸ J.subgroupOf I)) :
    ∑ i, {c ∈ T | ((g i : W) * φ) • c = c}.encard =
      (Fintype.card ι : ℕ∞) * {o : orbitRel.Quotient I X | ∃ c ∈ T,
        (Quotient.mk'' c : orbitRel.Quotient I X) = o ∧
          (Quotient.mk'' (φ • c) : orbitRel.Quotient I X) = o}.encard := by
  classical
  let S := stableSubMulAction T hT
  let Q := I ⧸ J.subgroupOf I
  let : MulAction Q S := cosetMulAction I J T hT hJ
  have hmk : ∀ (h : I) (y : S), (((h : Q) • y : S) : X) = (h : W) • (y : X) := fun h y => rfl
  let σ : S → S := fun y => φ • y
  have hσ : ∀ (x : Q) (y : S), ∃ x' : Q, σ (x • y) = x' • σ y := by
    intro x y
    induction x using QuotientGroup.induction_on with
    | H h =>
      refine ⟨((⟨φ * (h : W) * φ⁻¹, (inferInstance : I.Normal).conj_mem _ h.2 φ⟩ : I) : Q), ?_⟩
      apply Subtype.ext
      change φ • (((h : Q) • y : S) : X) = (φ * (h : W) * φ⁻¹) • φ • (y : X)
      rw [hmk, smul_smul, smul_smul, inv_mul_cancel_right]
  have hcond : ∀ (h : I) (y : S), ((h : Q) • σ y = y) ↔ (((h : W) * φ) • (y : X) = y) := by
    intro h y
    rw [Subtype.ext_iff, hmk, ← smul_smul]
    rfl
  have key := enatCard_twistedFixed σ hσ
  -- the left side
  have hLHS : ENat.card {p : Q × S // p.1 • σ p.2 = p.2} =
      ∑ i, {c ∈ T | ((g i : W) * φ) • c = c}.encard := by
    rw [ENat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun (x : Q) (y : S) => x • σ y = y),
      ← ENat.card_congr ((Equiv.ofBijective _ hg).sigmaCongrLeft
        (β := fun x : Q => {y : S // x • σ y = y})),
      Langlands.enatCardSigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact ENat.card_congr
      { toFun := fun y => ⟨(y.1 : X), y.1.2, (hcond (g i) y.1).1 y.2⟩
        invFun := fun c => ⟨⟨c.1, c.2.1⟩, (hcond (g i) ⟨c.1, c.2.1⟩).2 c.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  -- the number of cosets
  have hQ : ENat.card Q = Fintype.card ι := by
    rw [← ENat.card_congr (Equiv.ofBijective _ hg), ENat.card_eq_coe_fintype_card]
  -- the orbits
  let P := twistedStablePoints σ hσ
  let F : orbitRel.Quotient Q P → orbitRel.Quotient I X :=
    Quotient.map' (fun y : P => ((y : S) : X)) (by
      intro a b hab
      rw [orbitRel_apply, mem_orbit_iff] at hab ⊢
      obtain ⟨x, hx⟩ := hab
      induction x using QuotientGroup.induction_on with
      | H h =>
        refine ⟨h, ?_⟩
        have := congrArg (fun z : P => ((z : S) : X)) hx
        exact this)
  have hF : Function.Injective F := by
    intro a b hab
    induction a using Quotient.inductionOn' with
    | h a =>
    induction b using Quotient.inductionOn' with
    | h b =>
      have hab' : orbitRel I X ((a : S) : X) ((b : S) : X) := Quotient.exact' hab
      rw [orbitRel_apply, mem_orbit_iff] at hab'
      obtain ⟨h, hh⟩ := hab'
      apply Quotient.sound'
      rw [orbitRel_apply, mem_orbit_iff]
      refine ⟨(h : Q), ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hh
  have hrange : Set.range F = {o : orbitRel.Quotient I X | ∃ c ∈ T,
      (Quotient.mk'' c : orbitRel.Quotient I X) = o ∧
        (Quotient.mk'' (φ • c) : orbitRel.Quotient I X) = o} := by
    ext o
    constructor
    · rintro ⟨a, rfl⟩
      induction a using Quotient.inductionOn' with
      | h a =>
        obtain ⟨x, hx⟩ := a.2
        induction x using QuotientGroup.induction_on with
        | H h =>
          refine ⟨((a : S) : X), (a : S).2, rfl, ?_⟩
          change (Quotient.mk'' (φ • ((a : S) : X)) : orbitRel.Quotient I X) =
            Quotient.mk'' ((a : S) : X)
          apply Quotient.sound'
          rw [orbitRel_apply, mem_orbit_iff]
          refine ⟨h⁻¹, ?_⟩
          have hx' := (hcond h (a : S)).1 hx
          rw [Subgroup.smul_def, Subgroup.coe_inv, inv_smul_eq_iff, smul_smul, hx']
    · rintro ⟨c, hc, rfl, hφc⟩
      have hrel : orbitRel I X (φ • c) c := Quotient.exact' hφc
      rw [orbitRel_apply, mem_orbit_iff] at hrel
      obtain ⟨h, hh⟩ := hrel
      have hmemP : (⟨c, hc⟩ : S) ∈ P := by
        refine ⟨((h⁻¹ : I) : Q), ?_⟩
        rw [hcond]
        change (((h⁻¹ : I) : W) * φ) • c = c
        rw [← smul_smul, ← hh, Subgroup.smul_def, smul_smul, Subgroup.coe_inv, inv_mul_cancel,
          one_smul]
      exact ⟨Quotient.mk'' ⟨⟨c, hc⟩, hmemP⟩, rfl⟩
  have hRHS : ENat.card (orbitRel.Quotient Q P) = {o : orbitRel.Quotient I X | ∃ c ∈ T,
      (Quotient.mk'' c : orbitRel.Quotient I X) = o ∧
        (Quotient.mk'' (φ • c) : orbitRel.Quotient I X) = o}.encard := by
    rw [← hrange, ENat.card_congr (Equiv.ofInjective F hF)]
    rfl
  rw [← hLHS, key, hRHS, hQ, mul_comm]

end Cosets

/-! ## Stability of the tame classes under the Weil group -/

section Stability

open Weil.Local FiniteRepresentation

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- Triviality on an upper ramification group is preserved by conjugation by the Weil group,
because the upper ramification groups are normal. -/
theorem wildClassTrivialAt_smul (v : ℝ) (w : localWeilGroup K) (c : WildClasses.{uK, uW} K)
    (hc : wildClassTrivialAt K v c) : wildClassTrivialAt K v (w • c) := by
  revert hc
  refine Quotient.inductionOn c fun A hA => ?_
  change WildTrivialAt K v (conjugateOpenKernelIrreducible (weilWildInertia K) w A).1
  change WildTrivialAt K v A.1 at hA
  intro x hx
  have hN : (VirtualRepresentation.LocalWeil.Ramification.upperGroup K v).Normal :=
    Subgroup.Normal.comap inferInstance _
  have hmem : ((MulAut.conjNormal (H := weilWildInertia K) w⁻¹ x : weilWildInertia K) :
      localWeilGroup K) ∈ VirtualRepresentation.LocalWeil.Ramification.upperGroup K v := by
    rw [MulAut.conjNormal_apply]
    exact hN.conj_mem _ hx w⁻¹
  exact hA _ hmem

/-- The classes of `tameOrbitClasses` form a subset stable under the Weil group when the
subgroup `J` is normal. -/
theorem smul_mem_tameOrbitClasses (J : Subgroup (localWeilGroup K)) [J.Normal] (r m j : ℕ)
    (w : localWeilGroup K) (c : WildClasses.{uK, uW} K)
    (hc : c ∈ tameOrbitClasses.{uK, uW} K J r m j) :
    w • c ∈ tameOrbitClasses.{uK, uW} K J r m j := by
  obtain ⟨hfix, hrank, htriv⟩ := hc
  refine ⟨fun g hg => ?_, ?_, fun v hv => wildClassTrivialAt_smul K v w c (htriv v hv)⟩
  · have hconj : w⁻¹ * g * w ∈ J := by
      simpa only [inv_inv] using (inferInstance : J.Normal).conj_mem g hg w⁻¹
    calc g • w • c = (w * (w⁻¹ * g * w)) • c := by rw [smul_smul]; group
      _ = w • (w⁻¹ * g * w) • c := mul_smul _ _ _
      _ = w • c := by rw [hfix _ hconj]
  · rw [openKernelIrreducibleRank_smul]
    exact hrank

end Stability

/-! ## The fixed-cutoff average from the orbit formulas -/

/-- The Frobenius coset parametrization, the orbit formula over the base field and the
fixed-point formula over the tame fields together give the fixed-cutoff average. -/
theorem weilTameAveragingFromOrbitFormulas :
    WeilTameAveragingFromOrbitFormulasStatement.{uK, uW} := by
  intro hparam horbit hfix p _ K r m j hm
  let φ := Weil.Local.localGeometricFrobenius K
  have hφ : Weil.Local.localDegreeInt K φ = 1 :=
    Weil.Local.localDegreeInt_localGeometricFrobenius K
  obtain ⟨D⟩ := hparam p K m hm φ hφ
  let J := D.kernel
  let I := Weil.Local.localInertia K
  let T := tameOrbitClasses.{uK, uW} K J.toSubgroup r m j
  let g : Fin m → I := fun i => (D.cosetEquiv i).out
  have hgmk : ∀ i, (QuotientGroup.mk (g i) : tameInertiaCosets K J) = D.cosetEquiv i :=
    fun i => QuotientGroup.out_eq' _
  have hg : Function.Bijective fun i =>
      (QuotientGroup.mk (g i) : I ⧸ J.toSubgroup.subgroupOf I) := by
    have : (fun i => (QuotientGroup.mk (g i) : tameInertiaCosets K J)) = D.cosetEquiv :=
      funext hgmk
    exact this ▸ D.cosetEquiv.bijective
  refine ⟨D.cosetEquiv.trans D.fieldEquiv, ?_⟩
  have hindex : (J.toSubgroup.subgroupOf I).index = m := by
    rw [Subgroup.index, ← Nat.card_congr D.cosetEquiv, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have horb := horbit p K r m j hm J D.kernel_le_inertia hindex φ hφ
  have hsum : (∑ i : Fin m, Numerical.weilConductorCount.{uK, uW}
      (((D.cosetEquiv.trans D.fieldEquiv) i).1.asPadicField (p := p)) (p ^ r - 1) j) =
      ∑ i : Fin m, ((K.canonicalTopologicalData.residueCardinality - 1 : ℕ) : ℕ∞) *
        {c ∈ T | ((g i : Weil.Local.localWeilGroup K) * φ) • c = c}.encard := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := hfix p K r m j hm φ hφ D (g i)
    rw [hgmk i] at h
    exact h
  have hT : ∀ (w : Weil.Local.localWeilGroup K) (c : WildClasses.{uK, uW} K),
      c ∈ T → w • c ∈ T := fun w c hc => smul_mem_tameOrbitClasses K J.toSubgroup r m j w c hc
  have hJ : ∀ c ∈ T, ∀ x ∈ J.toSubgroup, x • c = c := fun c hc x hx => hc.1 x hx
  have hcount := sum_encard_cosetFixed I J.toSubgroup T hT hJ φ g hg
  rw [hsum, ← Finset.mul_sum, hcount, horb, Fintype.card_fin]
  change _ = (m : ℕ∞) * (_ * {o | ∃ c ∈ T, _ ∧ _}.encard)
  ring

end Langlands.Henniart
