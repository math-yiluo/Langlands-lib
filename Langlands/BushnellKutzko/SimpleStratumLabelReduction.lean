import Langlands.BushnellKutzko.SimpleStratumLabelStep
import Langlands.BushnellKutzko.SimpleStratumLabelStatement
import Langlands.BushnellKutzko.PureStratumSimpleApproximationStatement

/-! # Labels of simple strata by induction on the level -/

noncomputable section

open ValuativeRel Polynomial Langlands.Henniart.Numerical Langlands.FieldTheory

namespace Langlands.BushnellKutzko.SimpleStratumLabel

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

/-- The simple strata `[𝔄,n,m,β]` on a fixed chain with fixed integers. -/
abbrev LabelStrata (L : LatticeChain 𝒪[F] F V) (n m : ℤ) :=
  {S : Stratum 𝒪[F] F V // S.chain = L ∧ S.n = n ∧ S.r = m ∧ S.IsSimple}

/-- The label set `P^m_n(e(𝔄), N/e(𝔄); q_F)` of a principal chain. -/
abbrev LabelValues (L : LatticeChain 𝒪[F] F V) (n m : ℤ) :=
  ↥(labelSet m.toNat n.toNat L.period (Module.finrank F V / L.period) (Nat.card 𝓀[F]))

/-- The two properties of the label map in `SimpleStratumLabelStatement`. -/
def IsStratumLabelling (L : LatticeChain 𝒪[F] F V) (n m : ℤ)
    (ρ : LabelStrata L n m → LabelValues L n m) : Prop :=
  (∀ S T : LabelStrata L n m, ρ S = ρ T →
    ∃ u ∈ L.unitFiltration 0,
      (↑(u⁻¹) : Module.End F V) * S.1.b * (u : Module.End F V) ∈ T.1.coset) ∧
  (∀ S : LabelStrata L n m,
    (ρ S).1.d = elementResidueDegree F S.1.b ∧
    elementRamificationIndex F S.1.b * (ρ S).1.e = L.period)

theorem isPrimePow_natCard_residueField : IsPrimePow (Nat.card 𝓀[F]) := by
  let := Fintype.ofFinite 𝓀[F]
  rw [← Fintype.card_eq_nat_card]
  exact FiniteField.isPrimePow_card _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem Label.single_injective {q : ℕ} {x y : LabelEntry q} (h : Label.single x = Label.single y) :
    x = y := by
  simp only [Label.single, Label.mk.injEq, heq_eq_eq, true_and] at h
  exact congrFun h 0

set_option maxHeartbeats 1000000 in
/-- BK94 (1.14), the case `m = n − 1`, from (1.4)–(1.5). -/
theorem exists_isStratumLabelling_base [FiniteDimensional F V]
    (hPoly : MinimalSimpleStratumPolynomialStatement.{uF, uV})
    (L : LatticeChain 𝒪[F] F V) (hP : L.IsPrincipal) (n : ℤ) (hn : 1 ≤ n) :
    ∃ ρ, IsStratumLabelling L n (n - 1) ρ := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  let π : RingPrimeElement 𝒪[F] := ⟨ϖ, hϖ.ne_zero, by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal, hϖ.maximalIdeal_eq]⟩
  set q := Nat.card 𝓀[F] with hqdef
  have hq : IsPrimePow q := isPrimePow_natCard_residueField
  let : Field (𝒪[F] ⧸ Ring.jacobson 𝒪[F]) := jacobsonResidueField F
  have : Finite (𝒪[F] ⧸ Ring.jacobson 𝒪[F]) := finite_jacobsonResidue F
  let D1 : ℕ+ := 1
  obtain ⟨ι⟩ := nonempty_ringEquiv_labelField hq D1 (𝒪[F] ⧸ Ring.jacobson 𝒪[F])
    (by rw [natCard_jacobsonResidue]; exact (pow_one q).symm)
  have hP1 : ∀ S : LabelStrata L n (n - 1),
      ∃ (f : Polynomial (𝒪[F] ⧸ Ring.jacobson 𝒪[F])) (a : ℕ),
        f.Monic ∧ Irreducible f ∧ f ≠ Polynomial.X ∧ 0 < a ∧
        S.1.fundamentalPolynomial π = f ^ a ∧
        f.natDegree ∣ Module.finrank F V / L.period ∧
        elementResidueDegree F S.1.b = f.natDegree ∧
        elementRamificationIndex F S.1.b = L.period / Nat.gcd L.period n.natAbs :=
    (hPoly F V L n π hP hn).1
  have hP2 : ∀ (S T : LabelStrata L n (n - 1)) (f : Polynomial (𝒪[F] ⧸ Ring.jacobson 𝒪[F]))
      (a b : ℕ), f.Monic → Irreducible f → 0 < a → 0 < b →
      S.1.fundamentalPolynomial π = f ^ a → T.1.fundamentalPolynomial π = f ^ b →
      ∃ u ∈ L.unitFiltration 0,
        (↑(u⁻¹) : Module.End F V) * S.1.b * (u : Module.End F V) ∈ T.1.coset :=
    (hPoly F V L n π hP hn).2
  let polyOf : LabelStrata L n (n - 1) → Polynomial (𝒪[F] ⧸ Ring.jacobson 𝒪[F]) :=
    fun S => Classical.choose (hP1 S)
  have hpolyOf : ∀ S, ∃ a : ℕ,
      (polyOf S).Monic ∧ Irreducible (polyOf S) ∧ polyOf S ≠ Polynomial.X ∧ 0 < a ∧
        S.1.fundamentalPolynomial π = polyOf S ^ a ∧
        (polyOf S).natDegree ∣ Module.finrank F V / L.period ∧
        elementResidueDegree F S.1.b = (polyOf S).natDegree ∧
        elementRamificationIndex F S.1.b = L.period / Nat.gcd L.period n.natAbs :=
    fun S => Classical.choose_spec (hP1 S)
  let entryOf : LabelStrata L n (n - 1) → LabelEntry q := fun S =>
    { polynomial := ⟨D1, (polyOf S).map
        (ι : (𝒪[F] ⧸ Ring.jacobson 𝒪[F]) →+* polarExtensionField (labelFieldSize q) D1)⟩
      level := n.toNat
      degree := (polyOf S).natDegree
      ramification := Nat.gcd n.toNat L.period }
  have := L.finiteDimensional
  have hbpos : 0 < Module.finrank F V / L.period :=
    Nat.div_pos (PureApproximation.period_le_finrank L) L.period_pos
  have hmem : ∀ S, Label.single (entryOf S) ∈
      labelSet (n - 1).toNat n.toNat L.period (Module.finrank F V / L.period) q := by
    intro S
    obtain ⟨a, hm, hi, hX, -, -, hdvd, -, -⟩ := hpolyOf S
    exact single_mem_labelSet hq (by omega) L.period_pos hbpos rfl
      (Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hi))
      hdvd rfl rfl (map_mem_irreduciblePolynomialLabels ι hm hi hX)
  refine ⟨fun S => ⟨Label.single (entryOf S), hmem S⟩, ?_, ?_⟩
  · intro S T h
    have hx : entryOf S = entryOf T := Label.single_injective (congrArg Subtype.val h)
    have hmap : (polyOf S).map
          (ι : (𝒪[F] ⧸ Ring.jacobson 𝒪[F]) →+* polarExtensionField (labelFieldSize q) D1) =
        (polyOf T).map
          (ι : (𝒪[F] ⧸ Ring.jacobson 𝒪[F]) →+* polarExtensionField (labelFieldSize q) D1) := by
      have h1 := congrArg (fun y : LabelEntry q => y.polynomial) hx
      simp only [entryOf, FieldPolynomial.mk.injEq, heq_eq_eq, true_and] at h1
      exact h1
    have hpoly : polyOf S = polyOf T := Polynomial.map_injective _ ι.injective hmap
    obtain ⟨a, hm, hi, -, ha, hfS, -⟩ := hpolyOf S
    obtain ⟨b, -, -, -, hb, hfT, -⟩ := hpolyOf T
    rw [← hpoly] at hfT
    exact hP2 S T (polyOf S) a b hm hi ha hb hfS hfT
  · intro S
    obtain ⟨a, -, -, -, -, -, -, hres, hram⟩ := hpolyOf S
    refine ⟨?_, ?_⟩
    · change (Label.single (entryOf S)).d = _
      rw [Label.single_d, hres]
    · change elementRamificationIndex F S.1.b * (Label.single (entryOf S)).e = L.period
      rw [Label.single_e, hram]
      change L.period / Nat.gcd L.period n.natAbs * Nat.gcd n.toNat L.period = L.period
      rw [show n.natAbs = n.toNat by omega, Nat.gcd_comm n.toNat]
      exact Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)

set_option maxHeartbeats 4000000 in
/-- BK94 (1.14), the restriction step from level `m + 1` to level `m < n − 1`: each simple
stratum is conjugated into the fibre of a fixed representative of its restricted class, and its
label is that of the representative, extended by the quadruple of its derived stratum when that
stratum is not null. -/
theorem exists_isStratumLabelling_step [FiniteDimensional F V]
    (hPi : PureStratumSimpleApproximationStatement.{uF, uV})
    (hPolyE : MinimalSimpleStratumPolynomialStatement.{uV, uV})
    (L : LatticeChain 𝒪[F] F V) (hP : L.IsPrincipal) (n m : ℤ) (hm : 0 ≤ m) (hmn : m + 1 < n)
    (ρ' : LabelStrata L n (m + 1) → LabelValues L n (m + 1))
    (hρ' : IsStratumLabelling L n (m + 1) ρ') :
    ∃ ρ, IsStratumLabelling L n m ρ := by
  classical
  set q := Nat.card 𝓀[F] with hqdef
  have hm1 : (m + 1).toNat = m.toNat + 1 := by omega
  -- The fibre labellers.
  have hlab : ∀ T : LabelStrata L n (m + 1), ∃ lab, IsFibreLabeller T.1 lab := fun T =>
    exists_isFibreLabeller hPolyE T.1 T.2.2.2.2 (by rw [T.2.1]; exact hP)
      (by rw [T.2.2.2.1]; omega)
  let labOf : LabelStrata L n (m + 1) → Module.End F V → Option (LabelEntry q) :=
    fun T => Classical.choose (hlab T)
  have hlabOf : ∀ T, IsFibreLabeller T.1 (labOf T) := fun T => Classical.choose_spec (hlab T)
  -- A simple approximation one level up.
  have happrox : ∀ S : LabelStrata L n m, ∃ T : LabelStrata L n (m + 1),
      S.1.b - T.1.b ∈ L.endFiltration (-(m + 1)) := by
    intro S
    obtain ⟨⟨Sc, Sn, Sr, Sb, hlt, hv⟩, hc, hn, hr, hs⟩ := S
    change Sc = L at hc
    change Sn = n at hn
    subst hc hn
    let S' : Stratum 𝒪[F] F V := ⟨Sc, Sn, m + 1, Sb, hmn, hv⟩
    have hS' : S'.IsPure := hs.1
    obtain ⟨T, hTc, hTn, hTr, hT, hST, -, -⟩ := hPi F V S' hS'
    exact ⟨⟨T, hTc, hTn, hTr, hT⟩, Stratum.sub_mem_of_equivalent hST⟩
  let T₀ : LabelStrata L n m → LabelStrata L n (m + 1) := fun S => Classical.choose (happrox S)
  have hT₀ : ∀ S, S.1.b - (T₀ S).1.b ∈ L.endFiltration (-(m + 1)) :=
    fun S => Classical.choose_spec (happrox S)
  -- One representative for each label one level up.
  let rep : ∀ p : LabelValues L n (m + 1), (∃ T, ρ' T = p) → LabelStrata L n (m + 1) :=
    fun _ h => Classical.choose h
  have hrep : ∀ p h, ρ' (rep p h) = p := fun _ h => Classical.choose_spec h
  have hrep_congr : ∀ (p₁ p₂ : LabelValues L n (m + 1)) (h₁ : ∃ T, ρ' T = p₁)
      (h₂ : ∃ T, ρ' T = p₂), p₁ = p₂ → rep p₁ h₁ = rep p₂ h₂ := by
    rintro p _ h₁ h₂ rfl
    rfl
  let G : LabelStrata L n m → LabelStrata L n (m + 1) := fun S => rep (ρ' (T₀ S)) ⟨T₀ S, rfl⟩
  have hGρ : ∀ S, ρ' (G S) = ρ' (T₀ S) := fun S => hrep _ _
  -- The conjugating units.
  have hconjex : ∀ S, ∃ u ∈ L.unitFiltration 0,
      (↑(u⁻¹) : Module.End F V) * (T₀ S).1.b * (u : Module.End F V) ∈ (G S).1.coset :=
    fun S => hρ'.1 (T₀ S) (G S) (hGρ S).symm
  let u : LabelStrata L n m → (Module.End F V)ˣ := fun S => Classical.choose (hconjex S)
  have hu : ∀ S, u S ∈ L.unitFiltration 0 := fun S => (Classical.choose_spec (hconjex S)).1
  have huc : ∀ S, (↑((u S)⁻¹) : Module.End F V) * (T₀ S).1.b * (u S : Module.End F V) ∈
      (G S).1.coset := fun S => (Classical.choose_spec (hconjex S)).2
  have hu0 : ∀ S, ((u S : (Module.End F V)ˣ) : Module.End F V) ∈ S.1.chain.endFiltration 0 :=
    fun S => by rw [S.2.1]; exact (hu S).1
  have hui0 : ∀ S, (((u S)⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈
      S.1.chain.endFiltration 0 := fun S => by rw [S.2.1]; exact (hu S).2.1
  -- The conjugated strata, in the fibres of the representatives.
  let S'' : LabelStrata L n m → Stratum 𝒪[F] F V :=
    fun S => PureApproximation.conjStratum S.1 (u S) (hu0 S) (hui0 S)
  have hS''b : ∀ S, (S'' S).b =
      (↑((u S)⁻¹) : Module.End F V) * S.1.b * (u S : Module.End F V) := fun _ => rfl
  have hfib : ∀ S, InFibre (G S).1 (S'' S) := by
    intro S
    have hGc : (G S).1.chain = L := (G S).2.1
    have hGr : (G S).1.r = m + 1 := (G S).2.2.2.1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change S.1.chain = (G S).1.chain
      rw [S.2.1, hGc]
    · change S.1.n = (G S).1.n
      rw [S.2.2.1, (G S).2.2.1]
    · change S.1.r = (G S).1.r - 1
      rw [S.2.2.2.1, hGr]
      ring
    · exact PureApproximation.isSimple_conjStratum S.1 (u S) (hu0 S) (hui0 S) S.2.2.2.2
    · rw [hS''b, hGc, hGr]
      have h1 : (↑((u S)⁻¹) : Module.End F V) * (S.1.b - (T₀ S).1.b) * (u S : Module.End F V) ∈
          L.endFiltration (-(m + 1)) := by
        have := L.mul_mem_endFiltration (L.mul_mem_endFiltration (hu S).2.1 (hT₀ S)) (hu S).1
        simpa using this
      have h2 := huc S
      change _ - (G S).1.b ∈ (G S).1.chain.endFiltration (-(G S).1.r) at h2
      rw [hGc, hGr] at h2
      have := add_mem h1 h2
      convert this using 1
      noncomm_ring
  let ℓ : LabelStrata L n m → Option (LabelEntry q) :=
    fun S => labOf (G S) ((S'' S).b - (G S).1.b)
  -- Facts about the representatives.
  have hGe : ∀ S, elementRamificationIndex F (G S).1.b * (ρ' (G S)).1.e = L.period :=
    fun S => (hρ'.2 (G S)).2
  have hGd : ∀ S, (ρ' (G S)).1.d = elementResidueDegree F (G S).1.b := fun S => (hρ'.2 (G S)).1
  have hGepos : ∀ S, 0 < elementRamificationIndex F (G S).1.b := by
    intro S
    have h := hGe S
    have hp := L.period_pos
    rw [← h] at hp
    exact Nat.pos_of_mul_pos_right hp
  have hdiv : ∀ S, L.period / elementRamificationIndex F (G S).1.b = (ρ' (G S)).1.e :=
    fun S => Nat.div_eq_of_eq_mul_right (hGepos S) (hGe S).symm
  -- Conjugation leaves the invariants unchanged.
  have hconjinv : ∀ S, elementRamificationIndex F (S'' S).b = elementRamificationIndex F S.1.b ∧
      elementResidueDegree F (S'' S).b = elementResidueDegree F S.1.b := by
    intro S
    obtain ⟨⟨hf, hn⟩, -⟩ := S.2.2.2.2.1
    exact PureApproximation.elementInvariants_conj S.1.chain (hu0 S) (hui0 S) S.1.b
      (normalizingUnits_of_isField S.1.chain hf hn)
  -- The label.
  let lbl : LabelStrata L n m → Label q := fun S =>
    match ℓ S with
    | none => (ρ' (G S)).1
    | some x => (ρ' (G S)).1.snoc x
  have hsucc : ∀ x : Label q,
      x ∈ labelSet (m + 1).toNat n.toNat L.period (Module.finrank F V / L.period) q →
      x ∈ labelSet (m.toNat + 1) n.toNat L.period (Module.finrank F V / L.period) q := by
    rw [hm1]
    exact fun _ h => h
  have hmemG : ∀ S, (ρ' (G S)).1 ∈
      labelSet (m.toNat + 1) n.toNat L.period (Module.finrank F V / L.period) q :=
    fun S => hsucc _ (ρ' (G S)).2
  have hsomeP : ∀ S x, ℓ S = some x → _ := fun S x h => (hlabOf (G S)).2.2 (S'' S) (hfib S) x h
  have hlev : ∀ S x, ℓ S = some x → x.level = m.toNat + 1 := by
    intro S x h
    rw [(hsomeP S x h).1, (G S).2.2.2.1, hm1]
  have hmem : ∀ S, lbl S ∈
      labelSet m.toNat n.toNat L.period (Module.finrank F V / L.period) q := by
    intro S
    rcases h : ℓ S with _ | x
    · simp only [lbl, h]
      exact labelSet_succ_subset (hmemG S)
    · simp only [lbl, h]
      obtain ⟨-, hdeg, hram, hexp, hpoly, hdvd, -, -⟩ := hsomeP S x h
      rw [(G S).2.1] at hram hdvd
      refine snoc_mem_labelSet (hmemG S) (hlev S x h) hdeg ?_ ?_ hpoly ?_
      · rw [hram, hdiv S, (G S).2.2.2.1]
        exact congrArg (fun t => Nat.gcd t _) hm1
      · rw [hexp, hGd S]
      · rw [hGd S]
        exact hdvd
  refine ⟨fun S => ⟨lbl S, hmem S⟩, ?_, ?_⟩
  · -- Equal labels give conjugate strata.
    intro S₁ S₂ hρ
    have hlbl : lbl S₁ = lbl S₂ := congrArg Subtype.val hρ
    have key : ρ' (G S₁) = ρ' (G S₂) ∧ ℓ S₁ = ℓ S₂ := by
      rcases h₁ : ℓ S₁ with _ | x₁ <;> rcases h₂ : ℓ S₂ with _ | x₂ <;>
        simp only [lbl, h₁, h₂] at hlbl
      · exact ⟨Subtype.ext hlbl, rfl⟩
      · exact absurd hlbl.symm (snoc_ne_of_mem_labelSet (hmemG S₁) (hlev S₂ x₂ h₂))
      · exact absurd hlbl (snoc_ne_of_mem_labelSet (hmemG S₂) (hlev S₁ x₁ h₁))
      · obtain ⟨hp, hx⟩ := Label.snoc_injective hlbl
        exact ⟨Subtype.ext hp, by rw [hx]⟩
    have hG12 : G S₂ = G S₁ := by
      apply hrep_congr
      rw [← hGρ S₁, ← hGρ S₂, key.1]
    have hfib₂ := hfib S₂
    have hℓ : labOf (G S₁) ((S'' S₁).b - (G S₁).1.b) =
        labOf (G S₁) ((S'' S₂).b - (G S₁).1.b) := by
      have := key.2
      simp only [ℓ] at this
      rw [hG12] at this
      exact this
    rw [hG12] at hfib₂
    obtain ⟨g, hg, hgc⟩ := (hlabOf (G S₁)).1 (S'' S₁) (S'' S₂) (hfib S₁) hfib₂ hℓ
    rw [(G S₁).2.1] at hg
    rw [(G S₁).2.1, (G S₁).2.2.2.1, show 1 - (m + 1) = -m by ring, hS''b, hS''b] at hgc
    refine ⟨u S₁ * g * (u S₂)⁻¹, mul_mem (mul_mem (hu S₁) hg) (inv_mem (hu S₂)), ?_⟩
    change _ - S₂.1.b ∈ S₂.1.chain.endFiltration (-S₂.1.r)
    rw [S₂.2.1, S₂.2.2.2.1]
    have h3 := L.mul_mem_endFiltration (L.mul_mem_endFiltration (hu S₂).1 hgc) (hu S₂).2.1
    rw [zero_add, add_zero] at h3
    convert h3 using 1
    simp only [mul_inv_rev, inv_inv, Units.val_mul]
    have e1 : ((u S₂ : (Module.End F V)ˣ) : Module.End F V) *
        (((u S₂)⁻¹ : (Module.End F V)ˣ) : Module.End F V) = 1 := Units.mul_inv _
    have e2 : (((u S₂)⁻¹ : (Module.End F V)ˣ) : Module.End F V) *
        ((u S₂ : (Module.End F V)ˣ) : Module.End F V) = 1 := Units.inv_mul _
    calc _ = (u S₂ : Module.End F V) * (((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) *
          ((↑((u S₁)⁻¹) : Module.End F V) * S₁.1.b * (u S₁ : Module.End F V)) * g) *
          (((u S₂)⁻¹ : (Module.End F V)ˣ) : Module.End F V) - S₂.1.b := by noncomm_ring
      _ = _ := by
        rw [show (u S₂ : Module.End F V) * (((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) *
            ((↑((u S₁)⁻¹) : Module.End F V) * S₁.1.b * (u S₁ : Module.End F V)) * g) *
            (((u S₂)⁻¹ : (Module.End F V)ˣ) : Module.End F V) - S₂.1.b =
            (u S₂ : Module.End F V) * (((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) *
            ((↑((u S₁)⁻¹) : Module.End F V) * S₁.1.b * (u S₁ : Module.End F V)) * g -
            (↑((u S₂)⁻¹) : Module.End F V) * S₂.1.b * (u S₂ : Module.End F V)) *
            (((u S₂)⁻¹ : (Module.End F V)ˣ) : Module.End F V) by
          simp only [mul_sub, sub_mul, ← mul_assoc, e1, one_mul]
          rw [mul_assoc _ (u S₂ : Module.End F V), e1, mul_one]]
  · -- The invariants.
    intro S
    obtain ⟨he', hf'⟩ := hconjinv S
    rcases h : ℓ S with _ | x
    · obtain ⟨he, hf⟩ := (hlabOf (G S)).2.1 (S'' S) (hfib S) h
      change (lbl S).d = _ ∧ _ * (lbl S).e = _
      simp only [lbl, h]
      refine ⟨by rw [hGd S, ← hf, hf'], ?_⟩
      rw [← he', he, hGe S]
    · obtain ⟨-, -, -, -, -, -, he, hf⟩ := hsomeP S x h
      change (lbl S).d = _ ∧ _ * (lbl S).e = _
      simp only [lbl, h]
      refine ⟨?_, ?_⟩
      · rw [Label.snoc_d, hGd S, ← hf, hf']
      · rw [Label.snoc_e, ← he', he, (G S).2.1]

/-- BK94 (1.14) for principal orders, by induction on `n − m`. -/
theorem exists_isStratumLabelling [FiniteDimensional F V]
    (hPi : PureStratumSimpleApproximationStatement.{uF, uV})
    (hPoly : MinimalSimpleStratumPolynomialStatement.{uF, uV})
    (hPolyE : MinimalSimpleStratumPolynomialStatement.{uV, uV})
    (L : LatticeChain 𝒪[F] F V) (hP : L.IsPrincipal) (n : ℤ) :
    ∀ k : ℕ, ∀ m : ℤ, 0 ≤ m → m + 1 + k = n → ∃ ρ, IsStratumLabelling L n m ρ := by
  intro k
  induction k with
  | zero =>
    intro m hm hk
    obtain rfl : m = n - 1 := by omega
    exact exists_isStratumLabelling_base hPoly L hP n (by omega)
  | succ k ih =>
    intro m hm hk
    obtain ⟨ρ', hρ'⟩ := ih (m + 1) (by omega) (by push_cast at hk; omega)
    exact exists_isStratumLabelling_step hPi hPolyE L hP n m hm (by omega) ρ' hρ'

end Langlands.BushnellKutzko.SimpleStratumLabel

namespace Langlands.BushnellKutzko

universe uF' uV'

/-- The label statement follows from the existence of simple approximations and from the
polynomial labels at depth `n − 1`, the latter both over the base field and over fields in
the universe of the endomorphism algebra. -/
theorem simpleStratumLabel_of
    (hPi : PureStratumSimpleApproximationStatement.{uF', uV'})
    (hPoly : MinimalSimpleStratumPolynomialStatement.{uF', uV'})
    (hPolyE : MinimalSimpleStratumPolynomialStatement.{uV', uV'}) :
    SimpleStratumLabelStatement.{uF', uV'} := by
  intro F _ _ _ _ V _ _ _ L m n _ hP hm hmn
  obtain ⟨ρ, hρ⟩ := SimpleStratumLabel.exists_isStratumLabelling hPi hPoly hPolyE L hP n
    (n - m - 1).toNat m hm (by omega)
  exact ⟨ρ, hρ⟩

end Langlands.BushnellKutzko
