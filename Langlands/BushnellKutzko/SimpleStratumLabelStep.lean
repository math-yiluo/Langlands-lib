import Langlands.BushnellKutzko.SimpleStratumLabelFibre
import Langlands.BushnellKutzko.SimpleStratumLabelResidue
import Langlands.BushnellKutzko.SimpleStratumLabelSequences
import Langlands.BushnellKutzko.SimpleStratumLabelPeriod
import Langlands.BushnellKutzko.SimpleStratumLabelTransfer
import Langlands.BushnellKutzko.MinimalSimpleStratumPolynomialStatement
import Langlands.BushnellKutzko.SubfieldOrderProof

/-! # Labels on the fibre of a simple stratum one level up -/

noncomputable section

open ValuativeRel Polynomial Langlands.Henniart.Numerical Langlands.FieldTheory

namespace Langlands.BushnellKutzko.SimpleStratumLabel

universe uF uV uk uk'

/-- A label polynomial of degree `d` stays one under a ring isomorphism of fields. -/
theorem map_mem_irreduciblePolynomialLabels {k : Type uk} {k' : Type uk'} [Field k] [Field k']
    (σ : k ≃+* k') {f : k[X]} (hm : f.Monic) (hi : Irreducible f) (hX : f ≠ X) :
    f.map (σ : k →+* k') ∈ irreduciblePolynomialLabels f.natDegree k' := by
  rw [mem_irreduciblePolynomialLabels_iff]
  refine ⟨hm.map _, ?_, natDegree_map_eq_of_injective σ.injective f, ?_⟩
  · have h := (MulEquiv.irreducible_iff (mapEquiv σ).toMulEquiv).mpr hi
    exact h
  · intro h
    apply hX
    have := congrArg (Polynomial.map (σ.symm : k' →+* k)) h
    rwa [Polynomial.map_map, show ((σ.symm : k' →+* k).comp (σ : k →+* k')) = RingHom.id k by
      ext; simp, Polynomial.map_id, Polynomial.map_X] at this

section Element

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The element `β` generates the field `F[β]` that it generates in `End_F(V)`. -/
theorem adjoin_generator_eq_top (β : Module.End F V) :
    Algebra.adjoin F ({(⟨β, Algebra.self_mem_adjoin_singleton F β⟩ : elementAlgebra β)} :
      Set (elementAlgebra β)) = ⊤ := by
  apply Subalgebra.map_injective (f := (elementAlgebra β).val) Subtype.val_injective
  rw [AlgHom.map_adjoin_singleton, Algebra.map_top, Subalgebra.range_val]
  rfl

/-- Principality depends only on the lattice subsets. -/
theorem isPrincipal_of_lattices {O O' K K' : Type*} [CommRing O] [CommRing O'] [Field K]
    [Field K'] [Algebra O K] [Algebra O' K'] [Module K V] [Module K' V] [Module O V]
    [IsScalarTower O K V] [Module O' V] [IsScalarTower O' K' V] (L : LatticeChain O K V)
    (L' : LatticeChain O' K' V) (h : ∀ i, (L.lattice i : Set V) = L'.lattice i)
    (hP : L.IsPrincipal) : L'.IsPrincipal := by
  have hA : ∀ i, (L'.lattice i).toAddSubgroup = (L.lattice i).toAddSubgroup := fun i =>
    AddSubgroup.ext fun v => by
      change v ∈ (L'.lattice i : Set V) ↔ v ∈ (L.lattice i : Set V)
      rw [h]
  intro i j
  rw [hA, hA, hA, hA]
  exact hP i j

/-- A simple stratum `[𝔄,n,r−1,β]` in the fibre of the simple stratum `[𝔄,n,r,γ]`:
same chain and depth `n`, level one lower, and `β ≡ γ (mod 𝔓^{−r})`. -/
def InFibre (T S : Stratum 𝒪[F] F V) : Prop :=
  S.chain = T.chain ∧ S.n = T.n ∧ S.r = T.r - 1 ∧ S.IsSimple ∧
    S.b - T.b ∈ T.chain.endFiltration (-T.r)

/-- The properties of a labelling of the fibre of `T` by `none` (null derived stratum) or one
more quadruple of a label (BK94 (1.8), (1.12) and (1.14)). -/
def IsFibreLabeller (T : Stratum 𝒪[F] F V)
    (lab : Module.End F V → Option (LabelEntry (Nat.card 𝓀[F]))) : Prop :=
  (∀ S₁ S₂, InFibre T S₁ → InFibre T S₂ → lab (S₁.b - T.b) = lab (S₂.b - T.b) →
    ∃ g ∈ T.chain.unitFiltration 0,
      ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * S₁.b * g - S₂.b ∈
        T.chain.endFiltration (1 - T.r)) ∧
  (∀ S, InFibre T S → lab (S.b - T.b) = none →
    elementRamificationIndex F S.b = elementRamificationIndex F T.b ∧
      elementResidueDegree F S.b = elementResidueDegree F T.b) ∧
  (∀ S, InFibre T S → ∀ x, lab (S.b - T.b) = some x →
    x.level = T.r.toNat ∧ 0 < x.degree ∧
    x.ramification = Nat.gcd T.r.toNat (T.chain.period / elementRamificationIndex F T.b) ∧
    (x.polynomial.exponent : ℕ) = elementResidueDegree F T.b ∧ x.PolyOK ∧
    elementResidueDegree F T.b * x.degree ∣ Module.finrank F V / T.chain.period ∧
    elementRamificationIndex F S.b * x.ramification = T.chain.period ∧
    elementResidueDegree F S.b = elementResidueDegree F T.b * x.degree)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- BK94 (1.8) with (1.4), (1.12) and the recurrence (1.13) for principal orders: the fibre of
a simple stratum `[𝔄,n,r,γ]`, `r ≥ 1`, has a labelling by `none` or one more quadruple
`(φ, r, deg φ, gcd(r, e(𝔄)/e(F[γ]|F)))`, with the stated invariants and the conjugacy
property. -/
theorem exists_isFibreLabeller [FiniteDimensional F V]
    (hPolyE : MinimalSimpleStratumPolynomialStatement.{uV, uV})
    (T : Stratum 𝒪[F] F V) (hT : T.IsSimple) (hP : T.chain.IsPrincipal) (hr : 1 ≤ T.r) :
    ∃ lab, IsFibreLabeller T lab := by
  classical
  obtain ⟨⟨hf, hE⟩, -⟩ := hT.1
  let E := elementAlgebra T.b
  let : Field E := hf.toField
  have : FiniteDimensional F E := inferInstanceAs (FiniteDimensional F (elementAlgebra T.b))
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  have : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite F E V
  set L := T.chain with hLdef
  have hE' : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer := hE
  let γE : E := ⟨T.b, Algebra.self_mem_adjoin_singleton F T.b⟩
  have hγE : subfieldEmbedding F E V γE = T.b := by ext v; rfl
  have hgen : Algebra.adjoin F ({γE} : Set E) = ⊤ := adjoin_generator_eq_top T.b
  obtain ⟨s⟩ := (tameCorestriction F V E).1
  let LE := L.relativeLatticeChain hE' (isIntegral_iff_mem_spectralInteger F E)
  have hLE : ∀ i, (LE.lattice i : Set V) = L.lattice i := fun _ => rfl
  have hLEP : LE.IsPrincipal := isPrincipal_of_lattices L LE (fun i => (hLE i).symm) hP
  let LS := L.subfieldChain E hE'
  have hLS : ∀ i, (LS.lattice i : Set V) = L.lattice i := fun _ => rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  let πE : RingPrimeElement 𝒪[E] := ⟨ϖ, hϖ.ne_zero, by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal, hϖ.maximalIdeal_eq]⟩
  set q := Nat.card 𝓀[F] with hqdef
  have hq : IsPrimePow q := by
    let := Fintype.ofFinite 𝓀[F]
    rw [hqdef, ← Fintype.card_eq_nat_card]
    exact FiniteField.isPrimePow_card _
  set eγ := subfieldRamificationIndex F E with heγdef
  set fγ := subfieldResidueDegree F E with hfγdef
  have heγ : elementRamificationIndex F T.b = eγ := by
    unfold elementRamificationIndex
    rw [dite_eq_left hf]
  have hfγ : elementResidueDegree F T.b = fγ := by
    unfold elementResidueDegree
    rw [dite_eq_left hf]
  have hef : eγ * fγ = Module.finrank F E := subfieldRamificationIndex_mul_residueDegree F E
  have hdegpos : 0 < Module.finrank F E := Module.finrank_pos
  have hfpos : 0 < fγ := by
    rw [← hef] at hdegpos
    exact Nat.pos_of_mul_pos_left hdegpos
  have hepos : 0 < eγ := by
    rw [← hef] at hdegpos
    exact Nat.pos_of_mul_pos_right hdegpos
  let Dp : ℕ+ := ⟨fγ, hfpos⟩
  let : Field (𝒪[E] ⧸ Ring.jacobson 𝒪[E]) := jacobsonResidueField E
  have : Finite (𝒪[E] ⧸ Ring.jacobson 𝒪[E]) := finite_jacobsonResidue E
  obtain ⟨ι⟩ := nonempty_ringEquiv_labelField hq Dp (𝒪[E] ⧸ Ring.jacobson 𝒪[E])
    (natCard_spectralJacobsonResidue F E)
  have hP1 : ∀ C : {C : Stratum 𝒪[E] E V //
        C.chain = LE ∧ C.n = T.r ∧ C.r = T.r - 1 ∧ C.IsSimple},
      ∃ (f : Polynomial (𝒪[E] ⧸ Ring.jacobson 𝒪[E])) (a : ℕ),
        f.Monic ∧ Irreducible f ∧ f ≠ Polynomial.X ∧ 0 < a ∧
        C.1.fundamentalPolynomial πE = f ^ a ∧
        f.natDegree ∣ Module.finrank E V / LE.period ∧
        elementResidueDegree E C.1.b = f.natDegree ∧
        elementRamificationIndex E C.1.b = LE.period / Nat.gcd LE.period T.r.natAbs :=
    (hPolyE E V LE T.r πE hLEP hr).1
  have hP2 : ∀ (C₁ C₂ : {C : Stratum 𝒪[E] E V //
        C.chain = LE ∧ C.n = T.r ∧ C.r = T.r - 1 ∧ C.IsSimple})
      (f : Polynomial (𝒪[E] ⧸ Ring.jacobson 𝒪[E])) (a b : ℕ),
      f.Monic → Irreducible f → 0 < a → 0 < b →
      C₁.1.fundamentalPolynomial πE = f ^ a → C₂.1.fundamentalPolynomial πE = f ^ b →
      ∃ u ∈ LE.unitFiltration 0,
        (↑(u⁻¹) : Module.End E V) * C₁.1.b * (u : Module.End E V) ∈ C₂.1.coset :=
    (hPolyE E V LE T.r πE hLEP hr).2
  -- The labelling.
  let Good : Module.End F V → Stratum 𝒪[E] E V → Prop := fun c C =>
    (C.chain = LE ∧ C.n = T.r ∧ C.r = T.r - 1 ∧ C.IsSimple) ∧
      (s c - C.b).restrictScalars F ∈ L.endFiltration (1 - T.r)
  let polyOf : {C : Stratum 𝒪[E] E V // C.chain = LE ∧ C.n = T.r ∧ C.r = T.r - 1 ∧ C.IsSimple} →
      Polynomial (𝒪[E] ⧸ Ring.jacobson 𝒪[E]) := fun C => Classical.choose (hP1 C)
  have hpolyOf : ∀ C, ∃ a : ℕ,
      (polyOf C).Monic ∧ Irreducible (polyOf C) ∧ polyOf C ≠ Polynomial.X ∧ 0 < a ∧
        C.1.fundamentalPolynomial πE = polyOf C ^ a ∧
        (polyOf C).natDegree ∣ Module.finrank E V / LE.period ∧
        elementResidueDegree E C.1.b = (polyOf C).natDegree ∧
        elementRamificationIndex E C.1.b = LE.period / Nat.gcd LE.period T.r.natAbs :=
    fun C => Classical.choose_spec (hP1 C)
  let entryOf : {C : Stratum 𝒪[E] E V // C.chain = LE ∧ C.n = T.r ∧ C.r = T.r - 1 ∧ C.IsSimple} →
      LabelEntry q := fun C =>
    { polynomial := ⟨Dp, (polyOf C).map
        (ι : (𝒪[E] ⧸ Ring.jacobson 𝒪[E]) →+* polarExtensionField (labelFieldSize q) Dp)⟩
      level := T.r.toNat
      degree := (polyOf C).natDegree
      ramification := Nat.gcd T.r.toNat (L.period / eγ) }
  let lab : Module.End F V → Option (LabelEntry q) := fun c =>
    if (s c).restrictScalars F ∈ L.endFiltration (1 - T.r) then none
    else if hg : ∃ C, Good c C then
      some (entryOf ⟨Classical.choose hg, (Classical.choose_spec hg).1⟩)
    else none
  -- On the fibre, `none` means that the derived element is null.
  have hnone : ∀ S, InFibre T S → lab (S.b - T.b) = none →
      (s (S.b - T.b)).restrictScalars F ∈ L.endFiltration (1 - T.r) := by
    intro S ⟨hSc, hSn, hSr, hS, hc⟩ hlab
    by_contra hnn
    obtain ⟨C₀, hC₀lat, hC₀n, hC₀r, hC₀, hC₀s⟩ :=
      exists_simple_of_derived_notMem T hT hf s S hSc hSn hSr hS hc hnn
    let C' := C₀.chainTransfer LE (fun i => (hC₀lat i).trans (hLE i).symm)
    have hg : ∃ C, Good (S.b - T.b) C :=
      ⟨C', ⟨rfl, hC₀n, hC₀r, (Stratum.isSimple_chainTransfer_iff _ _ _).mpr hC₀⟩, hC₀s⟩
    have : lab (S.b - T.b) = some (entryOf ⟨Classical.choose hg, (Classical.choose_spec hg).1⟩) := by
      simp only [lab, if_neg hnn, dif_pos hg]
    rw [this] at hlab
    exact Option.some_ne_none _ hlab
  have hsome : ∀ c x, lab c = some x → ∃ hg : ∃ C, Good c C,
      x = entryOf ⟨Classical.choose hg, (Classical.choose_spec hg).1⟩ := by
    intro c x hlab
    simp only [lab] at hlab
    split_ifs at hlab with h1 h2
    exact ⟨h2, (Option.some_injective _ hlab).symm⟩
  refine ⟨lab, ?_, ?_, ?_⟩
  · -- Conjugacy on equal labels.
    intro S₁ S₂ h₁ h₂ heq
    have hb₁ : T.b + (S₁.b - T.b) = S₁.b := by abel
    have hb₂ : T.b + (S₂.b - T.b) = S₂.b := by abel
    rcases hl : lab (S₁.b - T.b) with _ | x
    · have hl₂ : lab (S₂.b - T.b) = none := heq ▸ hl
      have hn₁ := hnone S₁ h₁ hl
      have hn₂ := hnone S₂ h₂ hl₂
      obtain ⟨g, hg, hgc⟩ := exists_unit_conj_of_derived T hT hγE hgen s LE hLE h₁.2.2.2.2
        h₂.2.2.2.2 (α₁ := 0) (α₂ := 0) (by simpa using hn₁) (by simpa using hn₂)
        (w := 1) (one_mem _) (by simp)
      rw [hb₁, hb₂] at hgc
      exact ⟨g, hg, hgc⟩
    · have hl₂ : lab (S₂.b - T.b) = some x := heq ▸ hl
      obtain ⟨hg₁, hx₁⟩ := hsome _ _ hl
      obtain ⟨hg₂, hx₂⟩ := hsome _ _ hl₂
      set C₁ : {C : Stratum 𝒪[E] E V // C.chain = LE ∧ C.n = T.r ∧ C.r = T.r - 1 ∧ C.IsSimple} :=
        ⟨Classical.choose hg₁, (Classical.choose_spec hg₁).1⟩
      set C₂ : {C : Stratum 𝒪[E] E V // C.chain = LE ∧ C.n = T.r ∧ C.r = T.r - 1 ∧ C.IsSimple} :=
        ⟨Classical.choose hg₂, (Classical.choose_spec hg₂).1⟩
      have hent : entryOf C₁ = entryOf C₂ := hx₁.symm.trans hx₂
      have hmap : (polyOf C₁).map
            (ι : (𝒪[E] ⧸ Ring.jacobson 𝒪[E]) →+* polarExtensionField (labelFieldSize q) Dp) =
          (polyOf C₂).map
            (ι : (𝒪[E] ⧸ Ring.jacobson 𝒪[E]) →+* polarExtensionField (labelFieldSize q) Dp) := by
        have h1 := congrArg (fun y : LabelEntry q => y.polynomial) hent
        simp only [entryOf, FieldPolynomial.mk.injEq, heq_eq_eq, true_and] at h1
        exact h1
      have hpoly : polyOf C₁ = polyOf C₂ := Polynomial.map_injective _ ι.injective hmap
      obtain ⟨a₁, hm₁, hi₁, -, ha₁, hfund₁, -⟩ := hpolyOf C₁
      obtain ⟨a₂, -, -, -, ha₂, hfund₂, -⟩ := hpolyOf C₂
      rw [← hpoly] at hfund₂
      obtain ⟨u, hu, huc⟩ := hP2 C₁ C₂ (polyOf C₁) a₁ a₂ hm₁ hi₁ ha₁ ha₂ hfund₁ hfund₂
      have hα : ((u⁻¹ : (Module.End E V)ˣ) : Module.End E V) * C₁.1.b * u - C₂.1.b ∈
          LE.endFiltration (1 - T.r) := by
        have h := huc
        change _ - C₂.1.b ∈ C₂.1.chain.endFiltration (-C₂.1.r) at h
        rw [C₂.2.1, C₂.2.2.2.1, show -(T.r - 1) = 1 - T.r by ring] at h
        exact h
      obtain ⟨g, hg, hgc⟩ := exists_unit_conj_of_derived T hT hγE hgen s LE hLE h₁.2.2.2.2
        h₂.2.2.2.2 (Classical.choose_spec hg₁).2 (Classical.choose_spec hg₂).2 hu hα
      rw [hb₁, hb₂] at hgc
      exact ⟨g, hg, hgc⟩
  · -- Null derived element: the invariants of `F[γ]`.
    intro S hS hl
    obtain ⟨hSc, hSn, hSr, hSs, hc⟩ := hS
    exact elementInvariants_of_derived_null T hT hγE hgen s S hSc hSn hSr hSs hc
      (hnone S ⟨hSc, hSn, hSr, hSs, hc⟩ hl)
  · -- A simple derived stratum: one more quadruple.
    intro S hS x hl
    obtain ⟨hSc, hSn, hSr, hSs, hc⟩ := hS
    obtain ⟨hg, rfl⟩ := hsome _ _ hl
    set C := Classical.choose hg with hCdef
    have hCg : Good (S.b - T.b) C := Classical.choose_spec hg
    set C₁ : {C : Stratum 𝒪[E] E V // C.chain = LE ∧ C.n = T.r ∧ C.r = T.r - 1 ∧ C.IsSimple} :=
      ⟨C, hCg.1⟩
    obtain ⟨a, hm, hi, hX, -, -, hdvd, hres, hram⟩ := hpolyOf C₁
    have hClat : ∀ i, (C.chain.lattice i : Set V) = LS.lattice i := fun i => by
      rw [hCg.1.1]
      exact (hLE i).trans (hLS i).symm
    let Csub := C.chainTransfer LS hClat
    have hinv := elementInvariants_of_derived_simple T hT hγE hgen s S hSc hSn hSr hSs hc
      Csub (fun i => hLS i) hCg.1.2.1 hCg.1.2.2.1
      ((Stratum.isSimple_chainTransfer_iff _ _ _).mpr hCg.1.2.2.2) hCg.2
    change elementRamificationIndex F S.b = eγ * elementRamificationIndex E C.b ∧
      elementResidueDegree F S.b = fγ * elementResidueDegree E C.b at hinv
    have hrnat : T.r.natAbs = T.r.toNat := by omega
    have hLEper : LE.period = L.period / eγ := L.relativeLatticeChain_period_eq_div hE'
    obtain ⟨𝓛', -, -, -, -, -, hper⟩ := subfieldOrder F V E L hE'
    have hLper : L.period = eγ * LE.period := by
      rw [hLEper, hper, Nat.mul_div_cancel_left _ hepos]
    have hLEpos : 0 < LE.period := LE.period_pos
    refine ⟨rfl, ?_, by rw [heγ], by rw [hfγ]; rfl, ?_, ?_, ?_, ?_⟩
    · exact Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hi)
    · exact map_mem_irreduciblePolynomialLabels ι hm hi hX
    · -- `f(F[γ]) deg φ` divides `N / e(𝔄)`.
      rw [hfγ]
      change fγ * (polyOf C₁).natDegree ∣ Module.finrank F V / L.period
      obtain ⟨d', hd'⟩ := period_dvd_finrank_of_isPrincipal LE hLEP
      have hN : Module.finrank F V = eγ * fγ * (LE.period * d') := by
        rw [← Module.finrank_mul_finrank F E V, ← hef, hd']
      rw [hd', Nat.mul_div_cancel_left _ hLEpos] at hdvd
      have hq' : Module.finrank F V / L.period = fγ * d' := by
        rw [hN, hLper]
        rw [show eγ * fγ * (LE.period * d') = (eγ * LE.period) * (fγ * d') by ring]
        exact Nat.mul_div_cancel_left _ (Nat.mul_pos hepos hLEpos)
      rw [hq']
      exact Nat.mul_dvd_mul_left _ hdvd
    · -- `e(F[β]) e_{r+1} = e(𝔄)`.
      change elementRamificationIndex F S.b * Nat.gcd T.r.toNat (L.period / eγ) = L.period
      rw [hinv.1, hram, ← hLEper, hrnat, Nat.gcd_comm T.r.toNat]
      rw [mul_assoc, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _), hLper]
    · -- `f(F[β]) = f(F[γ]) deg φ`.
      change elementResidueDegree F S.b = elementResidueDegree F T.b * (polyOf C₁).natDegree
      rw [hinv.2, hres, hfγ]

end Element

end Langlands.BushnellKutzko.SimpleStratumLabel
