import Langlands.Representation.Whittaker.LowerBlockLocalizationStatement
import Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
import Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.Group.GL.IntegralSubgroup
import Langlands.LocalField.Topology

/-!
# Proof of the JPSS lower-block Whittaker localization

JPSS section 9.2, printed pages 454–455. The source averages a Whittaker
function row by row against characters. Here every average is a finite sum
over coset representatives of two additive lattices, so the new function is
again an actual coefficient `g ↦ ℓ (π g w)` of the same functional `ℓ`.
-/

noncomputable section

open scoped WithZero
open Topology Classical

namespace Langlands.Whittaker.LowerBlockLocalizationProof

open HarmonicAnalysis GeneralLinear RankinSelberg

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology

/-! ## Additive lattices -/

theorem lattice_mul {A B : ℤ} {x y : F.Carrier} (hx : x ∈ T.additiveLattice A)
    (hy : y ∈ T.additiveLattice B) : x * y ∈ T.additiveLattice (A + B) := by
  rw [PadicField.TopologicalData.mem_additiveLattice] at hx hy ⊢
  rw [map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

theorem one_mem_lattice_iff (k : ℤ) : (1 : F.Carrier) ∈ T.additiveLattice k ↔ 0 ≤ k := by
  rw [PadicField.TopologicalData.mem_additiveLattice, map_one, WithZero.one_le_exp_iff]

theorem neg_one_mem_lattice_iff (k : ℤ) :
    (-1 : F.Carrier) ∈ T.additiveLattice k ↔ 0 ≤ k := by
  rw [neg_mem_iff, one_mem_lattice_iff]

theorem lattice_le {A B : ℤ} (h : A ≤ B) {x : F.Carrier} (hx : x ∈ T.additiveLattice A) :
    x ∈ T.additiveLattice B :=
  T.additiveLattice_mono h hx

theorem exists_mem_lattice (x : F.Carrier) : ∃ k : ℤ, x ∈ T.additiveLattice k := by
  by_cases hx : x = 0
  · exact ⟨0, hx ▸ (T.additiveLattice 0).zero_mem⟩
  · refine ⟨WithZero.log (T.discreteValuation x), ?_⟩
    rw [PadicField.TopologicalData.mem_additiveLattice,
      WithZero.exp_log ((T.discreteValuation.ne_zero_iff).mpr hx)]

/-- An element of a nonpositive lattice is not congruent to `-1`; in particular
`1 + x` is nonzero for `x ∈ π O`. -/
theorem one_add_ne_zero {k : ℤ} (hk : k ≤ -1) {x : F.Carrier}
    (hx : x ∈ T.additiveLattice k) : 1 + x ≠ 0 := by
  intro h
  have : x = -1 := by linear_combination h
  rw [this, neg_one_mem_lattice_iff] at hx
  omega

theorem uniformizer_ne_zero : T.uniformizer ≠ 0 := by
  apply T.discreteValuation.ne_zero_iff.mp
  rw [T.discreteValuation_uniformizer]
  exact WithZero.exp_ne_zero

theorem lattice_eq_image (k : ℤ) :
    (T.additiveLattice k : Set F.Carrier) =
      (fun t => T.uniformizer ^ (-k) * t) '' (T.Integers : Set F.Carrier) := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_image]
  rw [T.mem_additiveLattice_iff_exists_integer]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, t.property, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩

/-! ## Annihilators and finite character sums -/

theorem character_eq_one_of_mem (ψ : AdditiveCharacter) {x : F.Carrier}
    (hx : x ∈ T.additiveLattice (T.additiveConductor ψ)) :
    letI := T.topology
    ψ.complex x = 1 := by
  let := T.topology
  rw [UnitaryAdditiveCharacter.complex_apply, (T.additiveConductor_spec ψ).1 x hx]
  rfl

/-- The annihilator of `π^(-A) O` under `ψ` is `π^(-(n(ψ)-A)) O`. -/
theorem annihilator_iff (ψ : AdditiveCharacter) (A : ℤ) (y : F.Carrier) :
    letI := T.topology
    (∀ s ∈ T.additiveLattice A, ψ.complex (s * y) = 1) ↔
      y ∈ T.additiveLattice (T.additiveConductor ψ - A) := by
  let := T.topology
  constructor
  · intro h
    by_contra hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hy (T.additiveLattice _).zero_mem
    obtain ⟨x₀, hx₀, hψ⟩ := T.exists_nontrivial_at_conductor_succ ψ
    have hord : T.ord y ≤ A - T.additiveConductor ψ - 1 := by
      have h1 : ¬ y * 1 ∈ T.additiveLattice (T.additiveConductor ψ - A) := by
        rwa [mul_one]
      rw [T.mul_mem_additiveLattice_iff hy0, one_mem_lattice_iff] at h1
      omega
    have hs : y⁻¹ * x₀ ∈ T.additiveLattice A := by
      rw [T.mul_mem_additiveLattice_iff (inv_ne_zero hy0), T.ord_inv]
      exact T.additiveLattice_mono (by omega) hx₀
    have := h _ hs
    rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hy0, one_mul,
      UnitaryAdditiveCharacter.complex_apply] at this
    exact hψ (Subtype.ext (by simpa using this))
  · intro hy s hs
    apply character_eq_one_of_mem T ψ
    simpa using lattice_mul T hs hy

/-- Finite character sums cut out every lattice coset inside a larger lattice. -/
theorem exists_character_sum (ψ : AdditiveCharacter) (B S : ℤ) (e : F.Carrier) :
    letI := T.topology
    ∃ (s : Finset F.Carrier) (c : F.Carrier → ℂ), ∀ y ∈ T.additiveLattice B,
      ∑ t ∈ s, c t * ψ.complex (t * y) =
        if y - e ∈ T.additiveLattice S then 1 else 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨b, hb⟩ := exists_mem_lattice T e
  set B' := max (max B S) b with hB'
  set cond := T.additiveConductor ψ
  let A := T.additiveLattice (cond - S)
  let A' := T.additiveLattice (cond - B')
  have hAA' : A' ≤ A := T.additiveLattice_mono (by omega)
  let : CompactSpace A := isCompact_iff_compactSpace.mp (T.isCompact_additiveLattice _)
  have hopen : IsOpen ((A'.addSubgroupOf A : AddSubgroup A) : Set A) :=
    AddSubgroup.addSubgroupOf_isOpen A A' (T.isOpen_additiveLattice _)
  let Q := A ⧸ A'.addSubgroupOf A
  have : Finite Q := AddSubgroup.quotient_finite_of_isOpen _ hopen
  let : Fintype Q := Fintype.ofFinite Q
  let r : Q → F.Carrier := fun q => ((Quotient.out q : A) : F.Carrier)
  have hr_inj : Function.Injective r := by
    intro q₁ q₂ h
    rw [← QuotientAddGroup.out_eq' q₁, ← QuotientAddGroup.out_eq' q₂]
    exact congrArg _ (Subtype.ext h)
  have hrA (q : Q) : r q ∈ A := (Quotient.out q).property
  have hcard : (Fintype.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨Finset.univ.image r,
    fun t => ψ.complex (-(t * e)) / (Fintype.card Q : ℂ), ?_⟩
  intro y hy
  have hyB : y - e ∈ T.additiveLattice B' :=
    sub_mem (T.additiveLattice_mono (by omega) hy) (T.additiveLattice_mono (by omega) hb)
  rw [Finset.sum_image (fun q₁ _ q₂ _ h => hr_inj h)]
  have hterm (q : Q) : ψ.complex (-(r q * e)) / (Fintype.card Q : ℂ) * ψ.complex (r q * y) =
      ψ.complex (r q * (y - e)) / (Fintype.card Q : ℂ) := by
    rw [div_mul_eq_mul_div, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [hterm, ← Finset.sum_div]
  set y' := y - e
  split_ifs with hy'
  · have hone (q : Q) : ψ.complex (r q * y') = 1 :=
      character_eq_one_of_mem T ψ (by simpa using lattice_mul T (hrA q) hy')
    simp_rw [hone]
    simp [hcard]
  · have hex : ∃ t₀ ∈ A, ψ.complex (t₀ * y') ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hy'
      have := (annihilator_iff T ψ (cond - S) y').mp hcon
      rwa [sub_sub_cancel] at this
    obtain ⟨t₀, ht₀, hψ⟩ := hex
    let q₀ : Q := QuotientAddGroup.mk ⟨t₀, ht₀⟩
    have hshift (q : Q) : ψ.complex (r (q₀ + q) * y') =
        ψ.complex (t₀ * y') * ψ.complex (r q * y') := by
      have hmk : (QuotientAddGroup.mk (Quotient.out (q₀ + q)) : Q) =
          QuotientAddGroup.mk (⟨t₀, ht₀⟩ + Quotient.out q) := by
        rw [QuotientAddGroup.out_eq', QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hmk
      have hdiff : (-(r (q₀ + q)) + (t₀ + r q)) * y' ∈ T.additiveLattice cond := by
        have := lattice_mul T hmk hyB
        simpa using this
      have h1 := character_eq_one_of_mem T ψ hdiff
      rw [← AddChar.map_add_eq_mul]
      have heq : r (q₀ + q) * y' =
          (t₀ * y' + r q * y') + -((-(r (q₀ + q)) + (t₀ + r q)) * y') := by ring
      rw [heq, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, h1, inv_one, mul_one]
    have hsum : ∑ q : Q, ψ.complex (r q * y') =
        ψ.complex (t₀ * y') * ∑ q : Q, ψ.complex (r q * y') := by
      rw [Finset.mul_sum]
      simp_rw [← hshift]
      exact (Fintype.sum_equiv (Equiv.addLeft q₀) _ _ (fun q => rfl)).symm
    rw [eq_zero_of_mul_eq_self_left hψ hsum.symm, zero_div]

/-! ## Lattice boxes inside neighborhoods -/

/-- A neighborhood in a finite product contains a uniform box, as soon as
each factor has a monotone family of boxes forming a neighborhood basis. -/
theorem exists_pi_box {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (B : ∀ i, ℤ → Set (X i)) (hB : ∀ i S S', S ≤ S' → B i S ⊆ B i S') (x : ∀ i, X i)
    (hx : ∀ i, ∀ N ∈ 𝓝 (x i), ∃ S, B i S ⊆ N) {N : Set (∀ i, X i)} (hN : N ∈ 𝓝 x) :
    ∃ S : ℤ, ∀ y : ∀ i, X i, (∀ i, y i ∈ B i S) → y ∈ N := by
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hsub⟩ := hN
  choose S hS using fun i => hx i (t i) (ht i)
  refine ⟨-∑ i, |S i|, fun y hy => hsub fun i _ => hS i (hB i _ _ ?_ (hy i))⟩
  have h1 : |S i| ≤ ∑ j, |S j| :=
    Finset.single_le_sum (f := fun j => |S j|) (fun j _ => abs_nonneg (S j))
      (Finset.mem_univ i)
  have h2 := neg_abs_le (S i)
  linarith

theorem exists_scalar_box (e : F.Carrier) {N : Set F.Carrier}
    (hN : letI := T.topology; N ∈ 𝓝 e) :
    ∃ S : ℤ, ∀ y, y - e ∈ T.additiveLattice S → y ∈ N := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have h0 : (fun z => z + e) ⁻¹' N ∈ 𝓝 (0 : F.Carrier) := by
    apply (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds
    simpa using hN
  obtain ⟨S, hS⟩ := T.exists_additiveLattice_subset h0
  exact ⟨S, fun y hy => by simpa using hS hy⟩

theorem exists_matrix_box {ι κ : Type*} [Fintype ι] [Fintype κ] (x : Matrix ι κ F.Carrier)
    {N : Set (Matrix ι κ F.Carrier)} (hN : letI := T.topology; N ∈ 𝓝 x) :
    ∃ S : ℤ, ∀ y : Matrix ι κ F.Carrier,
      (∀ i j, y i j - x i j ∈ T.additiveLattice S) → y ∈ N := by
  let := T.topology
  obtain ⟨S, hS⟩ := exists_pi_box (X := fun _ : ι => κ → F.Carrier)
    (fun i S => {r | ∀ j, r j - x i j ∈ T.additiveLattice S})
    (fun i S S' h r hr j => T.additiveLattice_mono h (hr j)) x
    (fun i N' hN' => by
      obtain ⟨S, hS⟩ := exists_pi_box (X := fun _ : κ => F.Carrier)
        (fun j S => {y | y - x i j ∈ T.additiveLattice S})
        (fun j S S' h y hy => T.additiveLattice_mono h hy) (x i)
        (fun j N'' hN'' => by
          obtain ⟨S, hS⟩ := exists_scalar_box T (x i j) hN''
          exact ⟨S, fun y hy => hS y hy⟩) hN'
      exact ⟨S, fun r hr => hS r hr⟩) hN
  exact ⟨S, fun y hy => hS y (fun i j => hy i j)⟩

/-- Every neighborhood of `1` in `GL_m` contains all matrices whose entries and
inverse entries are congruent to the identity modulo one lattice. -/
theorem exists_unit_box {m : ℕ} {U : Set (Langlands.GeneralLinear m F.Carrier)}
    (hU : letI := T.topology; U ∈ 𝓝 (1 : Langlands.GeneralLinear m F.Carrier)) :
    ∃ S : ℤ, ∀ g : Langlands.GeneralLinear m F.Carrier,
      (∀ i j, g.val i j - (1 : Matrix (Fin m) (Fin m) F.Carrier) i j ∈ T.additiveLattice S) →
      (∀ i j, g⁻¹.val i j - (1 : Matrix (Fin m) (Fin m) F.Carrier) i j ∈
        T.additiveLattice S) →
      g ∈ U := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨t, ht, htU⟩ := hU
  have h1 : Units.embedProduct (Matrix (Fin m) (Fin m) F.Carrier) 1 =
      ((1 : Matrix (Fin m) (Fin m) F.Carrier), MulOpposite.op 1) := by
    simp
  rw [h1, nhds_prod_eq, Filter.mem_prod_iff] at ht
  obtain ⟨A, hA, B, hB, hAB⟩ := ht
  have hB' : MulOpposite.op ⁻¹' B ∈ 𝓝 (1 : Matrix (Fin m) (Fin m) F.Carrier) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB
  obtain ⟨S₁, hS₁⟩ := exists_matrix_box T 1 hA
  obtain ⟨S₂, hS₂⟩ := exists_matrix_box T 1 hB'
  refine ⟨min S₁ S₂, fun g hg hg' => htU (hAB ⟨hS₁ _ ?_, hS₂ _ ?_⟩)⟩
  · exact fun i j => T.additiveLattice_mono (min_le_left _ _) (hg i j)
  · exact fun i j => T.additiveLattice_mono (min_le_right _ _) (hg' i j)

/-- A smooth vector is fixed by a whole lattice box of `GL_m`. -/
theorem exists_fixing_box {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear m F.Carrier) V)
    (hπ : letI := T.topology; IsSmooth π) (w : V) :
    ∃ S : ℤ, ∀ g : Langlands.GeneralLinear m F.Carrier,
      (∀ i j, g.val i j - (1 : Matrix (Fin m) (Fin m) F.Carrier) i j ∈ T.additiveLattice S) →
      (∀ i j, g⁻¹.val i j - (1 : Matrix (Fin m) (Fin m) F.Carrier) i j ∈
        T.additiveLattice S) →
      π g w = w := by
  let := T.topology
  obtain ⟨K, hK⟩ := hπ w
  obtain ⟨S, hS⟩ := exists_unit_box T (K.isOpen.mem_nhds K.one_mem)
  refine ⟨S, fun g hg hg' => ?_⟩
  exact (Representation.mem_invariants _ w).mp hK ⟨g, hS g hg hg'⟩

/-! ## Row-graded congruences for lower triangular matrices -/

theorem one_apply_mem_lattice_zero {m : ℕ} (i j : Fin m) :
    (1 : Matrix (Fin m) (Fin m) F.Carrier) i j ∈ T.additiveLattice 0 := by
  rw [Matrix.one_apply]
  split_ifs
  · exact (one_mem_lattice_iff T 0).mpr le_rfl
  · exact zero_mem _

/-- A lower triangular matrix congruent to `1` row by row, modulo lattices
inside `π O`, has determinant of valuation one. -/
theorem discreteValuation_det {m : ℕ} (A : Matrix (Fin m) (Fin m) F.Carrier)
    (hlow : A.IsLowerTriangular) (R : Fin m → ℤ) (hR : ∀ i, R i ≤ -1)
    (hA : ∀ i j, A i j - (1 : Matrix (Fin m) (Fin m) F.Carrier) i j ∈ T.additiveLattice (R i)) :
    T.discreteValuation A.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular A hlow, map_prod]
  apply Finset.prod_eq_one
  intro i _
  have h := hA i i
  rw [Matrix.one_apply_eq, PadicField.TopologicalData.mem_additiveLattice] at h
  have hlt : T.discreteValuation (A i i - 1) < 1 :=
    lt_of_le_of_lt h (by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      linarith [hR i])
  have := T.discreteValuation.map_one_add_of_lt hlt
  rwa [add_sub_cancel] at this

/-- Lemma D: the row-graded congruence passes to the inverse. -/
theorem inv_rowBox {m : ℕ} (g : Langlands.GeneralLinear m F.Carrier)
    (hlow : g.val.IsLowerTriangular) (R : Fin m → ℤ) (hR : ∀ i, R i ≤ -1)
    (hg : ∀ i j, g.val i j - (1 : Matrix (Fin m) (Fin m) F.Carrier) i j ∈
      T.additiveLattice (R i)) :
    ∀ i j, g⁻¹.val i j - (1 : Matrix (Fin m) (Fin m) F.Carrier) i j ∈
      T.additiveLattice (R i) := by
  let := T.valuativeRel
  have hint (i j : Fin m) : g.val i j ∈ T.additiveLattice 0 := by
    have := add_mem (T.additiveLattice_mono (hR i |>.trans (by norm_num)) (hg i j))
      (one_apply_mem_lattice_zero T i j)
    rwa [sub_add_cancel] at this
  have hdet := discreteValuation_det T g.val hlow R hR hg
  have hdet0 : g.val.det ≠ 0 := by
    intro h
    rw [h, map_zero] at hdet
    exact zero_ne_one hdet
  -- integrality of the adjugate
  let g' : Matrix (Fin m) (Fin m) T.Integers := fun i j =>
    ⟨g.val i j, (T.mem_additiveLattice_zero _).mp (hint i j)⟩
  have hg' : (T.Integers.subtype).mapMatrix g' = g.val := by
    ext i j
    rfl
  have hadj (i j : Fin m) : g.val.adjugate i j ∈ T.additiveLattice 0 := by
    rw [← hg', ← RingHom.map_adjugate]
    exact (T.mem_additiveLattice_zero _).mpr (g'.adjugate i j).property
  have hinvint (i j : Fin m) : g⁻¹.val i j ∈ T.additiveLattice 0 := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
      smul_eq_mul, PadicField.TopologicalData.mem_additiveLattice, map_mul, map_inv₀, hdet,
      inv_one, one_mul]
    exact hadj i j
  have hid (i j : Fin m) : g⁻¹.val i j - (1 : Matrix (Fin m) (Fin m) F.Carrier) i j =
      -∑ k, (g.val i k - (1 : Matrix (Fin m) (Fin m) F.Carrier) i k) * g⁻¹.val k j := by
    have h1 : (g.val * g⁻¹.val) i j = (1 : Matrix (Fin m) (Fin m) F.Carrier) i j := by
      rw [Units.mul_inv]
    rw [Matrix.mul_apply] at h1
    simp only [sub_mul, Finset.sum_sub_distrib, h1, Matrix.one_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  intro i j
  rw [hid]
  refine neg_mem (AddSubgroup.sum_mem _ fun k _ => ?_)
  simpa using lattice_mul T (hg i k) (hinvint k j)

/-! ## Elementary matrices and the column step -/

/-- The elementary matrix `1 + t e_{lm}` in `GL_N`. -/
def elementary {N : ℕ} (l m : Fin N) (hlm : l ≠ m) (t : F.Carrier) :
    Langlands.GeneralLinear N F.Carrier :=
  ⟨Matrix.transvection l m t, Matrix.transvection l m (-t),
    by rw [Matrix.transvection_mul_transvection_same _ _ hlm, add_neg_cancel,
      Matrix.transvection_zero],
    by rw [Matrix.transvection_mul_transvection_same _ _ hlm, neg_add_cancel,
      Matrix.transvection_zero]⟩

theorem elementary_box {N : ℕ} (l m : Fin N) (hlm : l ≠ m) {t : F.Carrier} {S : ℤ}
    (ht : t ∈ T.additiveLattice S) :
    (∀ i j, (elementary l m hlm t).val i j - (1 : Matrix (Fin N) (Fin N) F.Carrier) i j ∈
      T.additiveLattice S) ∧
    (∀ i j, (elementary l m hlm t)⁻¹.val i j - (1 : Matrix (Fin N) (Fin N) F.Carrier) i j ∈
      T.additiveLattice S) := by
  have key (s : F.Carrier) (hs : s ∈ T.additiveLattice S) (i j : Fin N) :
      Matrix.transvection l m s i j - (1 : Matrix (Fin N) (Fin N) F.Carrier) i j ∈
        T.additiveLattice S := by
    rw [Matrix.transvection, Matrix.add_apply, add_sub_cancel_left, Matrix.single_apply]
    split_ifs
    · exact hs
    · exact zero_mem _
  exact ⟨key t ht, key (-t) (neg_mem ht)⟩

/-- If the rows of `M` from `m` on are standard basis rows, conjugating
`1 + t e_{lm}` by `M` gives `1 + t (M e_l) e_mᵀ`. -/
theorem conj_elementary_val {N : ℕ} (M : Langlands.GeneralLinear N F.Carrier) {l m : Fin N}
    (hlm : l < m)
    (hM : ∀ i, m ≤ i → ∀ j, M.val i j = (1 : Matrix (Fin N) (Fin N) F.Carrier) i j)
    (t : F.Carrier) :
    (M * elementary l m hlm.ne t * M⁻¹).val =
      1 + Matrix.of (fun i j => if j = m then t * M.val i l else 0) := by
  have key : (1 + Matrix.of (fun i j => if j = m then t * M.val i l else 0)) * M.val =
      M.val * Matrix.transvection l m t := by
    ext i j
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply]
    simp only [Matrix.of_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    rw [hM m le_rfl j]
    by_cases hj : j = m
    · subst hj
      rw [Matrix.mul_transvection_apply_same, Matrix.one_apply_eq]
      ring
    · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hj, Matrix.one_apply_ne (Ne.symm hj)]
      ring
  calc (M * elementary l m hlm.ne t * M⁻¹).val
      = M.val * Matrix.transvection l m t * M⁻¹.val := rfl
    _ = (1 + Matrix.of (fun i j => if j = m then t * M.val i l else 0)) *
          (M.val * M⁻¹.val) := by
        rw [← key, Matrix.mul_assoc]
    _ = _ := by rw [Units.mul_inv, Matrix.mul_one]

theorem conj_elementary_mem {N : ℕ} (M : Langlands.GeneralLinear N F.Carrier) {l m : Fin N}
    (hlm : l < m)
    (hM : ∀ i, m ≤ i → ∀ j, M.val i j = (1 : Matrix (Fin N) (Fin N) F.Carrier) i j)
    (t : F.Carrier) :
    M * elementary l m hlm.ne t * M⁻¹ ∈ upperUnipotent N F.Carrier := by
  have hv := conj_elementary_val M hlm hM t
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · have hji' : j < i := hji
    change (M * elementary l m hlm.ne t * M⁻¹).val i j = 0
    rw [hv, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne hji'.ne', zero_add]
    split_ifs with hj
    · subst hj
      rw [hM i hji'.le l, Matrix.one_apply_ne (hlm.trans hji').ne', mul_zero]
    · rfl
  · change (M * elementary l m hlm.ne t * M⁻¹).val i i = 1
    rw [hv, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_eq]
    split_ifs with hi
    · subst hi
      rw [hM i le_rfl l, Matrix.one_apply_ne hlm.ne', mul_zero, add_zero]
    · rw [add_zero]

theorem superdiag_conj_elementary {n : ℕ} (M : Langlands.GeneralLinear (n + 1) F.Carrier)
    (ρ : Fin n) {l : Fin (n + 1)} (hl : l < ρ.succ)
    (hM : ∀ i, ρ.succ ≤ i → ∀ j,
      M.val i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j)
    (t : F.Carrier) :
    ∑ i : Fin n, (M * elementary l ρ.succ hl.ne t * M⁻¹).val i.castSucc i.succ =
      t * M.val ρ.castSucc l := by
  rw [conj_elementary_val M hl hM t]
  have h1 (i : Fin n) :
      (1 + Matrix.of (fun i j => if j = ρ.succ then t * M.val i l else 0) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i.castSucc i.succ =
        if i = ρ then t * M.val ρ.castSucc l else 0 := by
    rw [Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne (show i.castSucc < i.succ from Fin.castSucc_lt_succ).ne,
      zero_add]
    by_cases hi : i = ρ
    · subst hi
      simp
    · simp [hi]
  simp_rw [h1]
  simp

/-- The Whittaker functional sees the elementary translate through the character
of the conjugated unipotent matrix. -/
theorem coeff_elementary [TopologicalSpace F.Carrier] (ψ : UnitaryAdditiveCharacter F.Carrier)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ n π) (ρ : Fin n) {l : Fin (n + 1)} (hl : l < ρ.succ)
    (M : Langlands.GeneralLinear (n + 1) F.Carrier)
    (hM : ∀ i, ρ.succ ≤ i → ∀ j,
      M.val i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j)
    (t : F.Carrier) (w : V) :
    ℓ.val (π M (π (elementary l ρ.succ hl.ne t) w)) =
      ψ.complex (t * M.val ρ.castSucc l) * ℓ.val (π M w) := by
  have hmem := conj_elementary_mem M hl hM t
  have h := ℓ.property ⟨_, hmem⟩ (π M w)
  dsimp only at h
  rw [standardCharacter_apply] at h
  dsimp only at h
  rw [superdiag_conj_elementary M ρ hl hM t, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel_right] at h
  rw [← Module.End.mul_apply, ← map_mul]
  exact h

/-- One column of the JPSS averaging: cut the entry `M ρ l` down to `e + π^(-P) O`. -/
theorem column_step [τ : TopologicalSpace F.Carrier] (hτ : τ = T.topology)
    (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ} {V : Type uV} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hπ : IsSmooth π) (ℓ : glFunctionals ψ n π) (ρ : Fin n) {l : Fin (n + 1)}
    (hl : l < ρ.succ) (e : F.Carrier) (P : ℤ) (w : V) :
    ∃ w' : V, ∀ M : Langlands.GeneralLinear (n + 1) F.Carrier,
      (∀ i, ρ.succ ≤ i → ∀ j,
        M.val i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j) →
      ℓ.val (π M w') =
        if M.val ρ.castSucc l - e ∈ T.additiveLattice P then ℓ.val (π M w) else 0 := by
  subst hτ
  let : TopologicalSpace F.Carrier := T.topology
  obtain ⟨S₁, hS₁⟩ := exists_fixing_box T π hπ w
  obtain ⟨s, c, hsum⟩ := exists_character_sum T ψ (T.additiveConductor ψ - S₁) P e
  refine ⟨∑ t ∈ s, c t • π (elementary l ρ.succ hl.ne t) w, fun M hM => ?_⟩
  have hcoef := fun t => coeff_elementary ψ π ℓ ρ hl M hM t w
  rw [map_sum, map_sum]
  simp_rw [map_smul, smul_eq_mul, hcoef]
  by_cases h0 : ℓ.val (π M w) = 0
  · simp [h0]
  · have hy : M.val ρ.castSucc l ∈ T.additiveLattice (T.additiveConductor ψ - S₁) := by
      rw [← annihilator_iff]
      intro t ht
      have hbox := elementary_box T l ρ.succ hl.ne ht
      have h := hcoef t
      rw [hS₁ _ hbox.1 hbox.2] at h
      exact (mul_eq_right₀ h0).mp h.symm
    simp_rw [← mul_assoc, ← Finset.sum_mul, hsum _ hy]
    split_ifs <;> simp

/-- A whole row of the JPSS averaging, over a finite set of columns left of `ρ.succ`. -/
theorem row_step [τ : TopologicalSpace F.Carrier] (hτ : τ = T.topology)
    (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ} {V : Type uV} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hπ : IsSmooth π) (ℓ : glFunctionals ψ n π) (ρ : Fin n) (e : Fin (n + 1) → F.Carrier)
    (P : ℤ) (C : Finset (Fin (n + 1))) (hC : ∀ l ∈ C, l < ρ.succ) (w : V) :
    ∃ w' : V, ∀ M : Langlands.GeneralLinear (n + 1) F.Carrier,
      (∀ i, ρ.succ ≤ i → ∀ j,
        M.val i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j) →
      ℓ.val (π M w') =
        if (∀ l ∈ C, M.val ρ.castSucc l - e l ∈ T.additiveLattice P) then
          ℓ.val (π M w) else 0 := by
  induction C using Finset.induction_on with
  | empty => exact ⟨w, fun M _ => by simp⟩
  | insert l C hlC ih =>
    obtain ⟨w₁, hw₁⟩ := ih (fun l' hl' => hC l' (Finset.mem_insert_of_mem hl'))
    obtain ⟨w', hw'⟩ := column_step T hτ ψ π hπ ℓ ρ (hC l (Finset.mem_insert_self l C))
      (e l) P w₁
    refine ⟨w', fun M hM => ?_⟩
    rw [hw' M hM, hw₁ M hM]
    simp only [Finset.forall_mem_insert]
    by_cases h1 : M.val ρ.castSucc l - e l ∈ T.additiveLattice P
    · by_cases h2 : ∀ l ∈ C, M.val ρ.castSucc l - e l ∈ T.additiveLattice P
      · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left ⟨h1, h2⟩]
      · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right (fun h => h2 h.2)]
    · rw [ite_eq_right h1, ite_eq_right (fun h => h1 h.1)]

/-! ## Row-by-row localization of the middle block -/

/-- After `k` rows of the middle block have been averaged, the coefficient of the
new vector at `M` is the coefficient of `v` at the matrix `M₀` whose middle rows are
trivialized, cut down by row-graded congruences in the rows `a, …, a+k-1`. -/
theorem main_claim [τ : TopologicalSpace F.Carrier] (hτ : τ = T.topology)
    (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ} {V : Type uV} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hπ : IsSmooth π) (ℓ : glFunctionals ψ n π) (v : V) (a d : ℕ) (had : a + d ≤ n)
    (S₀ : ℤ) (hS₀ : S₀ ≤ -1) (k : ℕ) (hk : k ≤ d) :
    ∃ (w : V) (S : ℕ → ℤ), (∀ i, S i ≤ S₀) ∧
      ∀ M M₀ : Langlands.GeneralLinear (n + 1) F.Carrier,
        (∀ i : Fin (n + 1), a + k ≤ i.val → ∀ j,
          M.val i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j) →
        (∀ i j : Fin (n + 1), a ≤ j.val → i < j → M.val i j = 0) →
        (∀ i j : Fin (n + 1), M₀.val i j = if i.val < a then M.val i j else
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j) →
        ℓ.val (π M w) =
          if (∀ i j : Fin (n + 1), a ≤ i.val → i.val < a + k →
            M.val i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j ∈
              T.additiveLattice (S (i.val - a)))
          then ℓ.val (π M₀ v) else 0 := by
  subst hτ
  let : TopologicalSpace F.Carrier := T.topology
  induction k with
  | zero =>
    refine ⟨v, fun _ => S₀, fun _ => le_rfl, fun M M₀ hM _ hM₀ => ?_⟩
    have hMM : M₀ = M := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      rw [hM₀ i j]
      by_cases hi : i.val < a
      · rw [ite_eq_left hi]
      · rw [ite_eq_right hi]
        exact (hM i (by omega) j).symm
    rw [hMM, ite_eq_left]
    intro i j h₁ h₂
    exact absurd h₂ (by omega)
  | succ k ih =>
    obtain ⟨w₀, S, hS, hw₀⟩ := ih (by omega)
    let ρ' : Fin n := ⟨a + k, by omega⟩
    have hρ'v : ρ'.val = a + k := rfl
    have hρv : (ρ'.castSucc : Fin (n + 1)).val = a + k := rfl
    have hne (i : Fin (n + 1)) : i = ρ'.castSucc ↔ i.val = a + k := by
      rw [Fin.ext_iff, hρv]
    obtain ⟨S₁, hS₁⟩ := exists_fixing_box T π hπ w₀
    have hP1 : min S₀ S₁ ≤ -1 := (min_le_left _ _).trans hS₀
    have hPS₁ : min S₀ S₁ ≤ S₁ := min_le_right _ _
    obtain ⟨w', hw'⟩ := row_step T rfl ψ π hπ ℓ ρ'
      (fun l => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) ρ'.castSucc l) (min S₀ S₁)
      (Finset.univ.filter (fun l => l < ρ'.succ)) (fun l hl => (Finset.mem_filter.mp hl).2) w₀
    refine ⟨w', fun i => if i = k then min S₀ S₁ else S i, fun i => ?_,
      fun M M₀ hM hup hM₀ => ?_⟩
    · dsimp only
      split_ifs
      · exact min_le_left _ _
      · exact hS i
    have hMρ : ∀ i, ρ'.succ ≤ i → ∀ j,
        M.val i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j := by
      intro i hi j
      have h' : ρ'.succ.val ≤ i.val := hi
      rw [Fin.val_succ, hρ'v] at h'
      exact hM i (by omega) j
    have hrow : (∀ l ∈ Finset.univ.filter (fun l => l < ρ'.succ),
        M.val ρ'.castSucc l - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) ρ'.castSucc l ∈
          T.additiveLattice (min S₀ S₁)) ↔
        ∀ j, M.val ρ'.castSucc j -
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) ρ'.castSucc j ∈
            T.additiveLattice (min S₀ S₁) := by
      constructor
      · intro hr j
        by_cases hj : j < ρ'.succ
        · exact hr j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
        · have hj' : a + k < j.val := by
            have h' : ¬ (j.val < ρ'.succ.val) := hj
            rw [Fin.val_succ, hρ'v] at h'
            omega
          have hρj : ρ'.castSucc < j := by
            rw [Fin.lt_def, hρv]
            exact hj'
          have hρj' : ρ'.castSucc ≠ j := fun e => by
            rw [← e, hρv] at hj'
            omega
          rw [hup _ j (by omega) hρj, Matrix.one_apply_ne hρj', sub_zero]
          exact zero_mem _
      · intro hr l _
        exact hr l
    rw [hw' M hMρ]
    by_cases hr : ∀ j, M.val ρ'.castSucc j -
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) ρ'.castSucc j ∈
          T.additiveLattice (min S₀ S₁)
    swap
    · rw [ite_eq_right (fun h => hr (hrow.mp h)), ite_eq_right]
      intro h
      apply hr
      intro j
      have e : (ρ'.castSucc : Fin (n + 1)).val - a = k := by omega
      have := h ρ'.castSucc j (by omega) (by omega)
      beta_reduce at this
      rwa [ite_eq_left e] at this
    rw [ite_eq_left (hrow.mpr hr)]
    -- the lower triangular matrix carrying row `ρ` of `M`
    let κm : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier := fun i j =>
      if i = ρ'.castSucc then M.val i j
      else (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j
    have hκlow : κm.IsLowerTriangular := by
      intro i j hij
      have hij' : i < j := hij
      simp only [κm]
      split_ifs with hi
      · subst hi
        have h' := Fin.lt_def.mp hij'
        rw [hρv] at h'
        exact hup _ j (by omega) hij'
      · exact Matrix.one_apply_ne hij'.ne
    have hκbox : ∀ i j, κm i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j ∈
        T.additiveLattice ((fun _ => min S₀ S₁) i) := by
      intro i j
      simp only [κm]
      split_ifs with hi
      · subst hi
        exact hr j
      · rw [sub_self]
        exact zero_mem _
    have hdet : κm.det ≠ 0 := by
      intro h0
      have h1 := discreteValuation_det T κm hκlow (fun _ => min S₀ S₁) (fun _ => hP1) hκbox
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    let κ : Langlands.GeneralLinear (n + 1) F.Carrier :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero κm hdet
    have hκfix : π κ w₀ = w₀ := by
      apply hS₁
      · intro i j
        exact lattice_le T hPS₁ (hκbox i j)
      · intro i j
        exact lattice_le T hPS₁
          (inv_rowBox T κ hκlow (fun _ => min S₀ S₁) (fun _ => hP1) hκbox i j)
    -- `M κ⁻¹` is `M` with row `ρ` trivialized
    let Mt : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier := fun i j =>
      if i = ρ'.castSucc then (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j
      else M.val i j
    have hcol : ∀ i, i ≠ ρ'.castSucc → M.val i ρ'.castSucc = 0 := by
      intro i hi
      have hi' : i.val ≠ a + k := fun e => hi ((hne i).mpr e)
      rcases Nat.lt_or_gt_of_ne hi' with h | h
      · exact hup i _ (by omega) (by rw [Fin.lt_def, hρv]; exact h)
      · rw [hM i (by omega) _]
        exact Matrix.one_apply_ne hi
    have hMt : Mt * κm = M.val := by
      ext i j
      rw [Matrix.mul_apply]
      by_cases hi : i = ρ'.castSucc
      · subst hi
        rw [Finset.sum_eq_single ρ'.castSucc]
        · simp [Mt, κm]
        · intro l _ hl
          simp [Mt, Matrix.one_apply_ne (Ne.symm hl)]
        · simp
      · have hterm : ∀ l, Mt i l * κm l j =
            M.val i l * (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) l j := by
          intro l
          simp only [Mt, κm, hi, ite_false]
          split_ifs with hl
          · subst hl
            rw [hcol i hi, zero_mul, zero_mul]
          · rfl
        simp_rw [hterm]
        rw [← Matrix.mul_apply, Matrix.mul_one]
    have hM'val : (M * κ⁻¹).val = Mt := by
      rw [Units.val_mul, ← hMt, Matrix.mul_assoc]
      change Mt * (κ.val * κ⁻¹.val) = Mt
      rw [Units.mul_inv, Matrix.mul_one]
    have hMt_apply : ∀ i j, (M * κ⁻¹).val i j =
        if i = ρ'.castSucc then (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j
        else M.val i j := by
      intro i j
      rw [hM'val]
    have hπM : π M w₀ = π (M * κ⁻¹) w₀ := by
      calc π M w₀ = π (M * κ⁻¹ * κ) w₀ := by rw [inv_mul_cancel_right]
        _ = π (M * κ⁻¹) w₀ := by rw [map_mul, Module.End.mul_apply, hκfix]
    have hM'1 : ∀ i : Fin (n + 1), a + k ≤ i.val → ∀ j,
        (M * κ⁻¹).val i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j := by
      intro i hi j
      rw [hMt_apply]
      by_cases h : i = ρ'.castSucc
      · rw [ite_eq_left h]
      · rw [ite_eq_right h]
        have := (hne i).not.mp h
        exact hM i (by omega) j
    have hM'2 : ∀ i j : Fin (n + 1), a ≤ j.val → i < j → (M * κ⁻¹).val i j = 0 := by
      intro i j hj hij
      rw [hMt_apply]
      by_cases h : i = ρ'.castSucc
      · rw [ite_eq_left h]
        exact Matrix.one_apply_ne hij.ne
      · rw [ite_eq_right h]
        exact hup i j hj hij
    have hM'3 : ∀ i j : Fin (n + 1), M₀.val i j = if i.val < a then (M * κ⁻¹).val i j else
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j := by
      intro i j
      rw [hM₀ i j, hMt_apply]
      by_cases h₁ : i.val < a
      · have h₂ : ¬ i = ρ'.castSucc := fun h => by
          rw [(hne i).mp h] at h₁
          omega
        rw [ite_eq_left h₁, ite_eq_left h₁, ite_eq_right h₂]
      · rw [ite_eq_right h₁, ite_eq_right h₁]
    rw [hπM, hw₀ (M * κ⁻¹) M₀ hM'1 hM'2 hM'3]
    have hiff : (∀ i j : Fin (n + 1), a ≤ i.val → i.val < a + k →
        (M * κ⁻¹).val i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j ∈
          T.additiveLattice (S (i.val - a))) ↔
        (∀ i j : Fin (n + 1), a ≤ i.val → i.val < a + (k + 1) →
          M.val i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j ∈
            T.additiveLattice (if i.val - a = k then min S₀ S₁ else S (i.val - a))) := by
      constructor
      · intro h₁ i j hi₁ hi₂
        by_cases hik : i.val = a + k
        · rw [ite_eq_left (show i.val - a = k by omega),
            show i = ρ'.castSucc from (hne i).mpr hik]
          exact hr j
        · rw [ite_eq_right (show ¬ (i.val - a = k) by omega)]
          have := h₁ i j hi₁ (by omega)
          rwa [hMt_apply, ite_eq_right (fun h => hik ((hne i).mp h))] at this
      · intro h₂ i j hi₁ hi₂
        have hik : i.val ≠ a + k := by omega
        rw [hMt_apply, ite_eq_right (fun h => hik ((hne i).mp h))]
        have := h₂ i j hi₁ (by omega)
        rwa [ite_eq_right (show ¬ (i.val - a = k) by omega)] at this
    by_cases hc : ∀ i j : Fin (n + 1), a ≤ i.val → i.val < a + k →
        (M * κ⁻¹).val i j - (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) i j ∈
          T.additiveLattice (S (i.val - a))
    · rw [ite_eq_left hc, ite_eq_left (hiff.mp hc)]
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hiff.mpr h))]


/-! ## The three coordinate blocks of the chart -/

section Chart

variable {a d c : ℕ}

theorem val_lowerBlockFirst (i : Fin a) : (lowerBlockFirst d c i).val = i.val := rfl

theorem val_lowerBlockMiddle (i : Fin d) : (lowerBlockMiddle a c i).val = a + i.val := rfl

theorem val_lowerBlockLast (i : Fin c) : (lowerBlockLast a d i).val = a + d + i.val := rfl

theorem fin_blocks_cases (i : Fin (a + d + c)) :
    (∃ i', i = lowerBlockFirst d c i') ∨ (∃ i', i = lowerBlockMiddle a c i') ∨
      ∃ i', i = lowerBlockLast a d i' := by
  have hi := i.isLt
  by_cases h₁ : i.val < a
  · exact Or.inl ⟨⟨i.val, h₁⟩, Fin.ext rfl⟩
  · by_cases h₂ : i.val < a + d
    · exact Or.inr (Or.inl ⟨⟨i.val - a, by omega⟩,
        Fin.ext (show i.val = a + (i.val - a) by omega)⟩)
    · exact Or.inr (Or.inr ⟨⟨i.val - (a + d), by omega⟩,
        Fin.ext (show i.val = a + d + (i.val - (a + d)) by omega)⟩)

theorem one_apply_ne_val {N : ℕ} {i j : Fin N} (h : i.val ≠ j.val) :
    (1 : Matrix (Fin N) (Fin N) F.Carrier) i j = 0 :=
  Matrix.one_apply_ne (fun e => h (congrArg Fin.val e))

theorem one_middle (i j : Fin d) :
    (1 : Matrix (Fin (a + d + c)) (Fin (a + d + c)) F.Carrier)
        (lowerBlockMiddle a c i) (lowerBlockMiddle a c j) =
      (1 : Matrix (Fin d) (Fin d) F.Carrier) i j := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne h, one_apply_ne_val]
    rw [val_lowerBlockMiddle, val_lowerBlockMiddle]
    exact fun e => h (Fin.ext (by omega))

theorem one_last (i j : Fin c) :
    (1 : Matrix (Fin (a + d + c)) (Fin (a + d + c)) F.Carrier)
        (lowerBlockLast a d i) (lowerBlockLast a d j) =
      (1 : Matrix (Fin c) (Fin c) F.Carrier) i j := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne h, one_apply_ne_val]
    rw [val_lowerBlockLast, val_lowerBlockLast]
    exact fun e => h (Fin.ext (by omega))

variable (g : Langlands.GeneralLinear a F.Carrier) (x : Matrix (Fin d) (Fin a) F.Carrier)
  (h : lowerTriangularSubgroup d F.Carrier)

/-- The rows of the final block of the chart are standard basis rows. -/
theorem chart_lastRows : ∀ i : Fin (a + d + c), a + d ≤ i.val → ∀ j,
    (lowerBlockLocalization c g x h).val i j =
      (1 : Matrix (Fin (a + d + c)) (Fin (a + d + c)) F.Carrier) i j := by
  intro i hi j
  rcases fin_blocks_cases i with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exfalso
    have := i.isLt
    rw [val_lowerBlockFirst] at hi
    omega
  · exfalso
    have := i.isLt
    rw [val_lowerBlockMiddle] at hi
    omega
  · rcases fin_blocks_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have := j.isLt
      rw [lowerBlockLocalization_31, one_apply_ne_val]
      rw [val_lowerBlockLast, val_lowerBlockFirst]
      omega
    · have := j.isLt
      rw [lowerBlockLocalization_32, one_apply_ne_val]
      rw [val_lowerBlockLast, val_lowerBlockMiddle]
      omega
    · rw [lowerBlockLocalization_33, one_last]

/-- The chart vanishes above the diagonal in the columns from `a` on. -/
theorem chart_upper : ∀ i j : Fin (a + d + c), a ≤ j.val → i < j →
    (lowerBlockLocalization c g x h).val i j = 0 := by
  intro i j hj hij
  rw [Fin.lt_def] at hij
  rcases fin_blocks_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exfalso
    have := j.isLt
    rw [val_lowerBlockFirst] at hj
    omega
  · rcases fin_blocks_cases i with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact lowerBlockLocalization_12 g x h i j
    · rw [lowerBlockLocalization_22]
      rw [val_lowerBlockMiddle, val_lowerBlockMiddle] at hij
      exact (mem_lowerTriangularSubgroup_iff _).mp h.property i j (Fin.lt_def.mpr (by omega))
    · exact lowerBlockLocalization_32 g x h i j
  · rcases fin_blocks_cases i with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact lowerBlockLocalization_13 g x h i j
    · exact lowerBlockLocalization_23 g x h i j
    · rw [lowerBlockLocalization_33]
      rw [val_lowerBlockLast, val_lowerBlockLast] at hij
      exact Matrix.one_apply_ne (fun e => by rw [e] at hij; omega)

/-- The diagonal specialization of the chart agrees with the chart in the first
`a` rows and is the identity in the other rows. -/
theorem chart_diag : ∀ i j : Fin (a + d + c),
    (lowerBlockLocalization c g 0 1).val i j =
      if i.val < a then (lowerBlockLocalization c g x h).val i j else
        (1 : Matrix (Fin (a + d + c)) (Fin (a + d + c)) F.Carrier) i j := by
  intro i j
  rcases fin_blocks_cases i with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [ite_eq_left (show (lowerBlockFirst d c i).val < a from i.isLt)]
    rcases fin_blocks_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [lowerBlockLocalization_11, lowerBlockLocalization_11]
    · rw [lowerBlockLocalization_12, lowerBlockLocalization_12]
    · rw [lowerBlockLocalization_13, lowerBlockLocalization_13]
  · have hi : ¬ (lowerBlockMiddle a c i).val < a := by
      rw [val_lowerBlockMiddle]
      omega
    rw [ite_eq_right hi]
    rcases fin_blocks_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have := j.isLt
      rw [lowerBlockLocalization_21, one_apply_ne_val]
      · rfl
      · rw [val_lowerBlockMiddle, val_lowerBlockFirst]
        omega
    · rw [lowerBlockLocalization_22, one_middle]
      rfl
    · have := j.isLt
      rw [lowerBlockLocalization_23, one_apply_ne_val]
      rw [val_lowerBlockMiddle, val_lowerBlockLast]
      omega
  · have hi : ¬ (lowerBlockLast a d i).val < a := by
      rw [val_lowerBlockLast]
      omega
    rw [ite_eq_right hi]
    exact chart_lastRows g 0 1 _ (by rw [val_lowerBlockLast]; omega) j

/-- The row-graded congruence in the middle rows of the chart is the conjunction
of the conditions on the rectangular block and on the lower triangular block. -/
theorem chart_cond (S : ℕ → ℤ) :
    (∀ i j : Fin (a + d + c), a ≤ i.val → i.val < a + d →
      (lowerBlockLocalization c g x h).val i j -
          (1 : Matrix (Fin (a + d + c)) (Fin (a + d + c)) F.Carrier) i j ∈
        T.additiveLattice (S (i.val - a))) ↔
      ((∀ i j, x i j ∈ T.additiveLattice (S i.val)) ∧
        ∀ i j, h.val.val i j - (1 : Matrix (Fin d) (Fin d) F.Carrier) i j ∈
          T.additiveLattice (S i.val)) := by
  have hS (i : Fin d) : S ((lowerBlockMiddle a c i).val - a) = S i.val := by
    rw [val_lowerBlockMiddle, Nat.add_sub_cancel_left]
  constructor
  · intro H
    constructor
    · intro i j
      have := H (lowerBlockMiddle a c i) (lowerBlockFirst d c j)
        (by rw [val_lowerBlockMiddle]; omega)
        (by have := i.isLt; rw [val_lowerBlockMiddle]; omega)
      have hj := j.isLt
      rwa [lowerBlockLocalization_21, one_apply_ne_val, sub_zero, hS] at this
      rw [val_lowerBlockMiddle, val_lowerBlockFirst]
      omega
    · intro i j
      have := H (lowerBlockMiddle a c i) (lowerBlockMiddle a c j)
        (by rw [val_lowerBlockMiddle]; omega)
        (by have := i.isLt; rw [val_lowerBlockMiddle]; omega)
      rwa [lowerBlockLocalization_22, one_middle, hS] at this
  · rintro ⟨hx, hh⟩ i j hi₁ hi₂
    rcases fin_blocks_cases i with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exfalso
      have := i.isLt
      rw [val_lowerBlockFirst] at hi₁
      omega
    · rw [hS]
      rcases fin_blocks_cases j with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
      · have := j.isLt
        rw [lowerBlockLocalization_21, one_apply_ne_val, sub_zero]
        · exact hx i j
        · rw [val_lowerBlockMiddle, val_lowerBlockFirst]
          omega
      · rw [lowerBlockLocalization_22, one_middle]
        exact hh i j
      · rw [lowerBlockLocalization_23, one_apply_ne_val, sub_zero]
        · exact zero_mem _
        · have := i.isLt
          rw [val_lowerBlockMiddle, val_lowerBlockLast]
          omega
    · exfalso
      rw [val_lowerBlockLast] at hi₂
      omega

end Chart

/-! ## Compact open subgroups of congruence boxes -/

/-- Row-graded congruence boxes are closed under multiplication. -/
theorem mul_rowBox {m : ℕ} (A B : Matrix (Fin m) (Fin m) F.Carrier) (R : Fin m → ℤ)
    (hR : ∀ i, R i ≤ -1)
    (hA : ∀ i j, A i j - (1 : Matrix (Fin m) (Fin m) F.Carrier) i j ∈ T.additiveLattice (R i))
    (hB : ∀ i j, B i j - (1 : Matrix (Fin m) (Fin m) F.Carrier) i j ∈ T.additiveLattice (R i)) :
    ∀ i j, (A * B) i j - (1 : Matrix (Fin m) (Fin m) F.Carrier) i j ∈
      T.additiveLattice (R i) := by
  intro i j
  have key : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
  have h1 := congrFun (congrFun key i) j
  rw [Matrix.sub_apply, Matrix.add_apply, Matrix.add_apply] at h1
  rw [h1, Matrix.mul_apply]
  refine add_mem (add_mem (AddSubgroup.sum_mem _ fun l _ => ?_) ?_) ?_
  · rw [Matrix.sub_apply, Matrix.sub_apply]
    exact lattice_le T (by linarith [hR l]) (lattice_mul T (hA i l) (hB l j))
  · rw [Matrix.sub_apply]
    exact hA i j
  · rw [Matrix.sub_apply]
    exact hB i j

theorem isOpen_entryBox {m : ℕ} (R : Fin m → ℤ) :
    letI := T.topology
    IsOpen {g : Langlands.GeneralLinear m F.Carrier |
      ∀ i j, g.val i j - (1 : Matrix (Fin m) (Fin m) F.Carrier) i j ∈ T.additiveLattice (R i)} := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (T.isOpen_additiveLattice _).preimage ((Units.continuous_val.matrix_elem i j).sub continuous_const)

theorem isCompact_rowBox {m : ℕ} (R : Fin m → ℤ) (hR : ∀ i, R i ≤ -1) :
    letI := T.topology
    IsCompact {g : Langlands.GeneralLinear m F.Carrier |
      g ∈ lowerTriangularSubgroup m F.Carrier ∧
        ∀ i j, g.val i j - (1 : Matrix (Fin m) (Fin m) F.Carrier) i j ∈
          T.additiveLattice (R i)} := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.fieldT2
  have hint (A : Matrix (Fin m) (Fin m) F.Carrier)
      (hA : ∀ i j, A i j - (1 : Matrix (Fin m) (Fin m) F.Carrier) i j ∈
        T.additiveLattice (R i)) (i j : Fin m) : A i j ∈ T.Integers := by
    rw [← T.mem_additiveLattice_zero]
    have := add_mem (T.additiveLattice_mono ((hR i).trans (by norm_num)) (hA i j))
      (one_apply_mem_lattice_zero T i j)
    rwa [sub_add_cancel] at this
  apply (Langlands.GeneralLinearGroup.isCompact_integralSubgroup (Fin m) T.Integers
    T.isCompact_integers).of_isClosed_subset
  · rw [Set.ofPred_and]
    apply IsClosed.inter
    · simp only [mem_lowerTriangularSubgroup_iff, Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j =>
        (T.isCompact_additiveLattice _).isClosed.preimage
          ((Units.continuous_val.matrix_elem i j).sub continuous_const)
  · rintro g ⟨hl, hb⟩
    rw [SetLike.mem_coe, Langlands.GeneralLinearGroup.mem_integralSubgroup]
    exact ⟨hint _ hb, hint _ (inv_rowBox T g hl R hR hb)⟩

end Langlands.Whittaker.LowerBlockLocalizationProof

namespace Langlands.Whittaker

open Topology HarmonicAnalysis RankinSelberg GeneralLinear LowerBlockLocalizationProof

universe uF uV

/-- JPSS section 9.2: arbitrarily small lower-block localization of an actual
Whittaker coefficient, with the new coefficient taken for the same functional. -/
theorem lowerBlockWhittakerLocalization : LowerBlockWhittakerLocalizationStatement.{uF, uV} := by
  intro p _ F ψ a d c₀ ha hd c V _ _ π hπW W hW Ux Uh hUx hUh
  let T := F.canonicalTopologicalData
  let τ : TopologicalSpace F.Carrier := T.topology
  have hτ : τ = T.topology := rfl
  obtain ⟨ℓ, hWℓ⟩ := hW
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hWℓ
  have hπ : IsSmooth π := hπW.1.1
  obtain ⟨Sx, hSx⟩ := exists_matrix_box T 0 hUx
  rw [Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hUh
  obtain ⟨U', hU', hU'sub⟩ := hUh
  obtain ⟨Sh, hSh⟩ := exists_unit_box T hU'
  have hS₀ : min (-1) (min Sx Sh) ≤ -1 := min_le_left _ _
  have hS₀x : min (-1) (min Sx Sh) ≤ Sx := (min_le_right _ _).trans (min_le_left _ _)
  have hS₀h : min (-1) (min Sx Sh) ≤ Sh := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨w, S, hS, hw⟩ := main_claim (τ := τ) T hτ ψ (n := a + d + c₀) π hπ ℓ v a d (by omega)
    (min (-1) (min Sx Sh)) hS₀ d le_rfl
  have hR : ∀ i : Fin d, S i.val ≤ -1 := fun i => (hS _).trans hS₀
  let Ω₁ : AddSubgroup (Matrix (Fin d) (Fin a) F.Carrier) :=
    { carrier := {x | ∀ (i : Fin d) (j : Fin a), x i j ∈ T.additiveLattice (S i.val)}
      add_mem' := fun {x y} hx hy (i : Fin d) (j : Fin a) =>
        show x i j + y i j ∈ T.additiveLattice (S i.val) from add_mem (hx i j) (hy i j)
      zero_mem' := fun _ _ => zero_mem _
      neg_mem' := fun {x} hx (i : Fin d) (j : Fin a) =>
        show -x i j ∈ T.additiveLattice (S i.val) from neg_mem (hx i j) }
  let Ω₂ : Subgroup (lowerTriangularSubgroup d F.Carrier) :=
    { carrier := {h | ∀ i j, h.val.val i j - (1 : Matrix (Fin d) (Fin d) F.Carrier) i j ∈
        T.additiveLattice (S i.val)}
      one_mem' := fun i j => by
        change (1 : Matrix (Fin d) (Fin d) F.Carrier) i j -
          (1 : Matrix (Fin d) (Fin d) F.Carrier) i j ∈ _
        rw [sub_self]
        exact zero_mem _
      mul_mem' := fun {h₁ h₂} hh₁ hh₂ =>
        mul_rowBox T h₁.val.val h₂.val.val (fun i => S i.val) hR hh₁ hh₂
      inv_mem' := fun {h} hh => inv_rowBox T h.val h.property (fun i => S i.val) hR hh }
  have hΩ₁ : (Ω₁ : Set (Matrix (Fin d) (Fin a) F.Carrier)) =
      Set.univ.pi (fun i : Fin d => Set.univ.pi
        (fun _ : Fin a => (T.additiveLattice (S i.val) : Set F.Carrier))) := by
    ext x
    exact ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
  have hΩ₂ : Subtype.val '' (Ω₂ : Set (lowerTriangularSubgroup d F.Carrier)) =
      {g : Langlands.GeneralLinear d F.Carrier | g ∈ lowerTriangularSubgroup d F.Carrier ∧
        ∀ i j, g.val i j - (1 : Matrix (Fin d) (Fin d) F.Carrier) i j ∈
          T.additiveLattice (S i.val)} := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨h.property, hh⟩
    · rintro ⟨hl, hb⟩
      exact ⟨⟨g, hl⟩, hb, rfl⟩
  let W₀ := (coefficientMap π ℓ).toLinearMap w
  refine ⟨Ω₁, Ω₂, ?_, ?_, ?_, ?_, ?_, ?_, W₀, ⟨ℓ, LinearMap.mem_range.mpr ⟨w, rfl⟩⟩,
    fun g x h => ?_⟩
  · rw [hΩ₁]
    exact isCompact_univ_pi fun i => isCompact_univ_pi fun _ => T.isCompact_additiveLattice _
  · rw [hΩ₁]
    exact isOpen_set_pi Set.finite_univ fun i _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => T.isOpen_additiveLattice _
  · intro x hx
    apply hSx x
    intro i j
    rw [Matrix.zero_apply, sub_zero]
    exact lattice_le T ((hS _).trans hS₀x) (hx i j)
  · rw [Subtype.isCompact_iff, hΩ₂]
    exact isCompact_rowBox T (fun i => S i.val) hR
  · exact (isOpen_entryBox T (fun i => S i.val)).preimage continuous_subtype_val
  · intro h hh
    apply hU'sub
    apply hSh h.val
    · intro i j
      exact lattice_le T ((hS _).trans hS₀h) (hh i j)
    · intro i j
      exact lattice_le T ((hS _).trans hS₀h)
        (inv_rowBox T h.val h.property (fun i => S i.val) hR hh i j)
  · have hval := hw (lowerBlockLocalization c g x h) (lowerBlockLocalization c g 0 1)
      (chart_lastRows (c := c) g x h) (chart_upper (c := c) g x h) (chart_diag (c := c) g x h)
    constructor
    · intro hxh
      have hc := (chart_cond (c := c) T g x h S).mpr hxh
      refine hval.trans ((ite_eq_left hc).trans ?_)
      rfl
    · intro hxh
      have hc : ¬ _ := fun h' => hxh ((chart_cond (c := c) T g x h S).mp h')
      exact hval.trans (ite_eq_right hc)

end Langlands.Whittaker
