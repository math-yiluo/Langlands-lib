import Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.HarmonicAnalysis.PadicLatticeTopology
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Additive self-duality of a p-adic field

For a supplied topological realization `T` of a p-adic field `F` and a continuous
nontrivial unitary additive character `ψ`, every locally constant complex additive
character `χ` of `F` has the form `x ↦ ψ(a x)` for some `a ∈ F`.

The proof is by finite levels. If `χ` is trivial on the lattice `L_k` and `n` is the
conductor of `ψ`, then for every `M ≥ k` the map `a ↦ ψ(a ·)` embeds
`L_(n-k) / L_(n-M)` into the character group of `L_M / L_k`. Both quotients have the same
cardinality, since multiplication by a power of the uniformizer carries one pair of lattices
onto the other, and a finite abelian group has as many complex characters as elements. So the
embedding is a bijection. The admissible parameters for the successive levels form a
decreasing sequence of nonempty closed subsets of the compact lattice `L_(n-k)`. Their
intersection is nonempty, and any point in it works on all of `F`.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.AdditiveSelfDuality

universe u

/-! ## Characters of quotient groups -/

/-- A character trivial on a subgroup descends to the quotient group. -/
def quotientAddChar {G : Type*} [AddCommGroup G] (K : AddSubgroup G) (φ : AddChar G ℂ)
    (hφ : ∀ x ∈ K, φ x = 1) : AddChar (G ⧸ K) ℂ where
  toFun q := Quotient.liftOn' q φ (fun a b hab => by
    have h := hφ _ (QuotientAddGroup.leftRel_apply.mp hab)
    calc φ a = φ a * φ (-a + b) := by rw [h, mul_one]
      _ = φ b := by rw [← AddChar.map_add_eq_mul, add_neg_cancel_left])
  map_zero_eq_one' := φ.map_zero_eq_one
  map_add_eq_mul' x y := by
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact φ.map_add_eq_mul a b

theorem quotientAddChar_mk {G : Type*} [AddCommGroup G] (K : AddSubgroup G)
    (φ : AddChar G ℂ) (hφ : ∀ x ∈ K, φ x = 1) (x : G) :
    quotientAddChar K φ hφ (x : G ⧸ K) = φ x := rfl

end Langlands.HarmonicAnalysis.AdditiveSelfDuality

namespace Langlands.PadicField.TopologicalData

open HarmonicAnalysis HarmonicAnalysis.AdditiveSelfDuality

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology

/-! ## Lattices -/

/-- Products of lattice elements lie in the lattice of the summed level. -/
theorem mul_mem_additiveLattice_add {i j : ℤ} {a x : F.Carrier}
    (ha : a ∈ T.additiveLattice i) (hx : x ∈ T.additiveLattice j) :
    a * x ∈ T.additiveLattice (i + j) := by
  rw [mem_additiveLattice] at ha hx ⊢
  rw [map_mul, WithZero.exp_add]
  exact mul_le_mul' ha hx

/-- Multiplication by a nonzero `c` carries `L_j` onto `L_(j - ord c)`. -/
theorem map_mulLeft_additiveLattice {c : F.Carrier} (hc : c ≠ 0) (j : ℤ) :
    (T.additiveLattice j).map (AddMonoidHom.mulLeft c) = T.additiveLattice (j - T.ord c) := by
  ext y
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [AddMonoidHom.coe_mulLeft, T.mul_mem_additiveLattice_iff hc, sub_add_cancel]
    exact hx
  · intro hy
    refine ⟨c⁻¹ * y, ?_, ?_⟩
    · have h := (T.mul_mem_additiveLattice_iff hc (j - T.ord c) (c⁻¹ * y)).mp
        (by rwa [← mul_assoc, mul_inv_cancel₀ hc, one_mul])
      rwa [sub_add_cancel] at h
    · rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-! ## The conductor -/

theorem complex_eq_one_of_mem_conductor (ψ : AdditiveCharacter) {y : F.Carrier}
    (hy : y ∈ T.additiveLattice (T.additiveConductor ψ)) :
    letI := T.topology
    ψ.complex y = 1 := by
  let _ := T.topology
  rw [UnitaryAdditiveCharacter.complex_apply, (T.additiveConductor_spec ψ).1 y hy,
    Circle.coe_one]

/-- If `x ↦ ψ(a x)` is trivial on `L_m`, then `a ∈ L_(n(ψ) - m)`. -/
theorem mem_additiveLattice_of_forall_complex_mul_eq_one (ψ : AdditiveCharacter)
    (m : ℤ) (a : F.Carrier)
    (h : letI := T.topology; ∀ x ∈ T.additiveLattice m, ψ.complex (a * x) = 1) :
    a ∈ T.additiveLattice (T.additiveConductor ψ - m) := by
  let _ := T.topology
  have hπ : T.uniformizer ^ (-m) ≠ 0 := by
    apply zpow_ne_zero
    apply T.discreteValuation.ne_zero_iff.mp
    rw [T.discreteValuation_uniformizer]
    exact WithZero.exp_ne_zero
  have hlevel : T.additiveConductor ψ - m =
      T.additiveConductor ψ + T.ord (T.uniformizer ^ (-m)) := by
    rw [T.ord_zpow, T.ord_uniformizer, mul_one, sub_eq_add_neg]
  rw [hlevel]
  apply (T.mul_mem_additiveLattice_iff hπ _ a).mp
  apply (T.integer_annihilator_iff_mem_additiveLattice ψ _).mp
  intro t
  have ht : T.uniformizer ^ (-m) * (t : F.Carrier) ∈ T.additiveLattice m :=
    (T.mem_additiveLattice_iff_exists_integer m _).mpr ⟨t, rfl⟩
  have hprod : (t : F.Carrier) * (T.uniformizer ^ (-m) * a) =
      a * (T.uniformizer ^ (-m) * (t : F.Carrier)) := by ring
  rw [hprod]
  have h1 := h _ ht
  rw [UnitaryAdditiveCharacter.complex_apply] at h1
  exact Circle.coe_eq_one.mp h1

/-! ## Finite levels -/

/-- If `χ` is trivial on `L_k`, then on every lattice `L_M` it agrees with some
`x ↦ ψ(a x)`. -/
theorem exists_eq_complex_mul_on_additiveLattice (ψ : AdditiveCharacter)
    (χ : AddChar F.Carrier ℂ) (k M : ℤ)
    (hχ : ∀ x ∈ T.additiveLattice k, χ x = 1) :
    letI := T.topology
    ∃ a : F.Carrier, ∀ x ∈ T.additiveLattice M, χ x = ψ.complex (a * x) := by
  let _ := T.topology
  have : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    have := T.localField
    infer_instance
  set n := T.additiveConductor ψ with hn
  -- The finite groups `B = L_M / L_k` and `A = L_(n-k) / L_(n-M)`.
  let G := T.additiveLattice M
  let K := (T.additiveLattice k).addSubgroupOf G
  let G' := T.additiveLattice (n - k)
  let K' := (T.additiveLattice (n - M)).addSubgroupOf G'
  have hopen : ∀ (i j : ℤ), IsOpen (((T.additiveLattice i).addSubgroupOf
      (T.additiveLattice j)) : Set (T.additiveLattice j)) := by
    intro i j
    rw [AddSubgroup.coe_addSubgroupOf]
    exact (T.isOpen_additiveLattice i).preimage continuous_subtype_val
  have hcompact : ∀ j : ℤ, CompactSpace (T.additiveLattice j) :=
    fun j => isCompact_iff_compactSpace.mp (T.isCompact_additiveLattice j)
  let _ : Fintype (G ⧸ K) := @Fintype.ofFinite _ (by
    have := hcompact M
    exact AddSubgroup.quotient_finite_of_isOpen K (hopen k M))
  let _ : Fintype (G' ⧸ K') := @Fintype.ofFinite _ (by
    have := hcompact (n - k)
    exact AddSubgroup.quotient_finite_of_isOpen K' (hopen (n - M) (n - k)))
  -- The characters `x ↦ ψ(a x)` of `L_M` for `a ∈ L_(n-k)` descend to `B`.
  let φ : G' → AddChar G ℂ := fun a => (ψ.complex.mulShift a.val).compAddMonoidHom G.subtype
  have hφ : ∀ (a : G') (x : G), φ a x = ψ.complex (a.val * x.val) := fun a x => rfl
  have hφK : ∀ (a : G') (x : G), x ∈ K → φ a x = 1 := by
    intro a x hx
    rw [hφ]
    apply T.complex_eq_one_of_mem_conductor ψ
    have h := T.mul_mem_additiveLattice_add a.property (AddSubgroup.mem_addSubgroupOf.mp hx)
    rwa [sub_add_cancel] at h
  let Φ₀ : G' → AddChar (G ⧸ K) ℂ := fun a => quotientAddChar K (φ a) (hφK a)
  have hΦ₀ : ∀ (a : G') (x : G), Φ₀ a (x : G ⧸ K) = ψ.complex (a.val * x.val) :=
    fun a x => rfl
  have hΦ₀K : ∀ a b : G', -a + b ∈ K' → Φ₀ a = Φ₀ b := by
    intro a b hab
    ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [hΦ₀, hΦ₀]
    have hd : (b.val - a.val) * x.val ∈ T.additiveLattice n := by
      have hm : b.val - a.val ∈ T.additiveLattice (n - M) := by
        have := AddSubgroup.mem_addSubgroupOf.mp hab
        simpa [sub_eq_neg_add] using this
      have h := T.mul_mem_additiveLattice_add hm x.property
      rwa [sub_add_cancel] at h
    have hb : b.val * x.val = a.val * x.val + (b.val - a.val) * x.val := by ring
    rw [hb, AddChar.map_add_eq_mul, T.complex_eq_one_of_mem_conductor ψ hd, mul_one]
  let Φ : G' ⧸ K' → AddChar (G ⧸ K) ℂ := fun q =>
    Quotient.liftOn' q Φ₀ (fun a b h => hΦ₀K a b (QuotientAddGroup.leftRel_apply.mp h))
  have hΦ : ∀ a : G', Φ (a : G' ⧸ K') = Φ₀ a := fun a => rfl
  have hinj : Function.Injective Φ := by
    intro q q' hqq'
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective q'
    rw [hΦ, hΦ] at hqq'
    apply (QuotientAddGroup.eq).mpr
    rw [AddSubgroup.mem_addSubgroupOf]
    have hann : ∀ x ∈ T.additiveLattice M, ψ.complex ((b.val - a.val) * x) = 1 := by
      intro x hx
      have h := congrArg (fun c : AddChar (G ⧸ K) ℂ => c ((⟨x, hx⟩ : G) : G ⧸ K)) hqq'
      simp only [hΦ₀] at h
      have hb : b.val * x = a.val * x + (b.val - a.val) * x := by ring
      have h2 := congrArg (fun z => ψ.complex (-(a.val * x)) * z) h
      rw [hb, AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul,
        neg_add_cancel, AddChar.map_zero_eq_one, one_mul] at h2
      exact h2.symm
    have hmem := T.mem_additiveLattice_of_forall_complex_mul_eq_one ψ M _ hann
    simpa [sub_eq_neg_add] using hmem
  -- Both quotients have the same cardinality.
  have hcard : Nat.card (G' ⧸ K') = Nat.card (G ⧸ K) := by
    have hπ : T.uniformizer ^ (M + k - n) ≠ 0 := by
      apply zpow_ne_zero
      apply T.discreteValuation.ne_zero_iff.mp
      rw [T.discreteValuation_uniformizer]
      exact WithZero.exp_ne_zero
    have hord : T.ord (T.uniformizer ^ (M + k - n)) = M + k - n := by
      rw [T.ord_zpow, T.ord_uniformizer, mul_one]
    have hinjm : Function.Injective (AddMonoidHom.mulLeft (T.uniformizer ^ (M + k - n))) :=
      mul_right_injective₀ hπ
    have h := AddSubgroup.relIndex_map_map_of_injective (T.additiveLattice k)
      (T.additiveLattice M) hinjm
    rw [T.map_mulLeft_additiveLattice hπ, T.map_mulLeft_additiveLattice hπ, hord] at h
    have h1 : k - (M + k - n) = n - M := by ring
    have h2 : M - (M + k - n) = n - k := by ring
    rw [h1, h2] at h
    exact h
  have hbij : Function.Bijective Φ := by
    rw [Fintype.bijective_iff_injective_and_card, AddChar.card_eq]
    refine ⟨hinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard
  -- `χ` restricted to `L_M` descends to `B` and lies in the image.
  let χB : AddChar (G ⧸ K) ℂ := quotientAddChar K (χ.compAddMonoidHom G.subtype)
    (fun x hx => hχ _ (AddSubgroup.mem_addSubgroupOf.mp hx))
  obtain ⟨q, hq⟩ := hbij.2 χB
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
  refine ⟨a.val, fun x hx => ?_⟩
  have h := congrArg (fun c : AddChar (G ⧸ K) ℂ => c ((⟨x, hx⟩ : G) : G ⧸ K)) hq
  exact h.symm

/-! ## Self-duality -/

/-- Every locally constant complex additive character of `F` is `x ↦ ψ(a x)` for some
`a ∈ F`, for every continuous nontrivial unitary additive character `ψ`. -/
theorem exists_eq_complex_mul_of_isLocallyConstant (ψ : AdditiveCharacter)
    (χ : AddChar F.Carrier ℂ) (hχ : @IsLocallyConstant F.Carrier ℂ T.topology χ) :
    letI := T.topology
    ∃ a : F.Carrier, ∀ x, χ x = ψ.complex (a * x) := by
  let _ := T.topology
  have : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    have := T.localField
    infer_instance
  obtain ⟨k, hk⟩ := T.exists_additiveLattice_subset
    ((hχ.isOpen_fiber 1).mem_nhds (by simp : χ 0 = 1))
  have hχk : ∀ x ∈ T.additiveLattice k, χ x = 1 := fun x hx => hk hx
  let S : ℕ → Set F.Carrier := fun j =>
    {a | ∀ x ∈ T.additiveLattice (k + j), χ x = ψ.complex (a * x)}
  have htd : ∀ j, S (j + 1) ⊆ S j := by
    intro j a ha x hx
    exact ha x (T.additiveLattice_mono (by push_cast; omega) hx)
  have htn : ∀ j, (S j).Nonempty := by
    intro j
    obtain ⟨a, ha⟩ := T.exists_eq_complex_mul_on_additiveLattice ψ χ k (k + j) hχk
    exact ⟨a, ha⟩
  have htcl : ∀ j, IsClosed (S j) := by
    intro j
    have hS : S j = ⋂ x, ⋂ (_ : x ∈ T.additiveLattice (k + j)),
        {a : F.Carrier | χ x = ψ.complex (a * x)} := by
      ext a
      simp [S]
    rw [hS]
    exact isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_eq continuous_const
        (ψ.continuous_complex.comp (continuous_id.mul continuous_const))
  have ht0 : IsCompact (S 0) := by
    apply (T.isCompact_additiveLattice (T.additiveConductor ψ - k)).of_isClosed_subset
      (htcl 0)
    intro a ha
    apply T.mem_additiveLattice_of_forall_complex_mul_eq_one ψ k a
    intro x hx
    have h := ha x (by simpa using hx)
    rw [← h, hχk x hx]
  obtain ⟨a, ha⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S htd htn ht0 htcl
  rw [Set.mem_iInter] at ha
  refine ⟨a, fun x => ?_⟩
  let j : ℕ := (WithZero.log (T.discreteValuation x) - k).toNat
  have hx : x ∈ T.additiveLattice (k + j) := by
    rw [mem_additiveLattice]
    apply WithZero.le_exp_of_log_le
    have := Int.self_le_toNat (WithZero.log (T.discreteValuation x) - k)
    omega
  exact ha j x hx

end Langlands.PadicField.TopologicalData

namespace Langlands.HarmonicAnalysis

universe u

/-- Additive self-duality for every supplied p-adic topology: every locally constant complex
additive character is `x ↦ ψ(a x)` for some `a`. -/
theorem padicAdditiveSelfDuality (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData) :
    letI := T.topology
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (χ : AddChar F.Carrier ℂ),
      IsLocallyConstant χ → ∃ a : F.Carrier, ∀ x, χ x = ψ.complex (a * x) := by
  let _ := T.topology
  intro ψ χ hχ
  exact T.exists_eq_complex_mul_of_isLocallyConstant ψ χ hχ

end Langlands.HarmonicAnalysis
