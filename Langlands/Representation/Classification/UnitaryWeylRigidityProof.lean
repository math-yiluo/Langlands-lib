import Langlands.Representation.Classification.UnitaryWeylRigidityStatement
import Langlands.Representation.CuspidalSupport.BlockPermutation
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.LocalField.Normalization.Proof

/-!
# Proof of real determinant exponent rigidity under unitary Weyl association

Block scalar central elements isolate each weighted determinant exponent; the
unit modulus of their scalar actions is derived from the invariant forms.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric

universe uF uV uW uG

namespace UnitaryWeylRigidity

section Geometry

variable {n : ℕ}

/-- The coordinates of a block are counted by its size. -/
theorem card_blockFiber (B : BlockShape n) (i : Fin B.length) :
    Fintype.card {a : Fin n // blockIndex B a = i} = B.size i := by
  have e : Fin (B.size i) ≃ {a : Fin n // blockIndex B a = i} :=
    Equiv.ofBijective (fun x => ⟨B.index i x, blockIndex_index B i x⟩)
      ⟨fun x y h => (B.index i).injective (congrArg Subtype.val h), fun ⟨a, ha⟩ => by
        obtain ⟨b, hb⟩ := exists_index_of_blockIndex_eq B ha
        exact ⟨b, Subtype.ext hb⟩⟩
  exact (Fintype.card_congr e.symm).trans (Fintype.card_fin _)

/-- A permutation preserving the block relations in both directions carries
each source block bijectively onto its target block. -/
theorem size_eq_of_blockIndex_iff {B C : BlockShape n} {w : Equiv.Perm (Fin n)}
    (h : ∀ a b, blockIndex C (w a) = blockIndex C (w b) ↔
      blockIndex B a = blockIndex B b) (a : Fin n) :
    C.size (blockIndex C (w a)) = B.size (blockIndex B a) := by
  rw [← card_blockFiber C, ← card_blockFiber B]
  exact (Fintype.card_congr (w.subtypeEquiv fun x => (h x a).symm)).symm

variable {F : Type uF} [Field F]

/-- Actual Levi conjugation preserves the coordinate block relations. -/
theorem blockIndex_iff_of_conjugatesLevi {B C : BlockShape n} {w : Equiv.Perm (Fin n)}
    (hw : CuspidalSupport.ConjugatesLevi (F := F) B C w) (a b : Fin n) :
    blockIndex C (w a) = blockIndex C (w b) ↔ blockIndex B a = blockIndex B b :=
  ⟨CuspidalSupport.blockIndex_eq_of_conjugatesLevi_apply hw,
    CuspidalSupport.blockIndex_eq_of_conjugatesLevi hw⟩

/-- Actual Levi conjugation carries a block scalar to the block scalar with
the transported entries. -/
theorem leviConjugation_blockScalarLevi {B C : BlockShape n} {w : Equiv.Perm (Fin n)}
    (hw : CuspidalSupport.ConjugatesLevi (F := F) B C w)
    (a : Fin B.length → Fˣ) (a' : Fin C.length → Fˣ)
    (ha : ∀ x, a' (blockIndex C (w x)) = a (blockIndex B x)) :
    CuspidalSupport.leviConjugation B C w hw (B.blockScalarLevi F a) =
      C.blockScalarLevi F a' := by
  apply C.leviEmbedding_injective F
  rw [CuspidalSupport.leviConjugation_embedding]
  change permutation n F w * B.blockScalar F a * (permutation n F w)⁻¹ =
    C.blockScalar F a'
  apply Matrix.GeneralLinearGroup.ext
  intro x y
  rw [permutation_conjugate_entry, BlockShape.coe_blockScalar, BlockShape.coe_blockScalar]
  by_cases hxy : x = y
  · subst hxy
    have h := ha (w⁻¹ x)
    rw [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at h
    simp only [Matrix.diagonal_apply_eq]
    exact congrArg Units.val h.symm
  · rw [Matrix.diagonal_apply_ne _ hxy,
      Matrix.diagonal_apply_ne _ ((w⁻¹).injective.ne hxy)]

/-- The flattened block of a coordinate lies in the coarse block of that coordinate. -/
theorem flattenBlockEquiv_symm_blockIndex (B : BlockShape n)
    (S : BlockRefinement B) (x : Fin n) :
    ((B.flattenBlockEquiv S).symm (blockIndex (B.flatten S) x)).1 = blockIndex B x := by
  obtain ⟨⟨k, c⟩, rfl⟩ := (B.flatten S).indexEquiv.surjective x
  change ((B.flattenBlockEquiv S).symm (blockIndex (B.flatten S)
      ((B.flatten S).index k c))).1 = blockIndex B ((B.flatten S).index k c)
  rw [blockIndex_index, BlockShape.flatten_index, blockIndex_index]

end Geometry

section Unitary

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- An element acting by a scalar in a unitarizable representation acts by a
scalar of modulus one. The invariant form is obtained from `IsUnitarizable`. -/
theorem norm_eq_one_of_isUnitarizable {ρ : Representation ℂ G V} (hu : IsUnitarizable ρ)
    {g : G} {c : ℂ} (hc : ∀ v, ρ g v = c • v) {v : V} (hv : v ≠ 0) : ‖c‖ = 1 := by
  obtain ⟨b⟩ := hu
  have hinv := b.invariant g v v
  rw [hc] at hinv
  have hr : ∀ (x y : V) (r : ℂ), b.inner x (r • y) = r * b.inner x y := by
    intro x y r
    rw [← b.conj_inner_symm, b.smul_left, map_mul, Complex.conj_conj, b.conj_inner_symm]
  rw [b.smul_left, hr, ← mul_assoc] at hinv
  have hne : b.inner v v ≠ 0 := fun h => hv (b.definite v h)
  have h1 : (starRingEnd ℂ) c * c = 1 := by
    simpa [hne] using hinv
  have h2 : (Complex.normSq c : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self, h1]
  have h3 : ‖c‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact_mod_cast h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).mp h3

variable [TopologicalSpace G]

/-- Schur's lemma for an irreducible admissible representation and the
invariant form give a unit-modulus scalar action of every central element. -/
theorem exists_norm_one_scalar (ρ : Representation ℂ G V)
    (hi : ρ.IsIrreducible) (ha : IsAdmissible ρ) (hu : IsUnitarizable ρ)
    (z : G) (hz : ∀ g, z * g = g * z) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v := by
  let f : ρ.IntertwiningMap ρ :=
    { toLinearMap := ρ z
      isIntertwining' := fun g => by
        change ρ z * ρ g = ρ g * ρ z
        rw [← map_mul, ← map_mul, hz g] }
  obtain ⟨c, hc, -⟩ := admissibleSchur_scalarEndomorphism ρ ha hi f
  have act : ∀ v, ρ z v = c • v := fun v =>
    congrArg (fun f : ρ.IntertwiningMap ρ => f v) hc
  have := hi
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact ⟨c, norm_eq_one_of_isUnitarizable hu act hv, act⟩

end Unitary

section Rigidity

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- On a block scalar supported on one block, the real determinant character
is the weighted real power of the normalized absolute value. -/
theorem coe_leviRealPowerCharacter_mulSingle {n : ℕ} (B : BlockShape n)
    (t : Fin B.length → ℝ) (i : Fin B.length) (u : F.Carrierˣ) :
    (T.leviRealPowerCharacter B t (B.blockScalarLevi F.Carrier (Pi.mulSingle i u)) : ℂ) =
      ((T.normalizedAbs (u : F.Carrier) ^ ((B.size i : ℝ) * t i) : ℝ) : ℂ) := by
  rw [T.coe_leviRealPowerCharacter_blockScalar B]
  rw [Fintype.prod_eq_single i]
  · simp
  · intro k hk
    simp [Pi.mulSingle_eq_of_ne hk, T.normalizedAbs_one]

/-- The normalized absolute value of the chosen uniformizer is a positive real
number different from one. -/
theorem normalizedAbs_uniformizer_pos_ne_one :
    0 < T.normalizedAbs T.uniformizer ∧ T.normalizedAbs T.uniformizer ≠ 1 := by
  rw [T.normalizedAbs_uniformizer, zpow_neg_one]
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  refine ⟨inv_pos.mpr (by linarith), ?_⟩
  intro h
  have := inv_eq_one.mp h
  linarith

/-- The chosen uniformizer is nonzero, so it defines a unit. -/
theorem uniformizer_ne_zero : T.uniformizer ≠ 0 := by
  intro h
  have h0 := (normalizedAbs_uniformizer_pos_ne_one T).1
  rw [h, T.normalizedAbs_zero] at h0
  exact lt_irrefl 0 h0

variable [TopologicalSpace F.Carrier]

/-- Coordinate rigidity for an actual Weyl association of real determinant
twists of irreducible admissible unitarizable representations. -/
theorem coordinate_exponent_eq {n : ℕ} {B C : BlockShape n}
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ω : Representation ℂ (B.Levi F.Carrier) V}
    {η : Representation ℂ (C.Levi F.Carrier) W}
    (hωi : ω.IsIrreducible) (hωa : IsAdmissible ω) (hωu : IsUnitarizable ω)
    (hηi : η.IsIrreducible) (hηa : IsAdmissible η) (hηu : IsUnitarizable η)
    {s : Fin B.length → ℝ} {t : Fin C.length → ℝ} {w : Equiv.Perm (Fin n)}
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) B C w)
    (e : (CuspidalSupport.transport B C w hw (T.leviRealPowerTwist B s ω)).Equiv
      (T.leviRealPowerTwist C t η)) (a : Fin n) :
    t (blockIndex C (w a)) = s (blockIndex B a) := by
  classical
  have hiff := blockIndex_iff_of_conjugatesLevi hw
  have hsize := size_eq_of_blockIndex_iff hiff a
  set i := blockIndex B a with hi
  set j := blockIndex C (w a) with hj
  let ϖ : F.Carrierˣ := Units.mk0 T.uniformizer (uniformizer_ne_zero T)
  let α : Fin B.length → F.Carrierˣ := Pi.mulSingle i ϖ
  let α' : Fin C.length → F.Carrierˣ := Pi.mulSingle j ϖ
  have hα : ∀ x, α' (blockIndex C (w x)) = α (blockIndex B x) := by
    intro x
    by_cases hx : blockIndex B x = i
    · have hx' : blockIndex C (w x) = j := (hiff x a).mpr hx
      simp only [α, α', hx, hx', Pi.mulSingle_eq_same]
    · have hx' : blockIndex C (w x) ≠ j := fun h => hx ((hiff x a).mp h)
      simp only [α, α', Pi.mulSingle_eq_of_ne hx, Pi.mulSingle_eq_of_ne hx']
  have hconj := leviConjugation_blockScalarLevi hw α α' hα
  obtain ⟨cω, hcω, hωz⟩ := exists_norm_one_scalar ω hωi hωa hωu
    (B.blockScalarLevi F.Carrier α) (B.blockScalarLevi_commute F.Carrier α)
  obtain ⟨cη, hcη, hηz⟩ := exists_norm_one_scalar η hηi hηa hηu
    (C.blockScalarLevi F.Carrier α') (C.blockScalarLevi_commute F.Carrier α')
  have := hωi
  have : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (B.Levi F.Carrier)) ω.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hev : e v ≠ 0 := by
    intro h
    apply hv
    apply e.toLinearEquiv.injective
    exact h.trans (map_zero e.toLinearEquiv).symm
  have hsymm : (CuspidalSupport.leviConjugation B C w hw).symm
      (C.blockScalarLevi F.Carrier α') = B.blockScalarLevi F.Carrier α := by
    rw [← hconj, MulEquiv.symm_apply_apply]
  have key := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap
    (C.blockScalarLevi F.Carrier α') v
  change e ((T.leviRealPowerTwist B s ω)
      ((CuspidalSupport.leviConjugation B C w hw).symm
        (C.blockScalarLevi F.Carrier α')) v) =
    (T.leviRealPowerTwist C t η) (C.blockScalarLevi F.Carrier α') (e v) at key
  rw [hsymm, T.leviRealPowerTwist_apply, T.leviRealPowerTwist_apply, hωz, hηz,
    smul_smul, smul_smul, map_smul] at key
  have hc := smul_left_injective ℂ hev key
  have hn := congrArg norm hc
  simp only [norm_mul, hcω, hcη, mul_one, α, α', coe_leviRealPowerCharacter_mulSingle, ϖ,
    Units.val_mk0] at hn
  obtain ⟨hpos, hne⟩ := normalizedAbs_uniformizer_pos_ne_one T
  rw [Complex.norm_of_nonneg (Real.rpow_nonneg hpos.le _),
    Complex.norm_of_nonneg (Real.rpow_nonneg hpos.le _)] at hn
  have hexp := (Real.rpow_right_inj hpos hne).mp hn
  rw [hsize] at hexp
  have hB : (B.size i : ℝ) ≠ 0 := by exact_mod_cast (B.positive i).ne'
  exact (mul_left_cancel₀ hB hexp).symm

end Rigidity

end UnitaryWeylRigidity

/-- The complete real determinant exponent rigidity statement, at independent
field and carrier universes. -/
theorem glUnitaryWeylRealExponentRigidity :
    GLUnitaryWeylRealExponentRigidityStatement.{uF, uV, uW} := by
  intro p _ F T
  let := T.topology
  intro n _ B
  refine ⟨?_, ?_, ?_⟩
  · intro C w hw
    have hiff := UnitaryWeylRigidity.blockIndex_iff_of_conjugatesLevi hw
    exact ⟨hiff, UnitaryWeylRigidity.size_eq_of_blockIndex_iff hiff⟩
  · intro C V W _ _ _ _ ω η hωi hωa hωu hηi hηa hηu s t w hw ⟨e⟩ a
    exact UnitaryWeylRigidity.coordinate_exponent_eq T hωi hωa hωu hηi hηa hηu hw e a
  · intro S V _ _ ω hωi hωa hωu v₀ t hgen C e w hw ⟨eq⟩
    refine hgen.2 w (UnitaryWeylRigidity.blockIndex_iff_of_conjugatesLevi hw) ?_
    intro a
    have h := UnitaryWeylRigidity.coordinate_exponent_eq T hωi hωa hωu hωi hωa hωu hw eq a
    simp only [C, e, UnitaryWeylRigidity.flattenBlockEquiv_symm_blockIndex] at h
    linarith

end Langlands
