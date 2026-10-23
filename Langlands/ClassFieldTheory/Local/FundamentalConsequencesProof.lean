import Langlands.ClassFieldTheory.Local.ClassFormationStatement
import Langlands.ClassFieldTheory.Local.UnramifiedInvariant
import Langlands.ClassFieldTheory.Local.RelativeH2CorestrictionRestrictionProof

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v

private theorem reciprocalClass_mem (n : ℕ) (hn : 0 < n) :
    reciprocalClass n ∈ denominatorSubgroup n := by
  rw [← denominatorEquiv_one n hn]
  exact (denominatorEquiv n hn 1).property

private theorem reciprocalClass_addOrderOf (n : ℕ) (hn : 0 < n) :
    addOrderOf (reciprocalClass n) = n := by
  rw [← denominatorEquiv_one n hn]
  exact (addOrderOf_injective (denominatorSubgroup n).subtype Subtype.val_injective
    (denominatorEquiv n hn 1)).trans
      (((denominatorEquiv n hn).addOrderOf_eq 1).trans (ZMod.addOrderOf_one n))

private theorem denominatorSubgroup_mem_zmultiples (n : ℕ) (hn : 0 < n)
    (x : denominatorSubgroup n) :
    ∃ k : ℤ, k • reciprocalClass n = x.val := by
  let e := denominatorEquiv n hn
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (e.symm x)
  refine ⟨k, ?_⟩
  have hk' : k • (1 : ZMod n) = e.symm x := by
    simpa only [zsmul_eq_mul, mul_one] using hk
  have he := congrArg (fun z : ZMod n => (e z : RationalModIntegers)) hk'
  simpa only [map_zsmul, AddSubgroup.coe_zsmul, e, denominatorEquiv_one,
    AddEquiv.apply_symm_apply] using he

private theorem fundamentalProperties_of_invariantImage
    (K : Type v) (L : Type u) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    (inv : relativeCohomology K L 2 →+ RationalModIntegers)
    (hinj : Function.Injective inv)
    (hrange : inv.range = denominatorSubgroup (Module.finrank K L)) :
    HasUniqueFundamentalClass K L inv ∧ FundamentalClassGenerates K L inv := by
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  constructor
  · have hmem : reciprocalClass (Module.finrank K L) ∈ inv.range := by
      rw [hrange]
      exact reciprocalClass_mem _ hpos
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, hc, ?_⟩
    intro d hd
    exact hinj (hd.trans hc.symm)
  · intro c hc
    change inv c = reciprocalClass (Module.finrank K L) at hc
    constructor
    · rw [← addOrderOf_injective inv hinj c, hc]
      exact reciprocalClass_addOrderOf _ hpos
    · apply top_unique
      intro x _
      have hx : inv x ∈ denominatorSubgroup (Module.finrank K L) := by
        rw [← hrange]
        exact ⟨x, rfl⟩
      obtain ⟨k, hk⟩ := denominatorSubgroup_mem_zmultiples _ hpos ⟨inv x, hx⟩
      apply AddSubgroup.mem_zmultiples_iff.mpr
      refine ⟨k, hinj ?_⟩
      simpa only [map_zsmul, hc] using hk

private theorem reciprocalClass_mul_left (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    a • reciprocalClass (a * b) = reciprocalClass b := by
  unfold reciprocalClass
  rw [← map_nsmul]
  congr 1
  rw [nsmul_eq_mul, Nat.cast_mul]
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  field_simp

namespace InvariantFamily

variable {p : ℕ} [Fact p.Prime]

/-- Injectivity and the exact invariant image give all fundamental-class properties. -/
theorem fundamentalClasses_of_relativeImages (I : InvariantFamily.{u,u} p)
    (hI : I.RelativeImages) : I.FundamentalClasses := by
  intro F L _ _ _ _
  exact fundamentalProperties_of_invariantImage F.Carrier L (I.relative F L)
    (hI F L).1 (hI F L).2

/-- The inflation invariant formula gives the degree-scaled fundamental-class formula. -/
theorem fundamentalInflation_of_relativeClassFormation (I : InvariantFamily.{u,u} p)
    (hI : I.RelativeClassFormation) : I.FundamentalInflation := by
  intro F L M _ _ _ _ _ _ _ _ _ _ _ c d hc hd
  apply (hI.2.1 F M).1
  rw [hI.2.2.1 F L M c, map_nsmul]
  change I.relative F L c = Module.finrank L M • I.relative F M d
  rw [hc, hd, ← Module.finrank_mul_finrank F.Carrier L M, Nat.mul_comm]
  exact (reciprocalClass_mul_left _ _ Module.finrank_pos Module.finrank_pos).symm

/-- The restriction invariant formula preserves the fundamental class. -/
theorem fundamentalRestriction_of_relativeClassFormation (I : InvariantFamily.{u,u} p)
    (hI : I.RelativeClassFormation) : I.FundamentalRestriction := by
  intro F E M _ _ _ _ _ _ _ _ _ _ _ c d hc hd
  apply (hI.2.1 E M).1
  rw [hI.2.2.2 F E M c]
  change Module.finrank F.Carrier E.Carrier • I.relative F M c = I.relative E M d
  rw [hc, hd, ← Module.finrank_mul_finrank F.Carrier E.Carrier M]
  exact reciprocalClass_mul_left _ _ Module.finrank_pos Module.finrank_pos

/-- The actual cor-res identity and the fundamental restriction formula give
the fundamental corestriction formula. -/
theorem fundamentalCorestriction_of_relativeClassFormation
    (I : InvariantFamily.{u,u} p) (hI : I.RelativeClassFormation) :
    I.FundamentalCorestriction := by
  intro F E M _ _ _ _ _ _ _ _ _ _ _ c d hc hd
  have hres := fundamentalRestriction_of_relativeClassFormation I hI F E M d c hd hc
  rw [← hres]
  exact relativeH2CorestrictionRestriction F.Carrier E.Carrier M d

/-- Conjugacy compatibility and the conjugate Galois-group equivalence preserve the class. -/
theorem fundamentalConjugacy_of_relativeImages (I : InvariantFamily.{u,u} p)
    (hI : I.RelativeImages) (hconj : I.RelativeConjugacy) : I.FundamentalConjugacy := by
  intro F E L M _ _ _ _ _ _ _ _ eF eL h c d hc hd
  apply (hI E M).1
  rw [hconj F E L M eF eL h c]
  change I.relative F L c = I.relative E M d
  rw [hc, hd]
  congr 1
  rw [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank]
  exact Nat.card_congr (galoisConjugacy eF.toRingEquiv eL h).toEquiv

end InvariantFamily

/-- Fundamental classes and their four functoriality formulas follow from
the finite relative class-formation axioms and invariant conjugacy. -/
theorem relativeFundamentalClassConsequences :
    RelativeFundamentalClassConsequencesStatement.{u} := by
  intro p _ I hI hconj
  exact ⟨I.fundamentalClasses_of_relativeImages hI.2.1,
    I.fundamentalInflation_of_relativeClassFormation hI,
    I.fundamentalRestriction_of_relativeClassFormation hI,
    I.fundamentalCorestriction_of_relativeClassFormation hI,
    I.fundamentalConjugacy_of_relativeImages hI.2.1 hconj⟩

end Langlands.ClassFieldTheory.Local
