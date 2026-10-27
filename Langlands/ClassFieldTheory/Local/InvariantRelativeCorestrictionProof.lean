import Langlands.ClassFieldTheory.Local.InvariantTransferConsequencesStatement
import Langlands.ClassFieldTheory.Local.RelativeH2CorestrictionRestrictionProof

/-!
# Relative corestriction from the image and restriction laws

Restriction of relative `H²` is surjective once the invariants are injective
with the degree torsion subgroups as images, because `ℚ/ℤ` is divisible. The
corestriction law then follows from `Cor ∘ Res = [E:F]`.
-/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Every element of `ℚ/ℤ` is divisible by every positive integer. -/
theorem rationalModIntegers_exists_nsmul_eq (d : ℕ) (hd : 0 < d)
    (q : RationalModIntegers) : ∃ w : RationalModIntegers, d • w = q := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
  refine ⟨((r / d : ℚ) : RationalModIntegers), ?_⟩
  rw [← QuotientAddGroup.mk_nsmul]
  congr 1
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [nsmul_eq_mul]
  field_simp

namespace InvariantFamily

variable {p : ℕ} [Fact p.Prime]

/-- With the image and restriction laws, actual relative restriction of
degree-two classes is surjective. -/
theorem relativeRestriction_surjective_of_relativeImages (I : InvariantFamily.{u,u} p)
    (hImg : I.RelativeImages) (hRes : I.RelativeRestriction)
    (F E : PadicField.{u} p) (M : Type u) [Field M]
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [Algebra F.Carrier M] [Algebra E.Carrier M]
    [IsScalarTower F.Carrier E.Carrier M]
    [FiniteDimensional F.Carrier E.Carrier] [FiniteDimensional F.Carrier M]
    [FiniteDimensional E.Carrier M]
    [IsGalois F.Carrier M] [IsGalois E.Carrier M]
    (c : relativeCohomology E.Carrier M 2) :
    ∃ y : relativeCohomology F.Carrier M 2,
      relativeRestriction F.Carrier E.Carrier M 2 y = c := by
  obtain ⟨w, hw⟩ := rationalModIntegers_exists_nsmul_eq
    (Module.finrank F.Carrier E.Carrier) Module.finrank_pos (I.relative E M c)
  have hc : I.relative E M c ∈ denominatorSubgroup (Module.finrank E.Carrier M) := by
    rw [← (hImg E M).2]
    exact ⟨c, rfl⟩
  have hwmem : w ∈ (I.relative F M).range := by
    rw [(hImg F M).2]
    change Module.finrank F.Carrier M • w = 0
    rw [← Module.finrank_mul_finrank F.Carrier E.Carrier M, mul_nsmul, hw]
    exact hc
  obtain ⟨y, hy⟩ := hwmem
  refine ⟨y, (hImg E M).1 ?_⟩
  rw [hRes F E M y, hy, hw]

/-- The image and restriction laws imply the relative corestriction law. -/
theorem relativeCorestriction_of_relativeImages (I : InvariantFamily.{u,u} p)
    (hImg : I.RelativeImages) (hRes : I.RelativeRestriction) :
    I.RelativeCorestriction := by
  intro F E M _ _ _ _ _ _ _ _ _ _ _ c
  obtain ⟨y, rfl⟩ := I.relativeRestriction_surjective_of_relativeImages hImg hRes F E M c
  rw [relativeH2CorestrictionRestriction F.Carrier E.Carrier M y, map_nsmul,
    hRes F E M y]

end InvariantFamily

/-- Relative corestriction preserves invariants for every family with the
image and restriction laws. -/
theorem invariantRelativeCorestriction : InvariantRelativeCorestrictionStatement.{u} := by
  intro p _ I hImg hRes
  exact I.relativeCorestriction_of_relativeImages hImg hRes

end Langlands.ClassFieldTheory.Local
