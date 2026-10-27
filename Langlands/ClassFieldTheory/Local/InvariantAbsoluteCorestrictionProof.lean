import Langlands.ClassFieldTheory.Local.InvariantTransferConsequencesStatement
import Langlands.Cohomology.Continuous.CorestrictionIndexProof

/-!
# Absolute corestriction from bijective invariants and the restriction law

Absolute restriction of `H²` is surjective once the absolute invariants are
bijective, because `ℚ/ℤ` is divisible. The corestriction law then follows from
`Cor ∘ Res = [E:F]` on continuous cohomology.
-/

noncomputable section

open CategoryTheory Langlands.Continuous

namespace Langlands.ClassFieldTheory.Local

universe u

local instance absoluteGroupCompact' (K : Type u) [Field K] [CharZero K] :
    CompactSpace (Field.absoluteGaloisGroup K) :=
  inferInstanceAs (CompactSpace Gal(AlgebraicClosure K/K))

/-- Every element of `ℚ/ℤ` is divisible by every positive integer. -/
private theorem exists_nsmul_eq_of_pos (d : ℕ) (hd : 0 < d)
    (q : RationalModIntegers) : ∃ w : RationalModIntegers, d • w = q := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective q
  refine ⟨((r / d : ℚ) : RationalModIntegers), ?_⟩
  rw [← QuotientAddGroup.mk_nsmul]
  congr 1
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [nsmul_eq_mul]
  field_simp

section Index

variable (K L : Type u) [Field K] [Field L] [CharZero K]
  [Algebra K L] [FiniteDimensional K L]
  [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]

set_option backward.isDefEq.respectTransparency false in
/-- Absolute corestriction after absolute restriction is multiplication by
the degree. -/
theorem absoluteCorestriction_absoluteRestriction (q : ℕ)
    (y : absoluteCohomology K q) :
    absoluteCorestriction K L q (absoluteRestriction K L q y) =
      Module.finrank K L • y := by
  have hres : absoluteRestriction K L q y =
      (AbsoluteRestriction.subgroupCohomologyIso K L q).hom
        (continuousRestriction (absoluteUnitDiscreteModule K)
          (AbsoluteRestriction.openSubgroup K L).toSubgroup q y) := by
    rw [← AbsoluteRestriction.continuousRestriction_comp_subgroupCohomologyIso]
    rfl
  have hindex := congrArg (fun f => f y)
    (continuousRestriction_corestriction_index (absoluteUnitDiscreteModule K)
      (AbsoluteRestriction.openSubgroup K L) q)
  rw [hres, ← AbsoluteRestriction.index_eq_finrank K L]
  unfold absoluteCorestriction
  change continuousCorestriction (absoluteUnitDiscreteModule K)
      (AbsoluteRestriction.openSubgroup K L) q
        ((AbsoluteRestriction.subgroupCohomologyIso K L q).inv
          ((AbsoluteRestriction.subgroupCohomologyIso K L q).hom _)) = _
  rw [Iso.hom_inv_id_apply]
  simp only at hindex
  exact hindex

end Index

namespace InvariantFamily

variable {p : ℕ} [Fact p.Prime]

/-- Bijective absolute invariants with the restriction law make absolute
restriction of degree-two classes surjective. -/
theorem absoluteRestriction_surjective_of_absoluteIsomorphisms
    (I : InvariantFamily.{u,u} p)
    (hIso : I.AbsoluteIsomorphisms) (hRes : I.AbsoluteRestriction)
    (F E : PadicField.{u} p) [Algebra F.Carrier E.Carrier]
    [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    [Algebra (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)]
    [IsScalarTower F.Carrier (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)]
    (x : absoluteCohomology E.Carrier 2) :
    ∃ y : absoluteCohomology F.Carrier 2,
      absoluteRestriction F.Carrier E.Carrier 2 y = x := by
  obtain ⟨w, hw⟩ := exists_nsmul_eq_of_pos
    (Module.finrank F.Carrier E.Carrier) Module.finrank_pos (I.absolute E x)
  obtain ⟨y, hy⟩ := (hIso F).2 w
  refine ⟨y, (hIso E).1 ?_⟩
  rw [hRes F E y, hy, hw]

/-- Bijective absolute invariants with the restriction law imply the absolute
corestriction law. -/
theorem absoluteCorestriction_of_absoluteIsomorphisms (I : InvariantFamily.{u,u} p)
    (hIso : I.AbsoluteIsomorphisms) (hRes : I.AbsoluteRestriction) :
    I.AbsoluteCorestriction := by
  intro F E _ _ _ _ _
  let _ : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  intro x
  obtain ⟨y, rfl⟩ := I.absoluteRestriction_surjective_of_absoluteIsomorphisms
    hIso hRes F E x
  rw [absoluteCorestriction_absoluteRestriction, map_nsmul, hRes F E y]

end InvariantFamily

/-- Absolute corestriction preserves invariants for every family with
bijective absolute invariants and the absolute restriction law. -/
theorem invariantAbsoluteCorestriction : InvariantAbsoluteCorestrictionStatement.{u} := by
  intro p _ I hIso hRes
  exact I.absoluteCorestriction_of_absoluteIsomorphisms hIso hRes

end Langlands.ClassFieldTheory.Local
