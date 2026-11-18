import Langlands.Representation.Plancherel.MaximalLeviCharacterDirection
import Langlands.Representation.Plancherel.RationalUnramifiedRestrictionKernel

/-! # The cyclic valuation kernel of an actual maximal proper Levi -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme Langlands.LinearAlgebra.RationalSpan
open Langlands.LinearAlgebra.InvariantFormComplements
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel.MaximalLeviCharacterDirection

universe u

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G P M : GroupScheme (Spec (CommRingCat.of k))}

/-- After a positive integer multiple, every character is an ambient
restriction plus an integer multiple of a fixed character. -/
abbrev HasOneIntegralDirection (f : M ⟶ G) : Prop :=
  ∃ chi0 : rationalCharacters M,
    ∀ chi : rationalCharacters M,
      ∃ n : ℕ, 0 < n ∧ ∃ (c : ℤ) (psi : rationalCharacters G),
        n • chi = c • chi0 + characterRestrict f psi

variable (hG : IsConnectedReductive G)
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hproper : ¬ IsIso p)
  (hmax : ∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : Q ⟶ G) (j : P ⟶ Q),
    IsParabolicSubgroup q → j ≫ q = p → IsIso j ∨ IsIso q)
  (ha : IsSplitComponent a)

include hG hp hl hproper hmax ha

/-- An integral form of the single rational character direction of an actual
maximal proper Levi. -/
theorem exists_one_integral_direction :
    HasOneIntegralDirection (l ≫ p) := by
  obtain ⟨chi0, hchi0⟩ := exists_one_rational_direction hG hp hl hproper hmax ha
  have hinj := (characterRestriction k M hl.isConnectedReductive A a ha).1
  have hA : IsSplitTorus A.toGrp := ha.1.1.1
  refine ⟨chi0, fun chi => ?_⟩
  obtain ⟨c, y, hxy⟩ := hchi0 (toRat chi)
  obtain ⟨n, hn, psi, hpsi⟩ := exists_nsmul_eq_one_tmul y
  refine ⟨c.den * n, Nat.mul_pos c.den_pos hn, (n : ℤ) * c.num, c.den • psi,
    hinj (hA.character_toRat_injective ?_)⟩
  have hc : (c.den : ℚ) • (c • toRat chi0) = toRat (c.num • chi0) := by
    rw [smul_smul, mul_comm, Rat.mul_den_eq_num, map_zsmul,
      Int.cast_smul_eq_zsmul]
  have hy : rationalCharacterRestrictRat (l ≫ p) ((n : ℚ) • y) =
      toRat (characterRestrict (l ≫ p) psi) := by
    rw [hpsi, rationalCharacterRestrictRat_tmul]
    rfl
  have hy' : (n : ℚ) • rationalCharacterRestrictRat (l ≫ p) y =
      toRat (characterRestrict (l ≫ p) psi) := by
    simpa only [map_smul] using hy
  have he : ((c.den * n : ℕ) : ℚ) • toRat chi =
      toRat (((n : ℤ) * c.num) • chi0 + characterRestrict (l ≫ p) (c.den • psi)) := by
    rw [Nat.cast_mul, mul_comm, mul_smul, hxy, smul_add, hc,
      smul_add, smul_comm (n : ℚ) (c.den : ℚ), hy']
    simp only [map_add, map_nsmul, map_zsmul, Nat.cast_smul_eq_nsmul,
      mul_smul]
  change toRat (characterRestrict a ((c.den * n) • chi)) =
    toRat (characterRestrict a
      (((n : ℤ) * c.num) • chi0 + characterRestrict (l ≫ p) (c.den • psi)))
  have he' := congrArg (rationalCharacterRestrictRat a) he
  simpa only [map_smul, Nat.cast_smul_eq_nsmul, ← map_nsmul,
    rationalCharacterRestrictRat_toRat] using he'

end Langlands.Plancherel.MaximalLeviCharacterDirection

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G P M : GroupScheme (Spec (CommRingCat.of F))}

/-- The actual valuation-map kernel for the Levi of a maximal proper parabolic
is cyclic, over every nonarchimedean local field. -/
theorem maximalLevi_rationalValuationKernel_isCyclic
    (hG : IsConnectedReductive G)
    {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hproper : ¬ IsIso p)
    (hmax : ∀ (Q : GroupScheme (Spec (CommRingCat.of F))) (q : Q ⟶ G) (j : P ⟶ Q),
      IsParabolicSubgroup q → j ≫ q = p → IsIso j ∨ IsIso q)
    (ha : IsSplitComponent a) :
    IsCyclic (rationalValuationImageMap (l ≫ p)).ker := by
  obtain ⟨chi0, hchi0⟩ :=
    MaximalLeviCharacterDirection.exists_one_integral_direction hG hp hl hproper hmax ha
  exact rationalValuationKernel_isCyclic_of_one_direction (l ≫ p) chi0 hchi0

end Langlands.Plancherel
