import Langlands.Geometry.Building.PositiveDepthFieldDescent
import Langlands.GroupScheme.Rational.RootRayFromFactorPairs
import Langlands.GroupScheme.Rational.TwoCharacterPositiveCocharacter

/-! # Positive integral root cones and additive depths -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]
  [Smooth G.X.hom]

/-- Opposite factor pairs suffice for the primitive/double classification,
without an apartment or relative-root-system realization. -/
theorem HasOppositeFactorPairs.exists_indivisiblePositiveRoot_eq_or_double
    (hS : IsSplitTorus S.toGrp) (hE : HasOppositeFactorPairs i)
    (ν : cocharacterLattice S) {c : characterLattice S}
    (hc : c ∈ positiveRelativeRoots i ν) :
    ∃ a ∈ indivisiblePositiveRoots i ν, c = a ∨ c = 2 • a := by
  obtain ⟨a, ha, m, _, hm, hma⟩ :=
    exists_indivisiblePositiveRoot_ray i ν hc.1 hc.2
  refine ⟨a, ha, ?_⟩
  rcases hE.root_eq_or_twice_of_common_positive_multiple i hS
      hc.1 ha.1.1 (by omega : 0 < (1 : ℕ)) hm
      (by simpa only [one_smul] using hma.symm) with heq | heq | heq
  · exact Or.inl heq
  · exact Or.inr heq
  · exact False.elim (ha.1.2 c hc.1 2 (by omega) heq.symm)

/-- Every selected positive actual root is covered by the entries or doubles
of any complete enumeration of the indivisible positive roots. -/
theorem HasOppositeFactorPairs.positive_subset_primitive_double_cover
    (hS : IsSplitTorus S.toGrp) (hE : HasOppositeFactorPairs i)
    (ν : cocharacterLattice S) {n : ℕ} (a : Fin n → characterLattice S)
    (ha : Set.range a = indivisiblePositiveRoots i ν)
    {Ψ : Set (characterLattice S)} (hΨ : Ψ ⊆ positiveRelativeRoots i ν) :
    ∀ c ∈ Ψ, ∃ j, c = a j ∨ c = 2 • a j := by
  intro c hc
  obtain ⟨d, hd, hcd⟩ :=
    hE.exists_indivisiblePositiveRoot_eq_or_double i hS ν (hΨ hc)
  obtain ⟨j, rfl⟩ := (show d ∈ Set.range a by rw [ha]; exact hd)
  exact ⟨j, hcd⟩

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : S.toGrp ⟶ G) [IsAffineHom G.X.hom]

/-- The actual roots occurring as positive integral combinations of two
supplied characters. The input characters need not belong to this cone. -/
def positiveIntegralRootCone (a b : characterLattice S) :
    Set (characterLattice S) :=
  {c | c ∈ relativeRoots i ∧
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ c = p • a + q • b}

theorem positiveIntegralRootCone_positive
    (ν : cocharacterLattice S) {a b : characterLattice S}
    (ha : 0 < latticePairing S a ν) (hb : 0 < latticePairing S b ν) :
    positiveIntegralRootCone i a b ⊆ positiveRelativeRoots i ν := by
  rintro c ⟨hc, p, q, hp, hq, rfl⟩
  refine ⟨hc, ?_⟩
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply,
    nsmul_eq_mul]
  exact add_pos (mul_pos (by exact_mod_cast hp) ha)
    (mul_pos (by exact_mod_cast hq) hb)

theorem positiveIntegralRootCone_combination
    {a b c d : characterLattice S}
    (hc : c ∈ positiveIntegralRootCone i a b)
    (hd : d ∈ positiveIntegralRootCone i a b)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hroot : p • c + q • d ∈ relativeRoots i) :
    p • c + q • d ∈ positiveIntegralRootCone i a b := by
  obtain ⟨_, r, s, hr, hs, rfl⟩ := hc
  obtain ⟨_, t, v, ht, hv, rfl⟩ := hd
  refine ⟨hroot, p * r + q * t, p * s + q * v,
    add_pos (Nat.mul_pos hp hr) (Nat.mul_pos hq ht),
    add_pos (Nat.mul_pos hp hs) (Nat.mul_pos hq hv), ?_⟩
  simp only [smul_add, add_smul, smul_smul]
  abel

/-- Every additive real depth supplies the exact combination bound on the
positive integral cone, including its doubled-root bound. -/
theorem positiveIntegralRootCone_closedDepth
    (ν : cocharacterLattice S) {a b : characterLattice S}
    (ha : 0 < latticePairing S a ν) (hb : 0 < latticePairing S b ν)
    (f : characterLattice S →+ ℝ) :
    IsClosedPositiveRootDepth i ν (positiveIntegralRootCone i a b) f := by
  refine ⟨positiveIntegralRootCone_positive i ν ha hb, ?_⟩
  intro c d hc hd p q hp hq hroot
  refine ⟨positiveIntegralRootCone_combination i hc hd hp hq hroot, ?_⟩
  simp only [map_add, map_nsmul, nsmul_eq_mul, le_refl]

theorem additiveDepth_double (f : characterLattice S →+ ℝ)
    (c : characterLattice S) :
    2 * f c = f (2 • c) := by
  rw [map_nsmul, nsmul_eq_mul, Nat.cast_ofNat]

/-- The original V3 union is literally the union indexed by its actual cone
when an additive depth takes the two supplied values. -/
theorem rootDepthGeneratedSubgroup_positiveIntegralRootCone
    (φ : RootFunctionFamily S G) (a b : characterLattice S)
    (f : characterLattice S →+ ℝ) :
    rootDepthGeneratedSubgroup i φ (positiveIntegralRootCone i a b) f =
      Subgroup.closure (⋃ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • b ∈ relativeRoots i),
        rootFiltration i φ (p • a + q • b) (p * f a + q * f b)) := by
  unfold rootDepthGeneratedSubgroup
  congr 1
  ext g
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨⟨c, hc, p, q, hp, hq, rfl⟩, hg⟩
    exact ⟨p, q, hp, hq, hc, by
      simpa only [map_add, map_nsmul, nsmul_eq_mul] using hg⟩
  · rintro ⟨p, q, hp, hq, hc, hg⟩
    exact ⟨⟨p • a + q • b, hc, p, q, hp, hq, rfl⟩, by
      simpa only [map_add, map_nsmul, nsmul_eq_mul] using hg⟩

/-- Rational independence of two characters permits arbitrary prescribed
real depths on them, by extending a map from their actual rational span. -/
theorem exists_additiveDepth_of_independent
    (a b : characterLattice S)
    (hlin : LinearIndependent ℚ ![toRat a, toRat b]) (r s : ℝ) :
    ∃ f : characterLattice S →+ ℝ, f a = r ∧ f b = s := by
  classical
  let B := Module.Basis.span hlin
  let h : Submodule.span ℚ (Set.range ![toRat a, toRat b]) →ₗ[ℚ] ℝ :=
    B.constr ℚ ![r, s]
  obtain ⟨g, hg⟩ := h.exists_extend
  refine ⟨g.toAddMonoidHom.comp toRat, ?_, ?_⟩
  · have hx := LinearMap.congr_fun hg (B 0)
    change g (toRat a) = r
    change g (B 0) = B.constr ℚ ![r, s] (B 0) at hx
    rw [Module.Basis.constr_basis] at hx
    rw [show (B 0 : ℚ ⊗[ℤ] characterLattice S) = toRat a from
      Module.Basis.coe_span_apply hlin 0] at hx
    exact hx
  · have hx := LinearMap.congr_fun hg (B 1)
    change g (toRat b) = s
    change g (B 1) = B.constr ℚ ![r, s] (B 1) at hx
    rw [Module.Basis.constr_basis] at hx
    rw [show (B 1 : ℚ ⊗[ℤ] characterLattice S) = toRat b from
      Module.Basis.coe_span_apply hlin 1] at hx
    exact hx

end Langlands.Geometry.Building
