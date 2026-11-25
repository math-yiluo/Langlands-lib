import Langlands.LocalFactor.Ramification.Wintenberger.Generic
import FontaineWintenberger.Ramification.Upper.Transport
import FontaineWintenberger.LocalField.Spectral.FiniteExtension

/-!
# Finite upper ramification groups: spectral integers of the two libraries

Let `K₀` be a complete, ultrametric, locally compact normed field whose norm induces its
valuative relation, `K` a finite normed extension of `K₀` that is complete and discretely
valued, and `E` a finite Galois extension of `K`. The FontaineWintenberger library computes the
upper ramification groups of `Gal(E/K)` on the integer ring of the spectral norm over `K`; the
Library computes them on the integer ring of its canonical realization of `E` over `K₀`. The two
rings have the same elements, since the spectral norms over `K` and over `K₀` coincide, and the
two families of upper groups are equal.
-/

noncomputable section

namespace Langlands.Ramification.Wintenberger

universe u₀ uK uE

variable (K₀ : Type u₀) [NontriviallyNormedField K₀] [IsUltrametricDist K₀] [CompleteSpace K₀]
  [ValuativeRel K₀] [LocallyCompactSpace K₀]
  (hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b)
  (E : Type uE) [Field E] [Algebra K₀ E] [FiniteDimensional K₀ E]

/-- An element lies in the integer ring of the Library's canonical realization exactly when its
spectral norm over `K₀` is at most one. -/
theorem mem_canonicalIntegers_iff (x : E) :
    x ∈ (LocalField.canonicalTopologicalData K₀ E hbase).Integers ↔ spectralNorm K₀ E x ≤ 1 := by
  let := LocalField.canonicalValuativeRel K₀ E
  change ValuativeRel.valuation E x ≤ 1 ↔ _
  rw [← map_one (ValuativeRel.valuation E), ← Valuation.vle_iff_le]
  change LocalGalois.spectralValuation K₀ E x ≤ LocalGalois.spectralValuation K₀ E 1 ↔ _
  rw [map_one, ← NNReal.coe_le_coe]
  rfl

section SpectralNorm

variable (K : Type uK) [NontriviallyNormedField K] [NormedAlgebra K₀ K] [IsUltrametricDist K]
  [CompleteSpace K] [Algebra K E] [IsScalarTower K₀ K E]

omit [ValuativeRel K₀] [LocallyCompactSpace K₀] [FiniteDimensional K₀ E] in
/-- Over a normed extension `K` of `K₀`, the spectral norms of an algebraic extension over `K`
and over `K₀` coincide. -/
theorem spectralNorm_eq_of_tower [Algebra.IsAlgebraic K₀ E] (x : E) :
    spectralNorm K E x = spectralNorm K₀ E x := by
  let := spectralNorm.nontriviallyNormedField K₀ E
  let := spectralNorm.normedAlgebra' K₀ K E
  let : IsUltrametricDist E :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := K₀) (L := E))
  have : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.tower_top (K := K₀) K
  exact (NormedAlgebra.norm_eq_spectralNorm K x).symm

/-- The spectral integer ring of the FontaineWintenberger library over `K` and the integer ring of
the Library's canonical realization over `K₀` are the same subring. -/
theorem spectralIntegerRing_eq_canonicalIntegers [Algebra.IsAlgebraic K E] :
    (FontaineWintenberger.spectralIntegerRing K E).toSubring =
      (LocalField.canonicalTopologicalData K₀ E hbase).Integers := by
  ext x
  rw [mem_canonicalIntegers_iff, ← spectralNorm_eq_of_tower K₀ E K]
  exact FontaineWintenberger.mem_spectralIntegerRing K E x

/-- The identity on elements, as a ring isomorphism between the two integer rings. -/
def spectralIntegerRingEquiv [Algebra.IsAlgebraic K E] :
    FontaineWintenberger.spectralIntegerRing K E ≃+*
      (LocalField.canonicalTopologicalData K₀ E hbase).Integers :=
  RingEquiv.subringCongr (spectralIntegerRing_eq_canonicalIntegers K₀ hbase E K)

end SpectralNorm

section FiniteUpper

variable (K : Type uK) [NontriviallyNormedField K] [NormedAlgebra K₀ K]
  [FontaineWintenberger.IsCompleteDiscreteValuedField K] [Algebra K E] [IsScalarTower K₀ K E]
  [FiniteDimensional K E] [IsGalois K E]

/-- The FontaineWintenberger upper groups are constant below `-1`. -/
theorem upperRamificationGroup_eq_max {R G : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Group G] [MulSemiringAction G R] [Finite G] (v : ℝ) :
    FontaineWintenberger.upperRamificationGroup (R := R) G v =
      FontaineWintenberger.upperRamificationGroup (R := R) G (max v (-1)) := by
  simp only [FontaineWintenberger.upperRamificationGroup,
    FontaineWintenberger.inverseHerbrandFunction, max_assoc, max_self]

/-- **The finite upper groups of the two libraries agree.** For `E/K` finite Galois, the
FontaineWintenberger upper group on the spectral integers over `K` is the Library's canonical
upper group over the base `K₀`, at every real index. -/
theorem upperRamificationGroup_spectral_eq_canonical (v : ℝ) :
    FontaineWintenberger.upperRamificationGroup
        (R := FontaineWintenberger.spectralIntegerRing K E) (E ≃ₐ[K] E) v =
      Local.canonicalUpperRamificationGroup K₀ E hbase K v := by
  let T := LocalField.canonicalTopologicalData K₀ E hbase
  let := Local.integerAction T K
  let := integers_isDiscreteValuationRing T
  let := automorphismGroup_finite (K₀ := K₀) (L := E) K
  rw [Local.canonicalUpperRamificationGroup, ← upperRamificationGroup_eq_upperRamificationGroup T K v,
    upperRamificationGroup_eq_max, upperRamificationGroup_eq_max (R := T.Integers)]
  rw [← FontaineWintenberger.upperRamificationGroup_map_equivariant
    (spectralIntegerRingEquiv K₀ hbase E K) (MulEquiv.refl (E ≃ₐ[K] E))
    (fun _ _ => Subtype.ext rfl) (le_max_right v (-1))]
  exact (Subgroup.map_id _).symm

end FiniteUpper

end Langlands.Ramification.Wintenberger

