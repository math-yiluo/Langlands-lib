import Langlands.GroupScheme.Unipotent.ElementarySplitStatement
import Langlands.GroupScheme.Rational.SplitCommutativeVector
import Langlands.GroupScheme.Rational.VectorGroupSplit

/-! # Split elementary unipotent groups are vector groups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A closed subgroup of a vector group in positive characteristic is split unipotent
if and only if it is isomorphic to a standard vector group. -/
theorem elementaryUnipotentSplitIffVector : ElementaryUnipotentSplitIffVectorStatement.{u} := by
  intro k _ p _ _ G n e he
  constructor
  · rintro ⟨m, hm⟩
    have hV : RelativeRoot.IsVectorGroupOfDimension
        (VectorGroup.groupScheme (CommRingCat.of k) n) n :=
      ⟨VectorGroup.coordinates (CommRingCat.of k) n, VectorGroup.isNaturalVectorCoordinates⟩
    let : IsClosedImmersion e.hom.hom.left := he
    let : Mono e.hom.hom := Over.mono_of_mono_left _
    let : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) n).X.hom := hV.isAffineHom
    let : IsAffineHom G.X.hom := by
      rw [← Over.w e.hom.hom]
      infer_instance
    have hcomm : ∀ (T : Over (Spec (CommRingCat.of k))) (x y : T ⟶ G.X),
        x * y = y * x := by
      intro T x y
      apply (cancel_mono e.hom.hom).1
      rw [MonObj.mul_comp, MonObj.mul_comp]
      exact (hV.points_commute _ _).eq
    have hexp : HasUniformPowerExponent (VectorGroup.groupScheme (CommRingCat.of k) n)
        (ringChar k) := by
      intro T x
      let coords := VectorGroup.coordinates (CommRingCat.of k) n T
      apply coords.injective
      rw [map_pow, map_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext j
      change ringChar k • (coords x).toAdd j = 0
      have hzero : (ringChar k : Γ(T.left, ⊤)) = 0 := by
        rw [← map_natCast (scalarMap T), ringChar.Nat.cast_ringChar, map_zero]
      rw [nsmul_eq_mul, hzero, zero_mul]
    exact ⟨m, ⟨(RelativeRoot.isVectorGroupOfDimension_of_hasSplitSeries_of_exponent G
      hcomm (hexp.of_mono e) hm).iso⟩⟩
  · rintro ⟨m, ⟨i⟩⟩
    exact ⟨m, (VectorGroup.hasSplitSeries (k := k) m).of_iso i.symm⟩

end Langlands.GroupScheme
