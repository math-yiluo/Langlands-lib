import Langlands.Representation.Classification.IrreducibleTwoFactorProductSwapProof
import Langlands.Representation.Classification.SegmentTensorStabilizerProof

/-!
# Swapping an irreducible two-block product along the uniform shape

The Library theorem `irreducibleTwoFactorProductSwap` (Zelevinsky 1980, Theorem 1.9,
irreducible equal-rank case) is stated along `Shahidi.twoBlocks r r` on `GL_(r+r)`.
The shuffle isomorphisms of `shuffleFamily_induced_iso` use the uniform shape
`BlockShape.uniform 2 r` on `GL_(2*r)`. The two shapes agree after the rank cast
`r + r = 2 * r`, and this file transports the swap across that cast.
-/

noncomputable section

set_option linter.style.haveILetI false

namespace Langlands.Classification.JuxtaposedShuffle

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Equal block shapes with heterogeneously equal block families give equal
normalized products. -/
theorem productFunctor_obj_eq_of_heq {n : ℕ} {B C : BlockShape n} (h : B = C)
    (A : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (A' : letI := T.topology
      ∀ i : Fin C.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (C.size i) F.Carrier))
    (hA : HEq A A') :
    letI := T.topology
    (T.normalizedProductInductionFunctor B).obj A =
      (T.normalizedProductInductionFunctor C).obj A' := by
  subst h
  obtain rfl := eq_of_heq hA
  rfl

/-- Irreducibility of a normalized product is unchanged by a cast of the total rank. -/
theorem rankCast_isIrreducible_iff {m n : ℕ} (h : m = n) (B : BlockShape m)
    (A : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    ((T.normalizedProductInductionFunctor (B.rankCast h)).obj A).IsIrreducible ↔
      ((T.normalizedProductInductionFunctor B).obj A).IsIrreducible := by
  subst h
  rfl

/-- An isomorphism of normalized products survives a cast of the total rank. -/
theorem rankCast_nonempty_iso {m n : ℕ} (h : m = n) (B : BlockShape m)
    (A A' : letI := T.topology
      ∀ i : Fin B.length, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (e : letI := T.topology
      Nonempty ((T.normalizedProductInductionFunctor B).obj A ≅
        (T.normalizedProductInductionFunctor B).obj A')) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor (B.rankCast h)).obj A ≅
      (T.normalizedProductInductionFunctor (B.rankCast h)).obj A') := by
  subst h
  exact e

/-- The equal-rank two-block shape, cast to total rank `2 * r`, is the uniform shape
with two blocks. -/
theorem twoBlocks_rankCast_eq_uniform {r : ℕ} (hr : 0 < r) :
    (Shahidi.twoBlocks r r hr hr).rankCast (two_mul r).symm = BlockShape.uniform 2 r hr := by
  change BlockShape.mk 2 ![r, r] _ _ = BlockShape.mk 2 (fun _ => r) _ _
  congr 1
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i <;> rfl

/-- The factor families of the two shapes agree. -/
theorem twoBlockFactors_heq {r : ℕ} (hr : 0 < r)
    (σa σb : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    HEq (twoBlockFactors hr hr σa σb) (![σa, σb] :
      ∀ i : Fin (BlockShape.uniform 2 r hr).length,
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((BlockShape.uniform 2 r hr).size i) F.Carrier)) := by
  letI := T.topology
  refine Function.hfunext rfl fun i i' hii' => ?_
  obtain rfl : i = i' := eq_of_heq hii'
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i <;> exact HEq.rfl

/-- **Two-block swap along the uniform shape.** If the product `σa × σb` of irreducible
representations of `GL_r` along `BlockShape.uniform 2 r` is irreducible, it is
isomorphic to `σb × σa`. This is the Library theorem `irreducibleTwoFactorProductSwap`
transported from `Shahidi.twoBlocks r r`. -/
theorem uniform_two_swap_of_isIrreducible' {r : ℕ} (hr : 0 < r)
    (σa σb : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (ha : letI := T.topology; σa.IsIrreducible) (hb : letI := T.topology; σb.IsIrreducible)
    (hirr : letI := T.topology
      ((T.normalizedProductInductionFunctor.{uF, uV}
        (BlockShape.uniform 2 r hr)).obj ![σa, σb]).IsIrreducible) :
    letI := T.topology
    Nonempty ((T.normalizedProductInductionFunctor.{uF, uV}
        (BlockShape.uniform 2 r hr)).obj ![σa, σb] ≅
      (T.normalizedProductInductionFunctor.{uF, uV}
        (BlockShape.uniform 2 r hr)).obj ![σb, σa]) := by
  letI := T.topology
  have hsh := twoBlocks_rankCast_eq_uniform hr
  have hab := productFunctor_obj_eq_of_heq (T := T) hsh _ _ (twoBlockFactors_heq hr σa σb)
  have hba := productFunctor_obj_eq_of_heq (T := T) hsh _ _ (twoBlockFactors_heq hr σb σa)
  have hirr' : ((T.normalizedProductInductionFunctor.{uF, uV}
      (Shahidi.twoBlocks r r hr hr)).obj (twoBlockFactors hr hr σa σb)).IsIrreducible := by
    rw [← rankCast_isIrreducible_iff (two_mul r).symm, hab]
    exact hirr
  obtain ⟨e⟩ := rankCast_nonempty_iso (T := T) (two_mul r).symm _ _ _
    (irreducibleTwoFactorProductSwap F T r hr σa σb ha hb hirr')
  exact ⟨eqToIso hab.symm ≪≫ e ≪≫ eqToIso hba⟩

/-- The two-block swap hypothesis of `shuffleFamily_induced_iso` for the twists of a
supercuspidal representation, from irreducibility of the products whose exponents
differ by more than one. -/
theorem segmentFactor_swap_of_isIrreducible' {r : ℕ} (hr : 0 < r)
    (A : letI := T.topology
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
    (hirr : ∀ a b : ℕ, b + 1 < a → letI := T.topology
      ((T.normalizedProductInductionFunctor.{uF, uV} (BlockShape.uniform 2 r hr)).obj
        ![T.segmentFactor A.obj (a : ℝ), T.segmentFactor A.obj (b : ℝ)]).IsIrreducible) :
    ∀ a b : ℕ, b + 1 < a → letI := T.topology
      Nonempty ((T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 r hr)).obj
            ![T.segmentFactor A.obj (a : ℝ), T.segmentFactor A.obj (b : ℝ)] ≅
        (T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 r hr)).obj
            ![T.segmentFactor A.obj (b : ℝ), T.segmentFactor A.obj (a : ℝ)]) := by
  intro a b hab
  letI := T.topology
  exact uniform_two_swap_of_isIrreducible' hr _ _
    (segmentSupercuspidalFactor F T A a).property.1
    (segmentSupercuspidalFactor F T A b).property.1 (hirr a b hab)

end Langlands.Classification.JuxtaposedShuffle
