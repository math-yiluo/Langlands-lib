import Langlands.Geometry.Building.IntegerValuationBuildingBasedTransport
import Langlands.Geometry.Building.SplitIntegralPinning
import Langlands.Geometry.Building.SplitIntegralFrameUniqueness
import Langlands.Geometry.Building.ConjugateApartmentRealization
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof

/-! # The special point of the integral subgroup of a split integral pinning

Let `B` be integer-valued building data of a connected reductive group `G` over a field `k`
whose valuation ring has an infinite residue field, and let `P` be a split integral pinning
of some maximal split torus `i : S → G` that is also a maximal torus. Conjugating the torus of
`B` onto `i` and transporting `B` along the conjugation, `P` becomes a split integral frame,
so `P.K` is the one-group stabilizer of a special point of `B`. If moreover
`G(k) = P.K · P_ν(k)` for a generic cocharacter `ν` of `i`, that point is the only point of
the reduced building fixed by `P.K`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k] {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The integral subgroup of a split integral pinning of a maximal split torus that is a
maximal torus is the one-group stabilizer of a special point of any building data, and with
an Iwasawa decomposition along a generic cocharacter, that point is its only fixed point. -/
theorem exists_isSpecialPoint_eq_oneStabilizer_of_pinning
    [Infinite (IsLocalRing.ResidueField v.valuationSubring)]
    (B : IntegerValuationBuildingData v G) {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] (hsplit : IsMaximalSplitTorus i)
    (hmax : IsMaximalTorus i) (P : SplitIntegralPinning v i) (ν : cocharacterLattice S)
    (hν : IsGenericCocharacter i ν)
    (hIw : ∀ g : rationalPoints G, ∃ κ ∈ P.K,
      ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
        g = κ * p) :
    ∃ x : B.ReducedBuilding, B.IsSpecialPoint x ∧ P.K = B.oneStabilizer x ∧
      ∀ y : B.ReducedBuilding, (∀ g ∈ P.K, g • y = y) → y = x := by
  -- conjugate the torus of `B` onto `i`
  obtain ⟨g, e, he⟩ := (maximalSplitTorusConjugacy.{u} k G B.isConnectedReductive).1
    B.S S B.i i B.isMaximalSplitTorus hsplit
  let σ : B.S ≅ S :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  have h : B.i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom σ.hom ≫ i := he
  let B' := B.basedTransport σ (G.innerIso g) h
  -- the pinning is a split integral frame of the transported data
  let Fr : B'.SplitIntegralFrame := SplitIntegralPinning.toFrame (B := B') hmax P
  obtain ⟨x₀, hx₀, -, hK⟩ := Fr.exists_isSpecialPoint_K_eq_oneStabilizer
    (exists_unit_sq_ne_one v)
  -- rebase the transported quotient in the original one through the action of `g`
  let E : B'.ReducedBuilding ≃ B.ReducedBuilding :=
    B.apartment.conjugateReducedBuildingEquiv σ g h
  have hE (u : rationalPoints G) (q : B'.ReducedBuilding) : E (u • q) = u • E q :=
    B.apartment.conjugateReducedBuildingEquiv_smul σ g h u q
  have hfix (q : B'.ReducedBuilding) : B.fixer (E q) = B'.fixer q :=
    B.apartment.reducedFixer_conjugateReducedBuildingEquiv σ g h q
  refine ⟨E (B'.apartmentMap x₀), ?_, ?_, fun y hy => ?_⟩
  · -- `E q = g • q'` with `q'` the preimage of `q` under the based comparison
    have hspec : B'.IsSpecialPoint (B'.apartmentMap x₀) :=
      B'.apartment.isSpecialBuildingPoint_apartmentMap (Fr.isSpecialPoint hx₀)
    have hspec' : B.IsSpecialPoint
        ((B.basedBuildingEquiv σ (G.innerIso g) h).symm (B'.apartmentMap x₀)) := by
      rw [← B.isSpecialPoint_basedTransport_iff σ (G.innerIso g) h, Equiv.apply_symm_apply]
      exact hspec
    exact KPApartmentData.IsSpecialBuildingPoint.smul B.apartment hspec' g
  · change P.K = characterValuationKernel v G ⊓ B.fixer (E (B'.apartmentMap x₀))
    rw [hfix]
    exact hK
  · have hy' : ∀ κ ∈ Fr.K, κ • E.symm y = E.symm y := by
      intro κ hκ
      apply E.injective
      rw [hE, Equiv.apply_symm_apply]
      exact hy κ hκ
    have := Fr.eq_apartmentMap_of_forall_smul_eq_of_infinite hx₀ ν hν hIw (E.symm y) hy'
    rw [← this, Equiv.apply_symm_apply]

end IntegerValuationBuildingData

end Langlands.Geometry.Building
