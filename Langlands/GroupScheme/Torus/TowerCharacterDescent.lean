import Langlands.GroupScheme.Torus.NumberedCharacterDescent

/-! # Signed weight fibers through two character descents -/

noncomputable section
universe u v
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {K F L : Type u} [CommRing K] [IsDomain K]
  [CommRing F] [IsDomain F] [CommRing L] [IsDomain L]
  (b : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K))
  (b' : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of F))
  (S : CommGroupScheme (Spec (CommRingCat.of K))) (hS : IsSplitTorus S.toGrp)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (hT : IsSplitTorus T.toGrp)
  (f : (CommGroupScheme.baseChange b).obj S ⟶ T)

namespace characterLattice

/-- Descend over the second extension, restrict along the supplied morphism,
and descend over the first extension. -/
def descendRestrictFamilyTower {I : Type v}
    (chi : I → characterLattice ((CommGroupScheme.baseChange b').obj T)) :
    I → characterLattice S :=
  descendFamily b S hS (fun i => f ≫ descendFamily b' T hT chi i)

end characterLattice

/-- Descend a character family, restrict it, and descend once more. Its signed
weight fibers are computed on the original family and the actual lifted
cocharacter. -/
theorem signed_weight_card_descendFamily_tower {I : Type v}
    (chi : I → characterLattice ((CommGroupScheme.baseChange b').obj T))
    (nu : cocharacterLattice S) (c : ℤ) :
    Nat.card {a : I × ℤˣ // (a.2 : ℤ) * latticePairing S
      (characterLattice.descendRestrictFamilyTower b b' S hS T hT f chi a.1) nu = c} =
    Nat.card {a : I × ℤˣ //
      latticePairing ((CommGroupScheme.baseChange b').obj T)
        ((a.2 : ℤ) • chi a.1)
        (cocharacterLattice.baseChange b' T
          (cocharacterLattice.baseChange b S nu ≫ f)) = c} := by
  dsimp only [characterLattice.descendRestrictFamilyTower]
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight fun a => ?_
  rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul,
    latticePairing_descendFamily b S hS,
    latticePairing_restrict_descendFamily b' T hT f]

end Langlands.GroupScheme
