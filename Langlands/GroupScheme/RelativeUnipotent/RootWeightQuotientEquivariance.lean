import Langlands.GroupScheme.RelativeUnipotent.RootWeightTorusAction
import Langlands.GroupScheme.RelativeUnipotent.RootWeightQuotient
import Langlands.GroupScheme.Torus.ExponentCocharacters

/-! # Actual power-character equivariance of the exact-weight quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeUnipotent.RootWeightData

open LocalSplitCell

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I]
  {U G : GroupScheme (Spec (CommRingCat.of R))}
  {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {fam : J → (Ga R ⟶ G)}
  {C : RootHeightChart U} (W : RootWeightData C)
  (j : U ⟶ G) [Mono j.hom.hom]
  {index : Fin C.dimension → J}
  (hroot : ∀ k, C.roots (ULift.up k) ≫ j = fam (index k))
  (hu : TorusEquivariant t ch fam)

/-- The actual cocharacter action on each represented term, restricted from its
actual ambient-torus action. -/
def cocharacterAction (v : I → ℤ) (d : ℕ) :
    AutomorphicAction (Gm (Spec (CommRingCat.of R))).toGrp (W.groupScheme d) :=
  (W.torusAction j hroot hu d).restrict
    (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I v))

/-- Restricting an actual root character to an actual exponent cocharacter gives
the power character with the specified integral pairing, on every scheme test. -/
theorem torusChar_exponentCocharacter (α v : I → ℤ)
    (T : Over (Spec (CommRingCat.of R))) (s : T ⟶ (Gm (Spec (CommRingCat.of R))).X) :
    torusChar α T (s ≫
      (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I v)).hom.hom) =
      VectorGroup.charValue (Gm.powerHom _ (coPairing α v)) T s := by
  rw [torusChar, VectorGroup.charValue, VectorGroup.charValue,
    ← comp_groupHom_comp, splitTorus.exponentCocharacter_comp_exponentCharacter]
  rfl

include hroot hu

/-- If the realizing cocharacter has a common pairing N on an exact-weight layer,
the actual quotient map is equivariant for the actual scalar power-character action. -/
theorem quotientMap_isEquivariant_of_pairing (v : I → ℤ) (d : ℕ) (N : ℤ)
    (hw : ∀ k, W.weight k = d + 1 → coPairing (ch (index k)) v = N) :
    (W.cocharacterAction j hroot hu v d).IsEquivariant
      (VectorGroup.weightAction (n := Nat.card (W.exactSupport d)) (Gm.powerHom _ N))
      (W.quotientMap d) := by
  intro T s x
  apply VectorGroup.points_ext
  intro k
  rw [W.comp_quotientMap, W.quotientPoints_coord,
    VectorGroup.coordinates_weightAction_act, Pi.smul_apply, smul_eq_mul,
    W.comp_quotientMap, W.quotientPoints_coord]
  rw [cocharacterAction, AutomorphicAction.restrict_act,
    W.coordinates_torusAction_inclusion j hroot hu]
  dsimp only
  rw [torusChar_exponentCocharacter, hw _ (W.exactEnumeration d k).property]

/-- A cocharacter realizing q times the supplied secondary weights acts on the
exact layer by the common natural power q*(d+1). -/
theorem quotientMap_isEquivariant_of_realization (v : I → ℤ) (q : ℕ)
    (hw : ∀ k, coPairing (ch (index k)) v = (q : ℤ) * W.weight k) (d : ℕ) :
    (W.cocharacterAction j hroot hu v d).IsEquivariant
      (VectorGroup.weightAction (n := Nat.card (W.exactSupport d))
        (Gm.powerHom _ ((q * (d + 1) : ℕ) : ℤ)))
      (W.quotientMap d) := by
  apply W.quotientMap_isEquivariant_of_pairing j hroot hu
  intro k hk
  rw [hw, hk, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

omit hroot hu [Mono j.hom.hom] [Fintype I] in
/-- The exact-layer power is positive for every layer when the realizing multiplier
is positive, including layers with no coordinates. -/
theorem realization_quotient_power_pos (q : ℕ) (hq : 0 < q) (d : ℕ) :
    0 < q * (d + 1) :=
  Nat.mul_pos hq (Nat.succ_pos d)

end Langlands.GroupScheme.RelativeUnipotent.RootWeightData
