import Langlands.Geometry.FormalGroup.PDivisibleSplitPairingBaseChange

/-! # Pullback of isometries of actual split polarized towers -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.PDivisibleGroup

open GroupScheme GroupScheme.Cartier GroupScheme.HomScheme

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {p : ℕ} [Fact p.Prime] {G H : PDivisibleGroup (CommRingCat.of R) p}
variable (hExact : FiniteCartierDualExactnessStatement.{u})

local notation "F" => baseChangeFunctor R S p
local notation "b" => specBase R S

/-- Pull back a split tower isomorphism and identify the pulled-back split towers
with the splits of the pulled-back primals. -/
def baseChangeSplitTowerIso (e : G.splitWithDual hExact ≅ H.splitWithDual hExact) :
    ((F).obj G).splitWithDual hExact ≅ ((F).obj H).splitWithDual hExact :=
  (baseChangeSplitIso (S := S) G hExact).symm ≪≫ (F).mapIso e ≪≫ (baseChangeSplitIso (S := S) H hExact)

/-- The pulled-back isomorphism intertwines the new split order actions. -/
theorem baseChangeSplitTowerIso_order {A : Type v} [Ring A]
    (a : A →+* End G) (a' : A →+* End H)
    (e : G.splitWithDual hExact ≅ H.splitWithDual hExact) (t : Aᵐᵒᵖ × A)
    (h : splitOrderAction a hExact t ≫ e.hom = e.hom ≫ splitOrderAction a' hExact t) :
    splitOrderAction ((baseChangeEnd (S := S) G).comp a) hExact t ≫
        (baseChangeSplitTowerIso (S := S) hExact e).hom =
      (baseChangeSplitTowerIso (S := S) hExact e).hom ≫
        splitOrderAction ((baseChangeEnd (S := S) H).comp a') hExact t := by
  let i := baseChangeSplitIso (S := S) G hExact
  let j := baseChangeSplitIso (S := S) H hExact
  let x := (F).map (splitOrderAction a hExact t)
  let y := (F).map (splitOrderAction a' hExact t)
  let x' := splitOrderAction ((baseChangeEnd (S := S) G).comp a) hExact t
  let y' := splitOrderAction ((baseChangeEnd (S := S) H).comp a') hExact t
  let f := (F).map e.hom
  have hi : x ≫ i.hom = i.hom ≫ x' := baseChangeSplitIso_order (S := S) G hExact a t
  have hj : y ≫ j.hom = j.hom ≫ y' := baseChangeSplitIso_order (S := S) H hExact a' t
  have hi' : x' ≫ i.inv = i.inv ≫ x := by
    apply (cancel_mono i.hom).mp
    rw [Category.assoc, i.inv_hom_id, Category.comp_id, Category.assoc, hi,
      ← Category.assoc, i.inv_hom_id, Category.id_comp]
  have hf : x ≫ f = f ≫ y := by
    change (F).map (splitOrderAction a hExact t) ≫ (F).map e.hom =
      (F).map e.hom ≫ (F).map (splitOrderAction a' hExact t)
    rw [← (F).map_comp, h, (F).map_comp]
  change x' ≫ i.inv ≫ f ≫ j.hom = (i.inv ≫ f ≫ j.hom) ≫ y'
  rw [← Category.assoc x', hi', Category.assoc, ← Category.assoc x, hf,
    Category.assoc, hj, Category.assoc, Category.assoc]

/-- Pullback on tests preserves the equality of the original finite pairings. -/
private theorem pullbackSplitPairing_preserved
    (f : G.splitWithDual hExact ⟶ H.splitWithDual hExact)
    (h : ∀ (n : ℕ) (T : Over (Spec (CommRingCat.of R)))
      (x y : T ⟶ ((G.splitWithDual hExact).inclusions.obj n).X),
      let m := (f.app n).toMul.hom.hom
      (H.splitPrincipalPolarization hExact).evaluate n T (x ≫ m) (y ≫ m) =
        (G.splitPrincipalPolarization hExact).evaluate n T x y)
    (n : ℕ) (T : Over (Spec (CommRingCat.of S)))
    (x y : T ⟶ (((F).obj (G.splitWithDual hExact)).inclusions.obj n).X) :
    let k := (((F).map f).app n).toMul.hom.hom
    pullbackSplitPairing H hExact n T (x ≫ k) (y ≫ k) = pullbackSplitPairing G hExact n T x y := by
  let U := (Over.map b).obj T
  let A := (G.splitWithDual hExact).inclusions.obj n
  let B := (H.splitWithDual hExact).inclusions.obj n
  let k := (((F).map f).app n).toMul.hom.hom
  let e := baseChangePointsEquiv b A.toGrp T
  let e' := baseChangePointsEquiv b B.toGrp T
  let m := (f.app n).toMul.hom.hom
  have he (z : T ⟶ (((F).obj (G.splitWithDual hExact)).inclusions.obj n).X) :
      e' (z ≫ k) = e z ≫ m := baseChangePointsEquiv_comp b (f.app n).toMul T z
  change Gm.pointsEquiv _ U ((H.splitPrincipalPolarization hExact).evaluate n U
      (e' (x ≫ k)) (e' (y ≫ k))) =
    Gm.pointsEquiv _ U ((G.splitPrincipalPolarization hExact).evaluate n U (e x) (e y))
  rw [he, he]
  exact congrArg (Gm.pointsEquiv _ U) (h n U (e x) (e y))

/-- Pulling back an isometry gives a strict isometry of the actual split towers
on every finite level and test. -/
theorem baseChangeSplitTowerIso_pairing
    (e : G.splitWithDual hExact ≅ H.splitWithDual hExact)
    (h : ∀ (n : ℕ) (T : Over (Spec (CommRingCat.of R)))
      (x y : T ⟶ ((G.splitWithDual hExact).inclusions.obj n).X),
      let m := (e.hom.app n).toMul.hom.hom
      (H.splitPrincipalPolarization hExact).evaluate n T (x ≫ m) (y ≫ m) =
        (G.splitPrincipalPolarization hExact).evaluate n T x y)
    (n : ℕ) (T : Over (Spec (CommRingCat.of S)))
    (x y : T ⟶ ((((F).obj G).splitWithDual hExact).inclusions.obj n).X) :
    let k := ((baseChangeSplitTowerIso (S := S) hExact e).hom.app n).toMul.hom.hom
    (((F).obj H).splitPrincipalPolarization hExact).evaluate n T (x ≫ k) (y ≫ k) =
      (((F).obj G).splitPrincipalPolarization hExact).evaluate n T x y := by
  let i := baseChangeSplitIso (S := S) G hExact
  let j := baseChangeSplitIso (S := S) H hExact
  let m := (i.inv.app n).toMul.hom.hom
  let m' := (i.hom.app n).toMul.hom.hom
  let k := (((F).map e.hom).app n).toMul.hom.hom
  let l := (j.hom.app n).toMul.hom.hom
  let x₁ := x ≫ m
  let y₁ := y ≫ m
  let x₂ := x₁ ≫ k
  let y₂ := y₁ ≫ k
  have hi : m ≫ m' = 𝟙 _ := congrArg (fun f : End (((F).obj G).splitWithDual hExact) =>
    (f.app n).toMul.hom.hom) i.inv_hom_id
  have hx : x₁ ≫ m' = x := by
    change (x ≫ m) ≫ m' = x
    rw [Category.assoc, hi, Category.comp_id]
  have hy : y₁ ≫ m' = y := by
    change (y ≫ m) ≫ m' = y
    rw [Category.assoc, hi, Category.comp_id]
  have hSource := baseChangeSplitIso_pairing G hExact n T x₁ y₁
  change Gm.pointsEquiv _ T ((((F).obj G).splitPrincipalPolarization hExact).evaluate n T
      (x₁ ≫ m') (y₁ ≫ m')) = _ at hSource
  rw [hx, hy] at hSource
  have hTarget := baseChangeSplitIso_pairing H hExact n T x₂ y₂
  have hMap := pullbackSplitPairing_preserved hExact e.hom h n T x₁ y₁
  apply (Gm.pointsEquiv _ T).injective
  change Gm.pointsEquiv _ T ((((F).obj H).splitPrincipalPolarization hExact).evaluate n T
      (x ≫ m ≫ k ≫ l) (y ≫ m ≫ k ≫ l)) = _
  rw [← Category.assoc x, ← Category.assoc y, ← Category.assoc (x ≫ m), ← Category.assoc (y ≫ m)]
  exact hTarget.trans (hMap.trans hSource.symm)

end Langlands.PDivisibleGroup
