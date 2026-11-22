import Langlands.Geometry.FormalGroup.PDivisibleSplitBaseChange

/-! # Base change of the actual alternating polarization -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.PDivisibleGroup

open GroupScheme GroupScheme.Cartier GroupScheme.Cartier.FiniteDual GroupScheme.HomScheme

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {p : ℕ} [Fact p.Prime]
variable (G : PDivisibleGroup (CommRingCat.of R) p) (hExact : FiniteCartierDualExactnessStatement.{u})

local notation "b" => specBase R S
local notation "F" => baseChangeFunctor R S p
local notation "splitTower" => G.splitWithDual hExact
local notation "primalPullback" => Functor.obj (F) G
local notation "splitPullback" => Functor.obj (F) (splitTower)

local instance splitPairingBaseChangeFinite {A : CommRingCat.{u}} (H : PDivisibleGroup A p) (n : ℕ) :
    IsFinite (H.inclusions.obj n).X.hom := (H.finiteLocallyFree n).1
local instance splitPairingBaseChangeFlat {A : CommRingCat.{u}} (H : PDivisibleGroup A p) (n : ℕ) :
    Flat (H.inclusions.obj n).X.hom := (H.finiteLocallyFree n).2.1
local instance splitPairingBaseChangeFP {A : CommRingCat.{u}} (H : PDivisibleGroup A p) (n : ℕ) :
    LocallyOfFinitePresentation (H.inclusions.obj n).X.hom := (H.finiteLocallyFree n).2.2

/-- The split comparison's primal projection is the pullback of the original projection. -/
theorem baseChangeSplitIso_hom_fst :
    (baseChangeSplitIso (S := S) G hExact).hom ≫ prodFst (primalPullback) ((primalPullback).dual hExact) =
      (F).map (prodFst G (G.dual hExact)) := by
  change (_ ≫ Hom.prodMap (𝟙 (primalPullback)) _) ≫ _ = _
  rw [Category.assoc, Hom.prodMap_fst, Category.comp_id, baseChangeProdIso_hom_fst]

/-- The split comparison's dual projection is pullback followed by the Cartier comparison. -/
theorem baseChangeSplitIso_hom_snd :
    (baseChangeSplitIso (S := S) G hExact).hom ≫ prodSnd (primalPullback) ((primalPullback).dual hExact) =
      (F).map (prodSnd G (G.dual hExact)) ≫ (baseChangeDualIso (S := S) G hExact).hom := by
  change (_ ≫ Hom.prodMap (𝟙 (primalPullback)) _) ≫ _ = _
  rw [Category.assoc, Hom.prodMap_snd, ← Category.assoc, baseChangeProdIso_hom_snd]

variable (n : ℕ) (T : Over (Spec (CommRingCat.of S)))

/-- Evaluation of the original polarization on an actual point of its pullback.
The value is a global unit on the same test scheme. -/
def pullbackSplitPairing (x y : T ⟶ ((splitPullback).inclusions.obj n).X) : (Γ(T.left, ⊤))ˣ :=
  let U := (Over.map b).obj T
  let e := baseChangePointsEquiv b ((splitTower).inclusions.obj n).toGrp T
  Gm.pointsEquiv _ U ((G.splitPrincipalPolarization hExact).evaluate n U (e x) (e y))

/-- The split comparison respects the actual polarization on every level and test. -/
theorem baseChangeSplitIso_pairing (x y : T ⟶ ((splitPullback).inclusions.obj n).X) :
    let i := ((baseChangeSplitIso (S := S) G hExact).hom.app n).toMul.hom.hom
    Gm.pointsEquiv _ T (((primalPullback).splitPrincipalPolarization hExact).evaluate n T (x ≫ i) (y ≫ i)) =
      pullbackSplitPairing G hExact n T x y := by
  let U := (Over.map b).obj T
  let P := (splitTower).inclusions.obj n
  let V := G.inclusions.obj n
  let V' := (primalPullback).inclusions.obj n
  let E := baseChangePointsEquiv b P.toGrp T
  let i := ((baseChangeSplitIso (S := S) G hExact).hom.app n).toMul.hom.hom
  let j := (schemeDualBaseChangeIso (S := S) V).hom.toMul.hom.hom
  let fst := ((F).map (prodFst G (G.dual hExact))).app n
  let snd := ((F).map (prodSnd G (G.dual hExact))).app n
  have hfst (z : T ⟶ ((splitPullback).inclusions.obj n).X) :
      (productWithDualPoints V' T (z ≫ i)).1 = z ≫ fst.toMul.hom.hom := by
    have h := congrArg (fun f : (splitPullback) ⟶ (primalPullback) => (f.app n).toMul.hom.hom)
      (baseChangeSplitIso_hom_fst (S := S) G hExact)
    change (z ≫ i) ≫ _ = z ≫ fst.toMul.hom.hom
    rw [Category.assoc]
    exact congrArg (z ≫ ·) h
  have hsnd (z : T ⟶ ((splitPullback).inclusions.obj n).X) :
      (productWithDualPoints V' T (z ≫ i)).2 = z ≫ snd.toMul.hom.hom ≫ j := by
    have h := congrArg (fun f : (splitPullback) ⟶ (primalPullback).dual hExact => (f.app n).toMul.hom.hom)
      (baseChangeSplitIso_hom_snd (S := S) G hExact)
    change (z ≫ i) ≫ _ = z ≫ snd.toMul.hom.hom ≫ j
    rw [Category.assoc]
    exact congrArg (z ≫ ·) h
  have h₁ (z : T ⟶ ((splitPullback).inclusions.obj n).X) :
      baseChangePointsEquiv b V.toGrp T (z ≫ fst.toMul.hom.hom) =
        (productWithDualPoints V U (E z)).1 :=
    baseChangePointsEquiv_comp b ((prodFst G (G.dual hExact)).app n).toMul T z
  have h₂ (z : T ⟶ ((splitPullback).inclusions.obj n).X) :
      baseChangePointsEquiv b (schemeDual V).toGrp T (z ≫ snd.toMul.hom.hom) =
        (productWithDualPoints V U (E z)).2 :=
    baseChangePointsEquiv_comp b ((prodSnd G (G.dual hExact)).app n).toMul T z
  have pairing (z w : T ⟶ ((splitPullback).inclusions.obj n).X) :
      Gm.pointsEquiv _ T (finiteSchemePairing V' T (productWithDualPoints V' T (z ≫ i)).2
        (productWithDualPoints V' T (w ≫ i)).1) =
      Gm.pointsEquiv _ U (finiteSchemePairing V U (productWithDualPoints V U (E z)).2
        (productWithDualPoints V U (E w)).1) := by
    rw [hsnd, hfst]
    have h := schemeDualBaseChangeIso_evaluation (S := S) V T
      (z ≫ snd.toMul.hom.hom) (w ≫ fst.toMul.hom.hom)
    rw [h₁, h₂] at h
    exact h
  change Gm.pointsEquiv _ T (((primalPullback).splitPrincipalPolarization hExact).evaluate n T (x ≫ i) (y ≫ i)) =
    Gm.pointsEquiv _ U ((G.splitPrincipalPolarization hExact).evaluate n U (E x) (E y))
  rw [splitPrincipalPolarization_evaluate, splitPrincipalPolarization_evaluate]
  change Gm.pointsEquiv _ T (productWithDualPairing V' T (x ≫ i) (y ≫ i)) =
    Gm.pointsEquiv _ U (productWithDualPairing V U (E x) (E y))
  rw [productWithDualPairing_apply, productWithDualPairing_apply]
  simp only [map_mul, map_inv, pairing]

end Langlands.PDivisibleGroup
