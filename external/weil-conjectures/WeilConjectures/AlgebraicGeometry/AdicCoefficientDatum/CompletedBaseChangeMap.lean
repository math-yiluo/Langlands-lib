/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedTowerCorners

/-!
# The completed base-change map as the specified ordered composite

Source: blueprint proper base change, completed base-change map; Stacks Tags 09C9 and 099N
(blueprint: def-weil-pbc-completed-base-change-map).

## Main definitions

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedBaseChangeMap`:
  the recorded construction or statement of this node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory
namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

/-- The ordered construction, extended to ambient inputs. Its first arrow is Rlim(h),
with completed pullback definitionally Rlim(A); its middle arrow is Rlim(v'); its last
arrow is the inverse of the specified direct-image/Rlim conjugate. No arbitrary
isomorphism between the resulting objects is substituted for a comparison.
Source: blueprint completed base-change map, displayed ordered composite
(blueprint: def-weil-pbc-completed-base-change-map). -/
def AdicCoefficientDatum.completedExchange (K : d.derived X) :
    (d.completedPull g).obj ((d.push f).obj K) ⟶
      (d.push f').obj ((d.completedPull g').obj K) :=
  (completedRlim Y' (d.completedRing Y')).map
      ((d.towerH (f := f) (f' := f') (g := g) (g' := g') K).hom) ≫
    (completedRlim Y' (d.completedRing Y')).map (d.towerV' sq K) ≫
      (d.directImageRlimIso f').inv.app
        ((d.towerPull g').obj ((completedReductionTower X d).obj K))

/-- The completed base-change map on the precise domain of the blueprint: proper f,
derived-complete K, and a retained bounded-below etale-origin witness at every finite
quotient. The formula itself is the ambient ordered composite above; the witnesses
certify its finite exchange maps and impose no compatibility or uniform bound.
Source: blueprint completed base-change map, order 1338
(blueprint: def-weil-pbc-completed-base-change-map). -/
def AdicCoefficientDatum.completedBaseChangeMap [IsProper f]
    (K : d.derived X) (_hK : d.TowerComplete X K)
    (_W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj K)) :
    (d.completedPull g).obj ((d.push f).obj K) ⟶
      (d.push f').obj ((d.completedPull g').obj K) :=
  d.completedExchange sq K

end AlgebraicGeometry.Scheme
