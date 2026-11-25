/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechModel
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechResolutionCore
import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechResolutionExchange

/-! # An alternating acyclic resolution with ordinary exchange

Source: Stacks Project, Tags 02KG and 02KH; blueprint finite affine Čech calculation, Steps 1--2
of `lem-pc-affine-alternating-cech-pinned-mate`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- An increasing-tuple resolution computes the explicit section model, remains a
resolution after ordinary pullback, and has invertible termwise ordinary exchange.
This statement involves no derived base-change mate and no left-derived counit.
Source: Stacks Project, Tags 02KG and 02KH; Steps 1--2 of
`lem-pc-affine-alternating-cech-pinned-mate`.
(blueprint: lem-pc-affine-alternating-cech-exchange-resolution).

Proof: In nonnegative degree n take the finite product of j_{J,*}(G|_{U_J}) over
strictly increasing (n+1)-tuples, with signed restriction differential, and extend
by zero to integer degrees. Augment by restrictions. On U_i insert i into a tuple,
sort with its sign, and set repeated indices to zero. The two orders of deleting
an index cancel, leaving the identity in the augmented homotopy equation. This
proves the augmentation is a quasi-isomorphism; after ordinary tensor pullback the
same additive contracting homotopy proves the pulled-back augmentation is a
quasi-isomorphism, without tensor exactness. Separatedness over Spec A makes every
nonempty intersection affine. Apply affine_open_pushforward_rightAcyclic to each
intersection factor. Right-acyclic objects are closed under finite products. Apply
isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic to the resulting bounded-below
complex, then use rightDerivedFunctorPlusCompatibility and its unit identity to
make the unbounded right-derived unit invertible on D. Since X is separated over the affine base,
every affine intersection inclusion
j_J is an affine morphism: its inverse image on an affine chart V is U_J intersect V,
which is affine. Apply affinePushforward_baseChange to j_J and its cartesian
pullback square, with the quasi-coherent restriction of G. Thus p* of each factor
is the corresponding open pushforward on the pulled-back cover. Those intersections
are affine, and p*G is quasi-coherent; apply the same acyclicity argument for f'.
The affine tilde-Gamma equivalence identifies f_*D with the sheafification of the
increasing-tuple section complex, namely affineAlternatingCechModel. Its differential
is identified by the restriction formulas. On each intersection ordinary exchange
is the affine-section map s tensor b ↦ b times the pullback of s, which is bijective
by exists_tensorPullback_affine_sections. Finite products commute with tensor, so
exchange is invertible in each degree, hence on the homotopy complex and after
localization. For r=0 the cover condition forces X empty; all terms and maps are
zero and the same assertions hold. No arbitrary resolution witness is used in a
definition: the witnesses here are consumed only by the proof of the pinned mate. -/
theorem exists_affineAlternatingCech_exchange_resolution
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [QuasiCompact f] [IsSeparated f] (g : Spec B ⟶ Spec A)
    {r : ℕ} (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (haffine : ∀ i, IsAffineOpen (U i))
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback (pullback.fst f g)).Additive]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G] :
    ∃ (D : HomotopyCategory
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
      (a : (HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G ⟶ D)
      (q : ((Scheme.Modules.pushforward f).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj D ≅
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (affineAlternatingCechModel f U G)),
      IsIso (DerivedCategory.Qh.map a) ∧
      IsIso ((DerivedCategory.Qh (C := SheafOfModules.{u}
        (moduleRings (pullback f g).toRingedSpace))).map
        (((Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomotopyCategory
          (ComplexShape.up ℤ)).map a)) ∧
      IsIso ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app D) ∧
      IsIso ((RingedSpace.moduleDirectImage
        (pullback.snd f g).toLRSHom.toShHom).rightDerivedFunctorUnit.app
          (((Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj D)) ∧
      IsIso ((DerivedCategory.Qh (C := SheafOfModules.{u}
        (moduleRings (Spec B).toRingedSpace))).map
        ((moduleHomotopyBaseChange f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition).app D)) := by
  obtain ⟨D, a, _q, ha, hpa, hα, hβ, hterms⟩ :=
    affineAlternatingCech_resolution_core f g U hU haffine G
  have hb := affineAlternatingCech_resolution_exchange f g G D hterms
  exact ⟨D, a, _q, ha, hpa, hα, hβ, hb⟩

end AlgebraicGeometry
