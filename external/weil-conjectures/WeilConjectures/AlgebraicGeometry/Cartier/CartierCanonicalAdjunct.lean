/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSheafExt

/-! # Cartier adjunct uniqueness with shared canonical sheaf structures
Source: diagonal tower system proof, step (4).
(blueprint: lem-sfb-cartier-canonical-adjunct). -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] CategoryTheory.Abelian.Ext
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance 11000] kummerModuleHasExt kummerAbHasExt

attribute [local irreducible] DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ diagonalDerivedSingleCounit
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierEtaleKummerUnit cartierProKummerUnit cartierProIntegralGenerator cartierProRootMap
  cartierReducedEtale cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierResidueReducedPro diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary

/-- The existing uniquely characterized Cartier class, with canonical coefficient structures.
Source: the full Cartier scalar-adjunct characterization
(blueprint: lem-sfb-cartier-canonical-adjunct).
This is the existing unique class, with no additional witness choice. -/
def canonicalCartierClass (R : Type (u + 1)) [CommRing R] [Finite R]
    (n : ℕ) (hn : 0 < n) (hR : (n : R) = 0) {Z W : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hW : IsUnit (n : Γ(W, ⊤))) :
    Ext.{u + 1} ((lowerStar (ModuleCat.{u + 1} R) i).obj (geoCartierConstant R Z))
      (geoCartierLine R n hR W) 2 :=
  cartierReducedPro R n hn hR i hI hW

/-- Full Cartier-adjunct uniqueness with the named canonical sheaf structures.
Source: Cartier unit proof, full scalar-adjunct characterization
(blueprint: lem-sfb-cartier-canonical-adjunct).

Proof: the displayed equation is exactly CartierProReductionSpec, after unfolding
that predicate and cartierScalarBoundaryEquation. The pro-etale component of
cartierReduction_existsUnique identifies any such class with its unique witness.
That witness is cartierReducedPro and therefore canonicalCartierClass. All
coefficient-structure comparisons are performed for an arbitrary scheme W and
ring R, before specialization to the diagonal. -/
theorem canonical_cartier_class_of_adjunct (R : Type (u + 1)) [CommRing R] [Finite R]
    (n : ℕ) (hn : 0 < n) (hR : (n : R) = 0) {Z W : Scheme.{u}}
    (i : Z ⟶ W) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hW : IsUnit (n : Γ(W, ⊤)))
    (e : Ext.{u + 1}
      ((lowerStar (ModuleCat.{u + 1} R) i).obj (geoCartierConstant R Z))
      (geoCartierLine R n hR W) 2)
    (he : (Ext.mk₀ (cartierProIntegralGenerator R i)).comp
      (e.mapExactFunctor (cartierForget R W)) (zero_add 2) =
      (cartierProBoundary i (Etale.cartierPoleBoundary i hI)).comp
        (cartierProKummerUnit R n hR W hn hW) rfl) :
    e = canonicalCartierClass R n hn hR i hI hW := by
  have hspec : CartierProReductionSpec R n hR i hI hn hW e := by
    unfold CartierProReductionSpec cartierScalarBoundaryEquation
    exact he
  unfold canonicalCartierClass cartierReducedPro
  exact (Classical.choose_spec (cartierReduction_existsUnique R n hn hR i hI hW).2).2
    e hspec

end AlgebraicGeometry.ProEtale
