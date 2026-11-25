/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSourceQuotientNormalization
import WeilConjectures.AlgebraicGeometry.SixFunctors.SheafKummerTransportAssembly
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalFiniteCartierNormalization

/-! # Kummer calculation of the simultaneously reduced Cartier boundary
Source: diagonal tower proof steps 5--7, Cartier unit proof paragraphs 4--5. -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] CategoryTheory.Abelian.Ext
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance 11000] kummerModuleHasExt kummerAbHasExt

attribute [local irreducible] normalizedBoundaryTarget DiagonalSourceNormalization
  DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ diagonalDerivedSingleCounit
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierEtaleKummerUnit cartierProKummerUnit cartierProIntegralGenerator cartierProRootMap
  cartierReducedEtale cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierResidueReducedPro diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary

/-- Once the source counit is invertible, Kummer reduction identifies the target
and the evaluated reduced boundary with the normalized finite Cartier classes.

Source: blueprint diagonal tower proof steps 5--7 and the Cartier unit proof
paragraphs 4--5; Stacks Tags 03PL, 0152 and 06YY
(blueprint: lem-sfb-diagonal-kummer-reduction).

Proof: use the supported integer/residue exact sequence to identify the ordinary
source quotients with supported finite constants. Their quotient generators
uniquely fix these isomorphisms and the adjunction-unit normalization. Compute
simultaneous reduction on one flat resolution. At level n compare it with the
two-term resolution [Z --ell^(n+1)--> Z], in degrees -1 and 0. Kummer exactness
on the etale site and exact comparison pullback identify its sole cohomology
on comparison units with the actual roots of unity. The transition between the
two-term resolutions is multiplication by ell in degree -1 and identity in
degree 0, so its cohomology transition is the power-ell map. The canonical finite
coefficient action gives the Z_l action through its residue projection. Thus
the degree -2 cohomology of the reduced shifted units is one strict system H,
whose underlying abelian tower is the roots tower. Good truncation gives the
system isomorphism b. Choose its sign to be the negative normalized Kummer
identification. This sign commutes with every transition.
Apply divisible-extension derived reduction to the pole extension, on both
sites. Its quotient-unit normalization gives the source comparison already
fixed above; its Kummer-unit normalization gives the negative of b. The pole
boundary in this item is also the negative of the short-exact-sequence boundary,
so these signs cancel. Exact inverse-image naturality and the common flat
resolution identify the evaluated morphism with the full finite Cartier class,
as a residue-linear derived morphism, before restriction to Z_l. This is the
class's defining supported-boundary construction, and therefore does not infer
equality merely from equality of its Chern composites. The root-to-line
comparison fixes t and its stated underlying-map equation. The source and
root comparisons together give precisely the level normalization asserted below.
No compatibility is reconstructed from independent level maps: all transitions
and the reduced boundary were already maps in the strict system category. -/
theorem diagonal_kummer_reduction (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (ha : a.hom = diagonalDerivedSingleCounit ℓ
      (diagonalScalarExtension ℓ (diagonalSurface Y)) D (diagonalIntegralSource Y)) :
    diagonalBoundaryTarget ℓ Y hY D a := by
  have hW : IsUnit (ℓ : Γ(diagonalSurface Y, ⊤)) := by
    simpa only [Nat.zero_add, Nat.pow_one] using diagonalSurface_power_unit ℓ Y hY 0
  unfold diagonalBoundaryTarget
  refine sheaf_kummer_transport_assembly ℓ (diagonalSurface Y) hW D
    (diagonalIntegralSource Y)
    (fun n => (lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))
      (diagonalImmersion Y)).obj
        (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y)))
    (fun n => cartierProIntegralGenerator (diagonalResidue.{u} ℓ n) (diagonalImmersion Y))
    (diagonalIntegralBoundary Y) a ha ?_ ?_ ?_
  · exact fun n => diagonal_source_quotient_normalization ℓ Y D.ordinary n
  · intro n s hs
    unfold DiagonalSourceNormalization at hs
    exact hs
  · exact fun n e he => diagonal_finite_cartier_normalization ℓ Y hY hW n e he

end AlgebraicGeometry.ProEtale
