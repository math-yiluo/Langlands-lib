/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumCompositionCounit
import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportSumCompositorComponent

/-! # Support and sum compositors under the constructed graph comparison

Source: Stacks Project, More on Etale Cohomology, Tags 0F7J, 0F7K and 0F50.
(blueprint: lem-pur-etale-support-sum-compositor).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The actual proper/open compositor becomes nested sum composition under the graph maps.
Source: Stacks Project, Tags 0F7J, 0F7K and 0F50; Step 1 of
lem-pur-etale-normalized-mates-composition-pasting.
(blueprint: lem-pur-etale-support-sum-compositor).

Proof: Use the actual section-preserving support construction in the proof of
quasifiniteCompactSupportExact, with its normalized compactification units, rather than
arbitrary witnesses of that theorem's existential conclusion. Its graph-normalized etale
identifications identify the sheaf comparison maps with the canonical graph maps: cancel
the monic compactification inclusion in direct image. The homotopy-localization formulas
then identify the corresponding derived comparisons with
canonicalEtaleCompactSupportComparison. The nested-summand calculation sends each pair
of lifts to its composite lift, with the prescribed Over.mapComp restriction. The
sum/restriction adjunction bijection therefore identifies the resulting sheaf compositor
with etaleSumSheafCompIso. Apply exactCompactificationUnit_composition to these exact
support functors, their normalized sheaf factorizations, and their inverse derived units.
It identifies the specified unbounded proper/open compositor with the exact descent of
that sheaf compositor. Substitute the graph identifications and use the exact-functor
composition comparison to identify this descent with derivedEtaleSumCompIso. Finally the
every-tower formula for unboundedEtaleLowerShriekCompIso and the comparison cocycle
transport the equation to c,d,k. Naturality puts the two graph comparisons in horizontal
order. The same adjunction bijection covers identities, empty schemes and zero coefficients. -/
theorem etaleSupportSumCompositor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X T : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian T]
    (e : U ⟶ X) (v : X ⟶ T)
    [Etale e] [Etale v] [IsSeparated e] [IsSeparated v]
    [QuasiCompact e] [QuasiCompact v]
    (c : Compactification e) (d : Compactification v) (k : Compactification (e ≫ v)) :
    (Functor.isoWhiskerRight
        (rightDerivedLowerShriekOfCompactificationIso A c (k.ofComp d).restrict) _ ≪≫
      rightDerivedLowerShriekOfCompactificationCompIso A d (k.ofComp d) ≪≫
      rightDerivedLowerShriekOfCompactificationIso A (d.comp (k.ofComp d)) k).hom ≫
        (canonicalEtaleCompactSupportComparison A (e ≫ v) k).hom =
      NatTrans.hcomp (canonicalEtaleCompactSupportComparison A e c).hom
          (canonicalEtaleCompactSupportComparison A v d).hom ≫
        (derivedEtaleSumCompIso A e v).hom := by
  ext M
  exact etaleSupportSumCompositor_app A e v c d k M

end AlgebraicGeometry.Etale
