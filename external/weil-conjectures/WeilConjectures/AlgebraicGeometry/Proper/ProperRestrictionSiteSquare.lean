/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
import all WeilConjectures.AlgebraicGeometry.Sp.SpDirectImageEtaleMate
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarPullbackCube
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
import all WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-! # Restriction and the bounded direct-image site boundary

## References

* Stacks 09AF, 099R and 0D6E
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace CategoryTheory.Functor

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private theorem mate_whisker_top
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {G G' : C ⥤ E} {H : D ⥤ F}
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (w : TwoSquare G' L₁ L₂ H) (t : G ⟶ G') :
    mateEquiv a₁ a₂ (w.whiskerTop t) = (mateEquiv a₁ a₂ w).whiskerRight t := by
  simpa [TwoSquare.whiskerBottom, TwoSquare.whiskerLeft] using
    mateEquiv_whiskerTop_whiskerBottom a₁ a₂ w t (𝟙 H)

end AlgebraicGeometry.ProEtale
