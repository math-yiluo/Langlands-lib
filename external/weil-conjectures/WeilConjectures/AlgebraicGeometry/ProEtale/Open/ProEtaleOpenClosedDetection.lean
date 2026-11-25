/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-!
# Detection by open and closed pro-etale restrictions

## References

* Stacks Project, Tag 09AH
* Stacks, Modules on Sites
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Extension along the coefficient isomorphism reflects vanishing, by its existing
scalar-transport equivalence and tensor-extension adjunction. -/
private theorem inverseImage_isZero_of_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M : proEtaleRingModules Y R)
    (h : IsZero ((proEtaleRingModulePullback f R S c).obj M)) :
    IsZero ((proEtaleModuleInverseImage f R).obj M) := by
  let rc := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c
  let e := proEtaleScalarEquivalence X rc
  let adj := proEtaleRingExtensionAdjunction f R S c
  let t := adj.leftAdjointUniq e.symm.toAdjunction
  have hz : IsZero (e.inverse.obj ((proEtaleModuleInverseImage f R).obj M)) :=
    h.of_iso (t.app _).symm
  exact (e.functor.map_isZero hz).of_iso (e.counitIso.app _).symm

/-- A module over arbitrary commutative ring-sheaf coefficients is zero if its pullbacks
along a closed immersion and its complementary quasi-compact open immersion are zero.
The coefficient isomorphisms are specified, and pullback uses the recorded tensor extension. -/
theorem proEtaleRingModule_isZero_of_open_closed
    {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (Ri : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (Rj : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (ci : (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R ≅ Ri)
    (cj : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ Rj)
    (F : proEtaleRingModules X R)
    (hj : IsZero ((proEtaleRingModulePullback j R Rj cj).obj F))
    (hi : IsZero ((proEtaleRingModulePullback i R Ri ci).obj F)) : IsZero F := by
  have hi' := inverseImage_isZero_of_pullback i R Ri ci F hi
  have hj' := inverseImage_isZero_of_pullback j R Rj cj F hj
  let V := ProEt.mk j
  have : IsOpenImmersion V.hom := ‹IsOpenImmersion j›
  have : QuasiCompact V.hom := ‹QuasiCompact j›
  obtain ⟨q, ⟨e⟩, ai, aj, _, _, _, _, _, _, _, _, hs, _⟩ :=
    proEtale_ringed_open_closed i V hU R
  have ho : IsZero ((SheafOfModules.overFunctor.{u + 1}
      (proEtaleModuleCoefficients R) V).obj F) :=
    (q.functor.map_isZero hj').of_iso (e.app F).symm
  have : (proEtaleRingedExtensionByZero V R).IsLeftAdjoint := aj.isLeftAdjoint
  have : (proEtaleRingedDirectImage i R).IsRightAdjoint := ai.isRightAdjoint
  let T := ComposableArrows.mk₂ (aj.counit.app F) (ai.unit.app F)
  have hT : T.Exact := (hs F).2.2
  have he := (T.exact₂_iff hT.toIsComplex).1 hT
  exact he.isZero_of_both_isZero
    ((proEtaleRingedExtensionByZero V R).map_isZero ho)
    ((proEtaleRingedDirectImage i R).map_isZero hi')

end AlgebraicGeometry.Scheme
