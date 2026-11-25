/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Algebra.Homology.OpenCoverMateModuleShortExactCore
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # The module-level open-cover sequence with its canonical mate maps

Source: Stacks Project, Tag 08BU, proof, and Tag 00A7 (extension by zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace SheafOfModules

/-- The canonical mate sequence for a single module sheaf is short exact.
The caller supplies a proof that the displayed composite is zero.

Source: Stacks Project, Cohomology, Tag 08BU (the short exact sequence in the
proof), and Tag 00A7 (extension-by-zero adjunction and stalks).
(blueprint: lem-sc-open-cover-mate-module-short-exact).

Proof: Use the extension-by-zero functors constructed by extensionByZeroPresheaf
followed by module sheafification. Their adjunctions exist by the exact localized
module adjunction. For these adjunctions, the transition maps of
module_extensionByZero_stalk_maps are precisely the displayed transposes.
Both transition maps composed with the respective counit equal the overlap
counit, so the difference lift composed with the counit sum is zero.
At a point in both opens, the stalk-map comparison identifies the sequence with
m ↦ (m, -m), (m, n) ↦ m + n. The first map is injective, a pair in the
kernel of the second is (m, -m), and y lifts to (y, 0).
At a point in exactly one open, the overlap stalk
and the other summand vanish and the remaining counit is an isomorphism.
The covering assumption excludes any point in neither open. The stalk sequences
are short exact. Reflect exactness by module_stalk_exact; reflect mono and epi
using the faithful family of stalk functors (or the stalks of kernel and
cokernel). Thus the sequence of module sheaves is short exact.
For the chosen adjunctions aU, aV, aW, use leftAdjointUniq to transport the
canonical sequence. Its compatibility with units, counits, and Hom equivalences
identifies the transported maps with the displayed formulas. Transport short
exactness along the resulting short-complex isomorphism. The same argument
includes empty and equal opens, and the zero module; it needs no complexes. -/
theorem open_cover_mate_module_shortExact (X : AlgebraicGeometry.RingedSpace.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (hR : R = (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
    (U V : Opens X) (hcover : U ⊔ V = ⊤)
    [(overFunctor.{u} R U).Additive] [(overFunctor.{u} R V).Additive]
    [(overFunctor.{u} R (U ⊓ V)).Additive]
    (SU : SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} R)
    (SV : SheafOfModules.{u} (R.over V) ⥤ SheafOfModules.{u} R)
    (SW : SheafOfModules.{u} (R.over (U ⊓ V)) ⥤ SheafOfModules.{u} R)
    [SU.Additive] [SV.Additive] [SW.Additive]
    (aU : SU ⊣ overFunctor.{u} R U) (aV : SV ⊣ overFunctor.{u} R V)
    (aW : SW ⊣ overFunctor.{u} R (U ⊓ V))
    (F : SheafOfModules.{u} R) :
    let cU := overFunctorMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)
    let cV := overFunctorMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)
    let iU := (aW.homEquiv _ _).symm
      (cU.inv.app F ≫
        (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)).map
          (aU.unit.app ((overFunctor.{u} R U).obj F)) ≫
        cU.hom.app (SU.obj ((overFunctor.{u} R U).obj F)))
    let iV := (aW.homEquiv _ _).symm
      (cV.inv.app F ≫
        (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)).map
          (aV.unit.app ((overFunctor.{u} R V).obj F)) ≫
        cV.hom.app (SV.obj ((overFunctor.{u} R V).obj F)))
    ∀ hz : biprod.lift iU (-iV) ≫
        biprod.desc (aU.counit.app F) (aV.counit.app F) = 0,
      (ShortComplex.mk (biprod.lift iU (-iV))
        (biprod.desc (aU.counit.app F) (aV.counit.app F)) hz).ShortExact := by
  dsimp
  intro hz
  obtain ⟨hU, hV⟩ := open_cover_mate_module_counit_compatibility X R hR U V hcover
    SU SV SW aU aV aW F
  exact open_cover_mate_module_shortExact_core X R hR U V hcover SU SV SW aU aV aW F
    _ _ hU hV hz

end SheafOfModules
