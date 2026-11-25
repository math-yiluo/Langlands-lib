/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Module sections transported along an isomorphism

Source: Stacks Project, Tags 01ZR, 0095, 0097 and 01I6.
(blueprint: new-module-sections-pullback-iso-transport).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Global sections of a pulled-back module transport along a scheme isomorphism.
Source: Stacks Project, Modules on Schemes Tags 0095, 0097 and 01I6.
(blueprint: new-module-sections-pullback-iso-transport).

Proof: Composition of module pullbacks identifies the pullback along g' with
pullback along h.hom of the module pulled back along g, using the equation hg.
For the isomorphism h, pullback of modules is pushforward along h.inv: both are
left adjoint to pushforward along h.hom, whose inverse is pushforward along h.inv.
The latter pushforward has, on the full open, the same additive group of sections
as the original module, with scalars restricted along h.inv.appTop. The full open
is preserved by inverse image. The two section ring maps induced by h.hom and
h.inv are inverse. Thus extension along h.hom.appTop cancels this restriction:
on tensors the map sends b tensor m to h.inv.appTop(b) acting on m; the inverse
sends m to 1 tensor m. The tensor relations and inverse laws follow from the two
inverse ring-map identities. Composing with the pullback-composition comparison
gives the asserted isomorphism. No quasi-coherence or affineness is used. Identity
isomorphisms give the identity scalar extension; zero rings and zero modules obey
the same tensor relations. -/
theorem nonempty_module_sections_pullback_iso_transport
    {S X Y : Scheme.{u}} (h : Y ≅ X) (g : X ⟶ S) (g' : Y ⟶ S)
    (hg : h.hom ≫ g = g') (M : S.Modules) :
    Nonempty ((ModuleCat.extendScalars (Scheme.Γ.mapIso h.op).hom.hom).obj
      (ModuleCat.of Γ(X, ⊤) Γ((Scheme.Modules.pullback g).obj M, ⊤)) ≅
        ModuleCat.of Γ(Y, ⊤) Γ((Scheme.Modules.pullback g').obj M, ⊤)) := by
  classical
  let N := (Scheme.Modules.pullback g).obj M
  let s := Scheme.Γ.mapIso h.op
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv s.commRingCatIsoToRingEquiv
  let es : ModuleCat.extendScalars s.hom.hom ≅ ModuleCat.restrictScalars s.inv.hom :=
    (ModuleCat.extendRestrictScalarsAdj s.hom.hom).leftAdjointUniq E.symm.toAdjunction
  let t : (Scheme.Modules.pullback h.hom).obj N ≅
      (Scheme.Modules.pushforward h.inv).obj N := by
    simpa using (Scheme.Modules.pullbackIsoPushforwardInv h.hom).app N
  let t' := (SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).mapIso t
  let k : (Scheme.Modules.pullback h.hom).obj N ≅
      (Scheme.Modules.pullback g').obj M :=
    (Scheme.Modules.pullbackComp h.hom g).app M ≪≫
      (Scheme.Modules.pullbackCongr hg).app M
  let k' := (SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).mapIso k
  refine ⟨es.app _ ≪≫ ?_ ≪≫ t'.symm ≪≫ k'⟩
  exact Iso.refl _

end AlgebraicGeometry
