/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.ProperBaseChange.OrdinaryRingedToposPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.Algebra.Homology.ProperBaseChange.ElementSectionModuleRestriction
import WeilConjectures.Algebra.Homology.ProperBaseChange.RepresentableSliceModulePullback

/-! # Transport of a local finite generating family along a generalized section

Source: Stacks Project, Modules on Sites, Tags 03DO (5), 03DF, and 04IF.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite

namespace SheafOfModules

/-- A section of the inverse image of a represented localization transports generators.

Source: Stacks Project, Modules on Sites, Tags 03DO (5), 03DF, and 04IF.
(blueprint: lem-weil-pbc-ringed-topos-pullback-local-generators).

Proof: Put H = h_U^#. The equivalence between sheaves on D/U and the topos slice
Sh(D)/H identifies the restriction of M and the finite free epimorphism defined by
σ with their restrictions to H. Localize f at H. The ringed slice comparison
identifies the ordinary pullback of this restricted module with the restriction of
the ordinary pullback to f inverse H. Pullback on the slices is a left adjoint, so
it preserves epimorphisms and finite coproducts. The tensor-unit isomorphism
S tensor_R R = S identifies the pullback of a free module of rank σ.I with a free
module of that same rank. Pull back σ.π using this isomorphism. The section t
specifies a map h_V^# to f inverse H. Restrict the resulting finite free quotient
along it. Restriction is exact and carries the unit and finite sums to the unit
and finite sums. Finally identify the element-site object slice at (V,t) with C/V:
both evaluate the target at an arrow W to V as the original module at W, with
the same ring and restriction maps. The resulting epimorphism from a finite free
module gives the asserted generating sections via freeHomEquiv. Only the one
chosen source localization and the one generalized section occur; no cover or
local finite-type assumption on M is required. Empty generating families are
carried to the zero quotient, and no flatness is used. -/
theorem ordinaryRingedToposPullback_localGenerators
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (RI : Sheaf J CommRingCat.{u}) (I : AlgebraicInverseImage f.inverse B RI)
    (c : RI ⟶ A)
    (hc : I.ringUnderlying.hom ≫ (sheafCompose J (CategoryTheory.forget CommRingCat)).map c =
      f.ringMap)
    (M : ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (U : D) (σ : (M.over U).GeneratingSections) [σ.IsFiniteType]
    (V : C)
    (t : (f.inverse.obj ((presheafToSheaf K (Type u)).obj (yoneda.obj U))).obj.obj (op V)) :
    ∃ τ : ((ordinaryRingedToposPullback I c M).over V).GeneratingSections,
      τ.IsFiniteType := by
  obtain ⟨F, hF, ⟨eF⟩, hFM⟩ :=
    representableSliceModulePullback_exists A B f RI I c hc U
  let := hF
  let σF := σ.map F eF
  obtain ⟨G, hG, ⟨eG⟩, hGQ⟩ := elementSectionModuleRestriction_exists
    A
    (f.inverse.obj ((presheafToSheaf K (Type u)).obj (yoneda.obj U))) V t
  let := hG
  let σG := σF.map G eG
  obtain ⟨α⟩ := hFM M
  obtain ⟨β⟩ := hGQ (ordinaryRingedToposPullback I c M)
  let γ := G.mapIso α ≪≫ β
  exact ⟨σG.ofEpi γ.hom, inferInstance⟩

end SheafOfModules
