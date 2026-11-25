/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.SchemeIsoPerfectLocalTransport

/-! # Perfect objects under scheme isomorphisms

Source: Stacks Project, perfect.tex, Tag 08EB, transport along an affine isomorphism
(blueprint: lem-pc-scheme-iso-perfect-transport).
-/

@[expose] public section

universe u w₁ w₂

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The inverse of a derived equivalence induced by an isomorphism of schemes preserves
perfect objects.
Source: Stacks Project, perfect.tex, Tag 08EB, affine isomorphism transport
(blueprint: lem-pc-scheme-iso-perfect-transport).

Proof: The localization comparison identifies the forward functor with exact pushforward
along s.hom. Its inverse is consequently isomorphic to exact pushforward along s.inv,
by the pushforward composition and identity comparisons and uniqueness of localization.
For a point of X, transport a perfect neighbourhood of its image in Y
to its inverse-image open in X. The induced
localized-site equivalence commutes with restriction, including the localization
comparisons for the independently chosen derived categories. This equivalence identifies
the structure module and finite free modules, preserves retractions by functoriality,
and preserves zero objects. It therefore transports a strictly perfect local complex
with the same degree bounds and ranks. Applying the exact derived functor to the local
model isomorphism gives the required model of e.inverse.obj E. No affineness,
boundedness of E in advance, nonemptiness, or relation between w₁ and w₂ is needed. -/
theorem scheme_iso_derived_inverse_preserves_perfect {X Y : Scheme.{u}}
    (s : X ≅ Y)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w₁} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ V : Y.Opens,
      HasDerivedCategory.{w₂} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))]
    (e : schemeDerivedCategory X ≌ schemeDerivedCategory Y)
    (he : DerivedCategory.Q ⋙ e.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (E : schemeDerivedCategory Y) (hE : IsPerfect Y E) :
    IsPerfect X (e.inverse.obj E) := by
  intro x
  rcases hE (s.hom.base x) with ⟨V, hx, K, hK, hIso⟩
  exact scheme_iso_local_perfect_transport s e he E x V hx K hK hIso

end AlgebraicGeometry.Scheme
