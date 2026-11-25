/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.SupportedOpenPushforwardPerfectComponent
import WeilConjectures.AlgebraicGeometry.SupportedOpenPushforwardLocalComparisons
import WeilConjectures.AlgebraicGeometry.DerivedRestrictionIsIsoOpenCover

/-! # Perfect pushforward and canonical maps for supported open inclusions

Source: Stacks Project, Tags 08DP and 08DF
(blueprint: lem-pc-supported-open-pushforward).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- Let j = U.ι be the inclusion of an open subscheme and T ⊆ U closed in X.
(1) A perfect F on U supported on T has perfect derived direct image Rj_*F.
(2) For every E on X supported on T, the unit E → Rj_*(E|_U) of any adjunction between
derived restriction and Rj_* is invertible.
(3) For every such F, with j_! any left adjoint of derived restriction (extension by zero),
the canonical map j_!F → Rj_*F is invertible: it is the map φ whose adjunct
(j_!F)|_U → F is the inverse of the unit F → (j_!F)|_U, i.e. a left inverse of that unit.
Support means: every cohomology sheaf has zero stalk at every point off T.
Derived restriction is the over-site restriction followed by `Modules.overEquiv U`.

Source: Stacks Project, Tags 08DP and 08DF
(blueprint: lem-pc-supported-open-pushforward).

Proof:
1. Put V = X minus T. Since T ⊆ U, {U,V} covers X. For any supported G on U,
   G|_(U ∩ V) = 0. By lem-pc-restrict-derived-direct-image-open (Tag 08FE),
   (Rj_*G)|_V = 0 and (Rj_*G)|_U = G, and the unit restricts to the identity on U.
   Apply this with G = E|_U: both sides vanish on V, so the cone of E → Rj_*(E|_U)
   has zero cohomology on the cover, hence is zero. The map is invertible.
2. Extension by zero is exact and left adjoint to restriction
   (lem-sc-derived-open-restriction-adjunction-exact), computed termwise; its restrictions
   are F on U and 0 on V. The canonical map to Rj_*F is the identity on U and a map between
   zero objects on V. The same cone argument proves it invertible.
3. Perfectness is local (Tag 08CM). On U, Rj_*F is F and is perfect; on V it is zero,
   represented by the strictly perfect zero complex. Hence Rj_*F is perfect (Tag 08DP). -/
theorem supported_open_pushforward (X : Scheme.{u}) (U : X.Opens)
    (T : Set X) (hT : IsClosed T) (hTU : T ⊆ (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))] :
    (∀ F : schemeDerivedCategory U.toScheme, IsPerfect U.toScheme F →
      (∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj F).val.presheaf
            x))) →
      IsPerfect X ((schemeDerivedDirectImage U.ι).obj F)) ∧
    (∀ (adj : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
        (E : schemeDerivedCategory X),
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E).val.presheaf x))) →
      IsIso (adj.unit.app E)) ∧
    (∀ (adj : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
        (S : schemeDerivedCategory U.toScheme ⥤ schemeDerivedCategory X)
        (adjS : S ⊣ ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory)
        (F : schemeDerivedCategory U.toScheme), IsPerfect U.toScheme F →
      (∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj F).val.presheaf
            x))) →
      ∀ φ : S.obj F ⟶ (schemeDerivedDirectImage U.ι).obj F,
        adjS.unit.app F ≫ (adj.homEquiv (S.obj F) F).symm φ = 𝟙 F → IsIso φ) := by
  let V : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  have hcover : U ⊔ V = ⊤ := by
    ext x
    change (x ∈ U ∨ x ∈ Tᶜ) ↔ x ∈ (Set.univ : Set X)
    simp only [Set.mem_univ, iff_true]
    by_cases hx : x ∈ T
    · exact Or.inl (hTU hx)
    · exact Or.inr hx
  obtain ⟨hunit, hcanonical⟩ :=
    supported_open_pushforward_local_comparisons X U T hT V rfl
  refine ⟨supported_open_pushforward_perfect X U T hT hTU, ?_, ?_⟩
  · intro adj E hE
    exact derived_restriction_isIso_open_cover X U V hcover (adj.unit.app E)
      (hunit adj E hE U (Or.inl rfl)) (hunit adj E hE V (Or.inr rfl))
  · intro adj S adjS F hF hsupport φ hφ
    exact derived_restriction_isIso_open_cover X U V hcover φ
      (hcanonical adj S adjS F hsupport φ hφ U (Or.inl rfl))
      (hcanonical adj S adjS F hsupport φ hφ V (Or.inr rfl))

end AlgebraicGeometry.Scheme
