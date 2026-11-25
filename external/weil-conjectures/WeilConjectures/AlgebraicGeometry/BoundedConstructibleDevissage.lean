/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback

/-! # Finite truncation dévissage for constructible module objects

This is the standard t-structure induction from blueprint
`proposition-six-operations-dctf--14`, step 10. It is independent of coefficient finiteness:
only the target property is required to be triangulated.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open DerivedCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Boundedness and constructible homology are invariant under isomorphism. -/
instance isClosedUnderIsomorphisms_boundedConstructibleModule
    {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    (boundedConstructible R).IsClosedUnderIsomorphisms where
  of_iso e h := ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e h.1,
    fun n ↦ _root_.constructible_of_iso (R := R)
      ((homologyFunctor _ n).mapIso e) (h.2 n)⟩

/-- A bounded complex with constructible homology sheaves lies in every triangulated
subcategory of the derived module-object category, closed under isomorphisms, containing
the constructible sheaves placed in degree `0`. This is the generic derived-category
truncation theorem specialized to constructible module objects.
(auxiliary; not a blueprint node) -/
lemma prop_of_boundedConstructibleModule {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    (P : ObjectProperty
      (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hP : ∀ F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R,
      IsConstructibleModuleObject R F →
      P ((singleFunctor _ 0).obj F))
    {K : _root_.DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)}
    (hK : boundedConstructible R K) : P K := by
  let Q : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :=
    fun F ↦ IsConstructibleModuleObject R F
  have : Q.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ _root_.constructible_of_iso (R := R) e h⟩
  exact DerivedCategory.prop_of_bounded P Q hP K hK.1 hK.2

end AlgebraicGeometry.ProEtale
