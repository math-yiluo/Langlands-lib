/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.AffineFlatModuleStalkFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Tensor flatness from flat sections on all affine subopens

Source: Stacks Project, Tags 05NE, 00H9 and 00HT.
(blueprint: lem-pc-affine-flat-module-tensor-flat).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Stalkwise tensor exactness detects sheaf tensor exactness (Stacks, Tag 05NE). -/
private theorem isFlat_of_flat_stalks (X : RingedSpace.{u}) (F : RingedSpace.Modules X)
    (hflat : ∀ x : X, Module.Flat (X.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor X x).obj F)) : SheafOfModules.IsFlat F := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  let T := MonoidalCategory.tensorRight F
  have : T.Additive := inferInstance
  have hex : ∀ C : ShortComplex (RingedSpace.Modules X),
      C.Exact → (C.map T).Exact := by
    intro C hC
    apply ((RingedSpace.module_stalk_exact X (T.map C.f)).2.2.2.2
      _ _ _ _).mpr
    intro x
    let S := RingedSpace.moduleStalkFunctor X x
    have : S.PreservesZeroMorphisms := inferInstance
    have : Module.Flat (X.presheaf.stalk x) (S.obj F) :=
      hflat x
    have hs : (C.map S).Exact :=
      ((RingedSpace.module_stalk_exact X C.f).2.2.2.2
        _ _ _ _).mp hC x
    obtain ⟨Φ, _, hΦ⟩ := SheafOfModules.stalkTensorIso X x
    let e : T ⋙ S ≅ S ⋙ MonoidalCategory.tensorRight (S.obj F) :=
      NatIso.ofComponents (fun A ↦ Φ A F) (by
        intro A A' f
        dsimp [T, S]
        have hn := hΦ A F A' F f (𝟙 F)
        have hi : S.map (𝟙 F) = 𝟙 (S.obj F) := S.map_id F
        rw [hi, MonoidalCategory.tensorHom_id] at hn
        exact hn)
    exact ShortComplex.exact_of_iso (C.mapNatIso e.symm)
      (Module.Flat.rTensor_shortComplex_exact (S.obj F) (C.map S) hs)
  have : T.PreservesHomology := Functor.preservesHomology_of_map_exact T hex
  change Limits.PreservesFiniteLimits T ∧ Limits.PreservesFiniteColimits T
  exact ⟨Functor.preservesFiniteLimits_of_preservesHomology T,
    Functor.preservesFiniteColimits_of_preservesHomology T⟩


set_option backward.isDefEq.respectTransparency false in
/-- Affine-local flatness over the identity implies tensor-exact sheaf flatness.
Source: Stacks Project, Modules, Tag 05NE; flatness and filtered colimits, Tag 00H9.
(blueprint: lem-pc-affine-flat-module-tensor-flat).

Proof: Fix a point x and an affine neighbourhood V. For every affine neighbourhood
U of x contained in V, the hypothesis makes G(U) flat over O(V), with scalars
restricted along O(V) -> O(U). These U form a filtered neighbourhood basis.
Their filtered colimit is G_x as an O(V)-module, so it is flat over O(V).
The stalk ring O_x is the localization of O(V) at the prime of x. Since G_x is
already an O_x-module, localization of G_x over O(V) is canonically G_x itself.
Base change of a flat module is flat; thus G_x is flat over O_x. Tensor products
of module sheaves have the corresponding tensor products as stalks. Tensoring
any short exact sequence with G is therefore exact on every stalk, and hence
exact as a sequence of sheaves. Tensoring also preserves finite colimits by its
right exactness, giving the stated exact functor. No quasi-coherence is used:
the hypothesis controls all affine subopens, not just the sections over V.
The empty scheme has no stalks and its module category is trivial; the zero
sheaf satisfies the same argument. -/
theorem isFlat_of_affineFlatOver_identity {Y : Scheme.{u}} (G : Y.Modules)
    (hflat : Scheme.Modules.IsFlatOver G (𝟙 Y)) : SheafOfModules.IsFlat G := by
  exact isFlat_of_flat_stalks Y.toRingedSpace G
    (flat_stalk_of_affineFlatOver_identity G hflat)

end AlgebraicGeometry
