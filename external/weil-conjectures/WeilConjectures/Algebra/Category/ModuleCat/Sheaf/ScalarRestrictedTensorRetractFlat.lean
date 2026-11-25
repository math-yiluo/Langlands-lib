/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # Tensoring a base-flat module with a finite free retract

Source: Stacks Project, Tags 03EU and 00HD, the retract argument in Tag 0DJQ.
(blueprint: lem-pc-scalar-restricted-tensor-retract-flat).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules

private theorem restrictScalars_preservesColimits
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R A : Sheaf J RingCat.{u}} (α : R ⟶ A)
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    PreservesColimitsOfSize.{u, u} (SheafOfModules.restrictScalars.{u} α) := by
  have h (B : Sheaf J RingCat.{u}) :
      PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} B) := by
    constructor
    intro K _
    exact ((moduleSheaves_colimits_forgetful B).2.2.2.2.2 K).2.1
  have := h R
  have := h A
  have : ReflectsColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} R) :=
    reflectsColimits_of_reflectsIsomorphisms
  have : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.restrictScalars.{u} α ⋙ SheafOfModules.toSheaf.{u} R) :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} A))
  exact preservesColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{u} R)




/-- Tensoring with a retract of a finite free module preserves flatness after
restriction of scalars; the algebra itself need not be flat over the base ring.
Source: Stacks Project, Tags 03EU and 00HD, applied to the tensor calculation of 0DJQ.
(blueprint: lem-pc-scalar-restricted-tensor-retract-flat).

Proof: tensor the given inclusion and retraction with N. Functoriality carries
ι ≫ π = identity to the same equation for P tensor N as a retract of A^m tensor N.
Restriction of scalars preserves this equation. The free module is the coproduct
of m copies of the tensor unit. Right tensoring preserves coproducts, and its unit
isomorphism identifies A^m tensor N with the coproduct of m copies of N. Restriction
of scalars leaves the underlying abelian sheaf unchanged and hence preserves
coproducts. Thus the resulting restricted free tensor is a finite coproduct of the
flat restricted module N, and is flat by Tag 03EU. Flatness passes to a retract:
its tensor functor is a retract of an exact tensor functor, so preserves exact
short complexes and thus finite limits and colimits. This proves the conclusion.
For m = 0 the ambient module is zero, so P is zero; the zero base ring, zero N and
empty site also satisfy the argument. No flatness assumption on A is used. -/
theorem isFlat_scalarRestricted_tensor_retract
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    {R A : Sheaf J CommRingCat.{u}} (α : R ⟶ A)
    (P N : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A))
    (m : ℕ)
    (ι : P ⟶ free (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A)
      (ULift.{u} (Fin m)))
    (π : free (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A)
      (ULift.{u} (Fin m)) ⟶ P)
    (h : ι ≫ π = 𝟙 P)
    (hN : IsFlat ((restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α)).obj N)) :
    letI := monoidalCategory A
    IsFlat ((restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α)).obj (P ⊗ N))  := by
  let := monoidalCategory A
  let := symmetricCategory A
  obtain ⟨⟨mpA⟩, ⟨mcA⟩, _⟩ := tensorClosed A
  let := mpA
  let := mcA
  let B := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map α
  let F := restrictScalars B
  have : PreservesColimitsOfSize.{u, u} F := restrictScalars_preservesColimits B
  let V := fun _ : ULift.{u} (Fin m) ↦ unit
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A)
  let T := tensorRight N
  let e₁ : free (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A)
      (ULift.{u} (Fin m)) ⊗ N ≅ ∐ (fun _ : ULift.{u} (Fin m) ↦ N) :=
    PreservesCoproduct.iso T V ≪≫ Sigma.mapIso (fun _ ↦ λ_ N)
  let e := F.mapIso e₁ ≪≫ PreservesCoproduct.iso F (fun _ : ULift.{u} (Fin m) ↦ N)
  have hf := isFlat_coproduct R (fun _ : ULift.{u} (Fin m) ↦ F.obj N) (fun _ ↦ hN)
  let := monoidalCategory R
  let := symmetricCategory R
  obtain ⟨⟨mpR⟩, ⟨mcR⟩, _⟩ := tensorClosed R
  let := mpR
  let := mcR
  have hf' : IsFlat (F.obj (free
      (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A)
      (ULift.{u} (Fin m)) ⊗ N)) :=
    (exactFunctor _ _).prop_of_iso ((tensoringRight _).mapIso e.symm) hf
  have hobj : ObjectProperty.flat (F.obj (free
      (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A)
      (ULift.{u} (Fin m)) ⊗ N)) := by
    have : PreservesFiniteLimits (tensorRight (F.obj (free
        (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A)
        (ULift.{u} (Fin m)) ⊗ N))) := hf'.1
    apply (ObjectProperty.flat_iff_preservesFiniteLimits _).2
    exact preservesFiniteLimits_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight _).symm
  exact (ObjectProperty.flat_of_retract
    ⟨F.map (T.map ι), F.map (T.map π), by
      rw [← F.map_comp, ← T.map_comp, h, T.map_id, F.map_id]⟩ hobj).2


end SheafOfModules
