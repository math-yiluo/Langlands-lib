/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.HomologicalComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# Termwise change of rings of a cochain complex

Source: Stacks Project, Cohomology on Sites, Tag 0G7E, coefficient-change specialization
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  {R S : Sheaf J CommRingCat.{max u v}} (φ : R ⟶ S)
  (K : CochainComplex (SheafOfModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)

private theorem changeOfRingsHom_zero
    (M N : SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) :
    changeOfRingsHom φ M (0 : M ⟶ N) = 0 := by
  unfold changeOfRingsHom
  rw [← Functor.map_zero]
  congr 1
  apply PresheafOfModules.hom_ext
  intro U
  change (ModuleCat.extendScalars (φ.hom.app U).hom).map ((0 : M ⟶ N).val.app U) = 0
  rw [show (0 : M ⟶ N).val.app U = 0 from rfl]
  exact Functor.map_zero _ _ _

private theorem changeOfRingsHom_comp
    {M N P : SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)}
    (a : M ⟶ N) (b : N ⟶ P) :
    changeOfRingsHom φ M (a ≫ b) =
      changeOfRingsHom φ M a ≫ changeOfRingsHom φ N b := by
  unfold changeOfRingsHom
  rw [← Functor.map_comp]
  congr 1
  apply PresheafOfModules.hom_ext
  intro U
  change (ModuleCat.extendScalars (φ.hom.app U).hom).map (a.val.app U ≫ b.val.app U) = _
  exact Functor.map_comp _ _ _

/-- The changed differentials have cochain shape. Source: Stacks, Tag 0G7E
(auxiliary; not a blueprint node).
Proof: outside the shape, K's differential is zero. Sectionwise extension of scalars
preserves zero, and so does the additive module sheafification functor. -/
theorem changeOfRingsComplex_shape (i j : ℤ) (h : ¬ (ComplexShape.up ℤ).Rel i j) :
    changeOfRingsHom φ (K.X i) (K.d i j) = 0 := by
  rw [K.shape i j h, changeOfRingsHom_zero]

/-- The changed differentials square to zero. Source: Stacks, Tag 0G7E
(auxiliary; not a blueprint node).
Proof: sectionwise extension of scalars and module sheafification preserve composition
and zero. Apply these identities to K.d_comp_d i j k. -/
theorem changeOfRingsComplex_comp (i j k : ℤ) :
    changeOfRingsHom φ (K.X i) (K.d i j) ≫
      changeOfRingsHom φ (K.X j) (K.d j k) = 0 := by
  rw [← changeOfRingsHom_comp, K.d_comp_d, changeOfRingsHom_zero]

/-- Apply the existing change of rings to every term and differential.
Source: Stacks, Tag 0G7E (auxiliary; not a blueprint node). -/
noncomputable def changeOfRingsComplex : CochainComplex (SheafOfModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj S)) ℤ where
  X i := changeOfRings φ (K.X i)
  d i j := changeOfRingsHom φ (K.X i) (K.d i j)
  shape := changeOfRingsComplex_shape φ K
  d_comp_d' i j k _ _ := changeOfRingsComplex_comp φ K i j k

end SheafOfModules
