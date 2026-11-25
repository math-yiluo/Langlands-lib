/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Lifting finite-free sheaf complexes on an affine scheme

(blueprint: lem-pc-affine-finite-free-sheaf-complex-lift)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
-- Elaborating the two equivalent module-category presentations needs extra heartbeats.
/-- A bounded-above finite-free sheaf complex on an affine scheme is the associated
sheaf complex of a bounded-above finite-free module complex.
Source: Stacks Project, Tag 08E7, converse proof; Tags 01I7 and 01IB.
(blueprint: lem-pc-affine-finite-free-sheaf-complex-lift).

Proof: Choose the rank of each term and the corresponding free module. The tilde
isomorphism for finite direct sums identifies its associated sheaf with that term.
Lift the differentials conjugated by these identifications using full faithfulness
of tilde. Faithfulness proves the shape and square-zero equations. The termwise
identifications form a complex isomorphism. The chosen modules are finite and free;
faithfulness reflects zero objects, so the same upper bound works. This also handles
rank zero and the zero ring without choosing an artificial rank above the bound. -/
theorem affine_finiteFree_sheaf_complex_lift (A : Type u) [CommRing A]
    (P : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hb : ∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i))
    (hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
      (R := moduleRings (Spec (.of A)).toRingedSpace) (ULift.{u} (Fin r)))) :
    ∃ E : CochainComplex (ModuleCat.{u} A) ℤ,
      ∃ b : ℤ, E.IsStrictlyLE b ∧
        (∀ j : ℤ, Module.Free A (E.X j) ∧ Module.Finite A (E.X j)) ∧
        Nonempty ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          _ _ _ _ (tilde.functor (.of A))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj E ≅ P) := by
  classical
  choose r hr using hfree
  let F : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) :=
    tilde.functor (.of A)
  let : F.Full := tilde.fullyFaithfulFunctor.full
  let : F.Faithful := tilde.fullyFaithfulFunctor.faithful
  let : F.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let X (i : ℤ) := ModuleCat.of A (ULift.{u} (Fin (r i)) →₀ A)
  let e (i : ℤ) : F.obj (X i) ≅ P.X i := tildeFinsupp _ ≪≫ (hr i).some.symm
  let d (i j : ℤ) : X i ⟶ X j := F.preimage ((e i).hom ≫ P.d i j ≫ (e j).inv)
  have hd (i j : ℤ) : F.map (d i j) = (e i).hom ≫ P.d i j ≫ (e j).inv :=
    F.map_preimage _
  let E : CochainComplex (ModuleCat.{u} A) ℤ :=
    { X := X
      d := d
      shape := by
        intro i j hij
        apply F.map_injective
        rw [hd, P.shape i j hij]
        simp
      d_comp_d' := by
        intro i j k _ _
        apply F.map_injective
        rw [Functor.map_comp, hd, hd]
        simp [Category.assoc] }
  let eC : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E ≅ P :=
    HomologicalComplex.Hom.isoOfComponents e (by
      intro i j _
      change (e i).hom ≫ P.d i j = F.map (d i j) ≫ (e j).hom
      rw [hd]
      simp)
  obtain ⟨b, hb⟩ := hb
  refine ⟨E, b, ?_, ?_, ⟨eC⟩⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    apply (IsZero.iff_id_eq_zero _).mpr
    apply F.map_injective
    rw [F.map_id, F.map_zero]
    exact ((e i).isZero_iff.mpr (hb i hi)).eq_of_src _ _
  · intro j
    exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry
