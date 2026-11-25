/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.SingleSupportedFiniteFreeHomologyIso
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # The one-column finite free Hom calculation

Source: Stacks Project, Tags 0A6H (2) and 08I5.
(blueprint: lem-sc-single-supported-finite-free-hom-qc)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

private theorem qc_overEquiv (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U)) (hM : M.IsQuasicoherent) :
    ((Scheme.Modules.overEquiv U).functor.obj M).IsQuasicoherent := by
  let := hM
  have : ∀ W, (Over.post (X := W) U.overEquivalence.symm.functor).IsContinuous
      ((Opens.grothendieckTopology ↥U).over W)
      (((Opens.grothendieckTopology X).over U).over _) := fun W ↦
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous U.overEquivalence.symm.functor _ _).overPost W)
  apply SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
    (U.overEquivalence.symm.functor) _
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf)

private theorem qc_overEquiv_inverse (X : Scheme.{u}) (U : X.Opens)
    (M : U.toScheme.Modules) (hM : M.IsQuasicoherent) :
    ((Scheme.Modules.overEquiv U).inverse.obj M).IsQuasicoherent := by
  let := hM
  have : ∀ W, (Over.post (X := W) U.overEquivalence.functor).IsContinuous
      (((Opens.grothendieckTopology X).over U).over W)
      ((Opens.grothendieckTopology ↥U).over _) := fun W ↦
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous U.overEquivalence.functor _ _).overPost W)
  apply SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
    (U.overEquivalence.functor) _
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf)

set_option backward.isDefEq.respectTransparency true in
/-- A one-column source gives shifts of finite sums of target cohomology.

Source: Stacks Project, Tag 08I5, Hom double-complex calculation, and Tag 0A6H (2).
Proof: the product defining Hom has zero factors except for the source degree k.
The surviving factor is Hom(E^k,I^(k+n)); the source differential vanishes.
Choose the finite-free identification of E^k and evaluate on its basis to identify
this factor, naturally in the target, with r copies of I^(k+n). The differential
is r copies of the target differential, so H^n is r copies of H^(k+n)(I).
Finite sums commute with homology in the abelian category of module sheaves.
Transport to the open subscheme by its exact localized-site equivalence, use finite
sum closure of quasi-coherence there, and transport back. If r=0 all terms are zero;
no boundedness of I is used.
(blueprint: lem-sc-single-supported-finite-free-hom-qc). -/
theorem single_supported_finiteFree_hom_qc
    (X : Scheme.{u}) (U : X.Opens)
    (E I : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (k : ℤ) (hE : ∀ i : ℤ, i ≠ k → IsZero (E.X i))
    (hfree : ∃ r : ℕ, Nonempty (E.X k ≅ SheafOfModules.free
      (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r))))
    (hI : ∀ i : ℤ, (I.homology i).IsQuasicoherent) (n : ℤ) :
    ((homComplex (R := X.toRingedSpace.sheaf.over U) E I).homology n).IsQuasicoherent := by
  obtain ⟨r, ⟨hf⟩⟩ := hfree
  obtain ⟨eH⟩ := single_supported_finiteFree_homology_iso X U E I k hE r hf n
  let F := (Scheme.Modules.overEquiv U).functor
  let M := I.homology (k + n)
  have hM : (F.obj M).IsQuasicoherent := qc_overEquiv X U M (hI (k + n))
  have hsum : (∐ (fun _ : ULift.{u} (Fin r) ↦ F.obj M)).IsQuasicoherent :=
    @Scheme.Modules.isQuasicoherent_sigma U.toScheme _
      (fun _ : ULift.{u} (Fin r) ↦ F.obj M) (fun _ ↦ hM)
  have hF : (F.obj (∐ (fun _ : ULift.{u} (Fin r) ↦ M))).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      (PreservesCoproduct.iso F (fun _ : ULift.{u} (Fin r) ↦ M)).symm hsum
  have hback := qc_overEquiv_inverse X U _ hF
  have hsource : (∐ (fun _ : ULift.{u} (Fin r) ↦ M)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent ((moduleRings X.toRingedSpace).over U)).prop_of_iso
      ((Scheme.Modules.overEquiv U).unitIso.app _).symm hback
  exact (SheafOfModules.isQuasicoherent ((moduleRings X.toRingedSpace).over U)).prop_of_iso
    eH.symm hsource

end AlgebraicGeometry
