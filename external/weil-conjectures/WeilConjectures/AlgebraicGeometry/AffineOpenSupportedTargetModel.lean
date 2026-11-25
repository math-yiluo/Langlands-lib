/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel

import WeilConjectures.AlgebraicGeometry.AffineOpenSupportedModelExists
import WeilConjectures.AlgebraicGeometry.AffineOpenSupportedModelTorsion

/-! # Supported target models on affine opens

Source: Stacks Project, Tags 06Z0, 08EB and 08EJ.
(blueprint: lem-sc-affine-open-supported-target-model).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- A supported quasi-coherent target has a power-torsion affine module preimage.
Source: Stacks Project, Tag 08EJ, affine paragraph, and Tag 06Z0.
(blueprint: lem-sc-affine-open-supported-target-model).

Proof: First shift the cohomology support hypothesis using the homology shift
isomorphism: every cohomology sheaf of E'[k] is isomorphic to a cohomology sheaf of E'.
Restriction to U and transport to its affine spectrum preserve quasi-coherence and
identify stalks. Apply the inverse affine derived equivalence to this shifted
restricted target, giving M and its counit isomorphism. The localized-site transport
and the comparison Q followed by F with explicit sheafification identify F(M) with
the restriction of E'[k]; extend the comparison from Q by its localization property.
Exactness identifies the associated sheaf of H^i(M) with the transported restricted
cohomology sheaf. All its stalks on D(f|U) vanish by the support hypothesis and the
zero-locus restriction formula. Thus its sections on D(f|U), the localization of
H^i(M) at f|U, are zero. The localization zero criterion gives, for each m, an n with
(f|U)^n m=0. No uniform exponent or finiteness of H^i(M) is claimed. For f=0 take n=1;
for a unit f the localization vanishing forces H^i(M)=0; the empty open is also
covered by the zero ring and zero module category. -/
theorem affine_open_supported_target_model
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (f : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (E' : schemeDerivedQCohCategory X)
    (hSupport : ∀ (i : ℤ) (x : X), x ∉ X.zeroLocus (U := ⊤) {f.val (op ⊤)} →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E'.obj).val.presheaf x)))
    (U : X.Opens) (hU : IsAffineOpen U) (k : ℤ) :
    let A := ↑(X.sheaf.obj.obj (op U))
    letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
      HasDerivedCategory.standard (ModuleCat.{u} A)
    let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    ∀ (F : DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))),
      Nonempty (DerivedCategory.Q ⋙ F ≅
        (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q) →
      ∃ M : DerivedCategory (ModuleCat.{u} A),
        (∀ (i : ℤ) (m : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M),
          ∃ n : ℕ, (f.val (op U)) ^ n • m = 0) ∧
        Nonempty (F.obj M ≅ R.obj (E'.obj⟦k⟧)) := by
  dsimp
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} (X.sheaf.obj.obj (op U))) :=
    HasDerivedCategory.standard _
  intro F hF
  obtain ⟨M, hM⟩ := affine_open_supported_model_exists X E' U hU k F hF
  have htor := affine_open_supported_model_torsion X f E' hSupport U hU k F hF M hM
  exact ⟨M, htor, hM⟩

end AlgebraicGeometry.Scheme
