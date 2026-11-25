/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageAffineTruncationComparison
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Derived direct image preserves quasi-coherent cohomology

Source: literature/stacks-project/perfect.tex, Tag 08D5,
part (1) (blueprint: lem-pc-derived-direct-image-preserves-qcoh).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- For a quasi-compact and quasi-separated morphism of schemes, derived direct image
preserves the full subcategory of complexes with quasi-coherent cohomology.
Source: literature/stacks-project/perfect.tex, Tag 08D5,
part (1) (blueprint: lem-pc-derived-direct-image-preserves-qcoh).
Proof:
1. For every degree q and affine open U of Y, use
   exists_isIso_schemeHigherDirectImage_truncGE_over_affine to replace E by
   a sufficiently low canonical truncation in the restricted higher direct image.
2. The quasi-coherent property contains zero: the free sheaf on no generators
   has zero identity, by freeHomEquiv, and is quasi-coherent. Consequently
   DerivedCategory.homologyProperty_truncGE gives quasi-coherent cohomology of
   the truncation. It is bounded below by the standard t-structure.
3. Apply schemeDerivedDirectImage_preserves_QCoh_of_isGE to this truncation.
   Restrict its quasi-coherent q-th higher direct image using
   SheafOfModules.isQuasicoherent_over, and transport the property through the
   inverse of the canonical comparison isomorphism.
4. The affine opens cover Y. SheafOfModules.IsQuasicoherent.of_coversTop gives
   global quasi-coherence in degree q; quantify over all integers q.
(blueprint: lem-pc-derived-direct-image-preserves-qcoh). -/
theorem schemeDerivedDirectImage_preserves_QCoh
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∀ E : schemeDerivedCategory X,
      schemeDerivedQCohProperty X E →
        schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E) := by
  intro E hE q
  have hzero : CategoryTheory.Limits.IsZero
      (SheafOfModules.free (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}) := by
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  have : (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).ContainsZero :=
    ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free
      (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}⟩⟩
  let M := (schemeHigherDirectImage f q).obj E
  have hU : ∀ U : Y.affineOpens, (M.over U.1).IsQuasicoherent := by
    intro U
    obtain ⟨n, hn⟩ :=
      exists_isIso_schemeHigherDirectImage_truncGE_over_affine f E hE q U
    let K := (DerivedCategory.TStructure.t.truncGE (-n)).obj E
    have hK : schemeDerivedQCohProperty X K := by
      apply DerivedCategory.homologyProperty_truncGE hE
    have hK' := schemeDerivedDirectImage_preserves_QCoh_of_isGE f K hK (-n)
    have hQ : ((schemeHigherDirectImage f q).obj K).IsQuasicoherent := hK' q
    have hQover := SheafOfModules.isQuasicoherent_over
      ((schemeHigherDirectImage f q).obj K) U.1
    let e := asIso
      ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U.1).map
        ((schemeHigherDirectImage f q).map
          ((DerivedCategory.TStructure.t.truncGEπ (-n)).app E)))
    exact (SheafOfModules.isQuasicoherent ((moduleRings Y.toRingedSpace).over U.1)).prop_of_iso
      e.symm hQover
  have : ∀ U : Y.affineOpens, (M.over U.1).IsQuasicoherent := hU
  exact SheafOfModules.IsQuasicoherent.of_coversTop M (fun U : Y.affineOpens => U.1)
    ((Opens.coversTop_iff _ _).mpr (iSup_affineOpens_eq_top Y))

end AlgebraicGeometry
