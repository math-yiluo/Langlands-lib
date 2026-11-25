/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.SupportedPerfectDetectorAffineConstruction
import WeilConjectures.AlgebraicGeometry.SupportedDerivedRestrictionZero
import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine supported zero detection
Source: Stacks Project, Tag 0A9A, affine case.
(blueprint: lem-pc-supported-perfect-detector-affine).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The affine Koszul argument, including the empty scheme, detects zero objects supported
on a closed subset when an affine cover has at most one member.
Source: Stacks Project, Tag 0A9A, affine paragraph, and Tag 09IR.
(blueprint: lem-pc-supported-perfect-detector-affine).

Proof:
1. If the cover is empty, its union is empty, so X has no points. Every module sheaf
   and every derived object is zero. Take the strictly perfect zero complex.
2. Otherwise the cover has one member, which equals X. Thus X is affine. Identify X
   with Spec A by the canonical affine presentation. Quasi-compactness of X minus T
   gives finitely many functions f_i whose principal opens cover that complement.
3. Sheafify the actual finite Koszul complex on these functions and localize it.
   It is perfect and has quasi-coherent cohomology. Each f_i acts null-homotopically,
   so its cohomology stalks vanish off their common zero locus T (Tag 0663).
4. For a quasi-coherent K supported on T and orthogonal to every shift of this complex,
   apply koszul_open_orthogonality with the affine chart equal to X and open X minus T.
   The restriction of K to this open is zero: its cohomology sheaves have zero stalks
   there. The canonical unit therefore identifies K with derived pushforward of zero.
   A right adjoint preserves zero, so K is zero. The same calculation handles T empty
   (the Koszul complex is acyclic) and T equal to X (the empty Koszul tuple). -/
theorem supported_perfect_detector_affine
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (s : Finset X.affineOpens) (hcover : (⨆ U ∈ s, (U : X.Opens)) = ⊤)
    (hcard : s.card ≤ 1) (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ) :
    ∃ E : schemeDerivedQCohCategory X, Scheme.IsPerfect X E.obj ∧
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E.obj).val.presheaf x))) ∧
      ∀ K : schemeDerivedQCohCategory X,
        (∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K.obj).val.presheaf x))) →
        (∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj)) → IsZero K.obj := by
  classical
  have htop : IsAffineOpen (⊤ : X.Opens) := by
    by_cases hs : s.Nonempty
    · obtain ⟨V, hV⟩ := hs
      have heq : s = {V} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hV, fun W hW ↦ Finset.card_le_one.mp hcard W hW V hV⟩
      have hVtop : (V : X.Opens) = ⊤ := by simpa [heq] using hcover
      exact hVtop ▸ V.property
    · have heq : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      have hbot : (⊥ : X.Opens) = ⊤ := by simpa [heq] using hcover
      exact hbot ▸ isAffineOpen_bot X
  have : IsAffine (⊤ : X.Opens).toScheme := htop
  have : IsAffine X := .of_isIso X.topIso.inv
  let U : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  obtain ⟨E, R, adj, hE, hsupport, hunit⟩ :=
    supported_perfect_detector_affine_construction X T hT hTc U rfl
  refine ⟨E, hE, hsupport, ?_⟩
  intro K hK horth
  have := hunit K horth
  have hz := supported_derived_restriction_zero X T U (by rfl) K.obj hK
  have hR : IsZero (R.obj
      (((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory).obj K.obj)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (adj.homEquiv _ _).symm.injective
    exact hz.eq_of_tgt _ _
  exact hR.of_iso (asIso (adj.unit.app K.obj))

end AlgebraicGeometry
