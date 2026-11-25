/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh
import WeilConjectures.AlgebraicGeometry.SupportedOpenTensorDirectImageComparisons
import WeilConjectures.AlgebraicGeometry.QCqsDerivedProjectionIsoUniverses
import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Data.Int.Interval
import WeilConjectures.AlgebraicGeometry.OpenDerivedCategorySmall
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh
import WeilConjectures.AlgebraicGeometry.DirectImageQCSupportReduction
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition
import WeilConjectures.AlgebraicGeometry.SupportedOpenPushforward
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-! # Derived projection formula for a complex with proper support

Source: Stacks Project, Tags 08EV (support reduction) and 08EU (projection formula).
(blueprint: lem-pc-proper-support-derived-projection-formula)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

private theorem zero_stalk (X : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (hM : IsZero M) (x : X) :
    Subsingleton (↑(TopCat.Presheaf.stalk M.val.presheaf x)) := by
  exact ModuleCat.subsingleton_of_isZero
    ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map_isZero hM)

private theorem compact_open_support
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsNoetherian S]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E))
    (hs : ∀ n : ℤ, Modules.HasSupportProperOver f
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E)) :
    ∃ (T : TopologicalSpace.Closeds X) (U : X.Opens),
      IsCompact (U : Set X) ∧ (T : Set X) ⊆ (U : Set X) ∧
      ∀ (n : ℤ) (x : X), x ∉ (T : Set X) →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E).val.presheaf x)) := by
  classical
  obtain ⟨a, b, hab⟩ := hb
  choose Z hZ hp using hs
  let I := {n : ℤ // n ∈ Finset.Icc a b}
  let e := (Fintype.equivFin I).symm
  let W : Fin (Fintype.card I) → TopologicalSpace.Closeds X := fun i ↦ Z (e i).val
  let T : TopologicalSpace.Closeds X := ⨆ i, W i
  have hT : IsClosedSubsetProperOver f T :=
    (isClosedSubsetProperOver_union_preimage f).1 _ W (fun i ↦ hp (e i).val)
  let j := (IdealSheafData.vanishingIdeal T).subschemeι
  have : IsProper (j ≫ f) := hT
  have : CompactSpace (IdealSheafData.vanishingIdeal T).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (j ≫ f)
  obtain ⟨U, g, hU, _, hg⟩ := j.exists_isCompact_isClosedImmersion
  have hTU : (T : Set X) ⊆ (U : Set X) := by
    have hj : Set.range j = (T : Set X) := by simp [j]
    intro x hx
    obtain ⟨z, rfl⟩ := hj.symm ▸ hx
    rw [← hg]
    exact (g z).property
  refine ⟨T, U, hU, hTU, ?_⟩
  intro n x hx
  by_cases hn : n ∈ Finset.Icc a b
  · by_contra hnonzero
    have hxZ : x ∈ Z n := by
      change x ∈ (Z n : Set X)
      rw [hZ n]
      exact hnonzero
    have hle : Z n ≤ T := by
      have he : (e ((Fintype.equivFin I) ⟨n, hn⟩)).val = n := by simp [e]
      rw [← he]
      exact le_iSup W ((Fintype.equivFin I) ⟨n, hn⟩)
    exact hx (hle hxZ)
  · apply zero_stalk X _ (hab n ?_) x
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    exact hn

private theorem qc_single (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (F : SheafOfModules.{u} (moduleRings S.toRingedSpace)) (hF : F.IsQuasicoherent) :
    schemeDerivedQCohProperty S ((DerivedCategory.singleFunctor _ 0).obj F) := by
  have hzero : IsZero
      (SheafOfModules.free (R := moduleRings S.toRingedSpace) PEmpty.{u + 1}) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  have : (SheafOfModules.isQuasicoherent (moduleRings S.toRingedSpace)).ContainsZero :=
    ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free PEmpty.{u + 1}⟩⟩
  intro n
  by_cases hn : n = 0
  · subst n
    exact (SheafOfModules.isQuasicoherent (moduleRings S.toRingedSpace)).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm hF
  · apply (SheafOfModules.isQuasicoherent (moduleRings S.toRingedSpace)).prop_of_isZero
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE _ 0 n hn
    · exact DerivedCategory.isZero_of_isLE _ 0 n hn

/-- Proper support permits the derived projection formula without assuming f quasi-compact.
Source: Stacks Project, Tag 08EV, proof, support reduction and first displayed equality;
Tag 08EU.
(blueprint: lem-pc-proper-support-derived-projection-formula)

Proof: Boundedness gives finitely many nonzero cohomology sheaves. Their supports
have proper union T over S, hence T is quasi-compact. Choose a quasi-compact open
j:U -> X containing T. Since S is Noetherian and f is locally of finite type,
X is locally Noetherian and f|U is quasi-compact and quasi-separated. Restriction
is exact; the supported-open comparison and composition of derived direct images
identify Rf*E with R(f|U)*(E|U). Coherence implies quasi-coherence here. For a
quasi-coherent F, apply Tag 08EU on U to obtain the projection isomorphism.
Derived tensor and pullback commute with open restriction. The cohomological
support of E tensor^L Lf*(F[0]) is contained in T: its restriction outside T is
zero because E restricts to zero and tensor preserves zero. Thus the same
supported-open comparison identifies its direct image from U with that from X.
Compose these comparisons with the projection isomorphism on U. The result is
an isomorphism of the two displayed objects for the fixed derived localizations
on X and S; auxiliary localizations on U are transported by their equivalences.
No Tor bound is used in this argument. -/
theorem nonempty_properSupport_derivedProjection_iso
    (S : Scheme.{u}) [IsNoetherian S]
    (X : Scheme.{u}) (f : X ⟶ S) [LocallyOfFiniteType f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hcoherent : ∀ i : ℤ,
      RingedSpace.IsCoherent X.toRingedSpace
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (hsupport : ∀ i : ℤ,
      Scheme.Modules.HasSupportProperOver f
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E))
    (F : SheafOfModules.{u} (moduleRings S.toRingedSpace)) (hF : F.IsQuasicoherent) :
    Nonempty (((schemeDerivedDirectImage f).obj E) ⊗
        (DerivedCategory.singleFunctor _ 0).obj F ≅
      (schemeDerivedDirectImage f).obj
        (E ⊗ (derivedPullback f).obj ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨T, U, hU, hTU, hET⟩ := compact_open_support f E hbounded hsupport
  let K := (DerivedCategory.singleFunctor _ 0).obj F
  obtain ⟨hDU⟩ := nonempty_openHasDerivedCategory X U
  let := hDU
  obtain ⟨⟨eE⟩, ⟨eTensor⟩⟩ :=
    supportedOpen_tensor_directImage_comparisons f U T T.isClosed hTU E hET K
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : QuasiCompact (U.ι ≫ f) := inferInstance
  have : QuasiSeparated (U.ι ≫ f) := inferInstance
  have hEU : schemeDerivedQCohProperty U.toScheme
      ((schemeOpenRestriction X U).mapDerivedCategory.obj E) := by
    apply (schemeDerivedQCoh_openRestriction_iff X U E).mpr
    intro n
    have hq := ((Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
      (hcoherent n)).1
    have := hq
    exact SheafOfModules.isQuasicoherent_over ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E) U
  obtain ⟨eProjection⟩ := nonempty_qcqs_derivedProjection_iso_universes
    (U.ι ≫ f) _ hEU K (qc_single S F hF)
  exact ⟨tensorIso eE (Iso.refl K) ≪≫ eProjection ≪≫ eTensor.symm⟩

end AlgebraicGeometry.Scheme
