/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalizedResidueHomology
import WeilConjectures.AlgebraicGeometry.LocalizedResidueHomologySheafRestriction
import WeilConjectures.AlgebraicGeometry.FieldSpecTensorPullbackGlobalSections

/-! # Restriction of derived residue homology to an open subscheme

Source: Stacks Project, Tags 0D5S and 0098.
(blueprint: lem-sc-localized-residue-homology-restriction).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Derived residue homology is unchanged by restriction to an open containing the point,
with the residue fields identified by the open immersion's residue map.
Source: Stacks Project, Tags 0D5S and 0098.
(blueprint: lem-sc-localized-residue-homology-restriction).

Proof: The over-site equivalence identifies exact restriction with tensor pullback
along the open immersion. The induced derived equivalence therefore identifies the
restriction functor with its derived pullback; the latter is computed without a
resolution since open restriction is exact. Compose with derived pullback to the
residue point of the open. The square formed by the two residue morphisms, the open
immersion, and the spectrum of its residue-field isomorphism commutes. Derived pullback
composition (Tag 0D5S) identifies the two routes naturally. On the residue schemes,
exact global sections commute with degree-zero homology. Scalar transport along
GammaSpecIso identifies pullback along the residue-field isomorphism with extension of
scalars along its ring map. Composing these natural identifications gives the stated
natural isomorphism. If the open is empty there is no point x. This argument applies
to every derived object and imposes no perfectness or cohomology-invertibility condition.
The standard localizations in localizedResidueHomology and the supplied localizations
are compared by the canonical equivalences of localizations, so their universes need
not coincide. -/
theorem nonempty_localizedResidueHomology_restriction_iso (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ s : S, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField s)).toRingedSpace))]
    (U : S.Opens) (x : U.toScheme) :
    Nonempty
      ((SheafOfModules.overFunctor.{u}
          (moduleRings S.toRingedSpace) U).mapDerivedCategory ⋙
          localizedResidueHomology S U x ≅
        derivedPullback (S.fromSpecResidueField (U.ι x)) ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u}
              (moduleRings (Spec (S.residueField (U.ι x))).toRingedSpace)) 0 ⋙
          SheafOfModules.evaluation
            (moduleRings (Spec (S.residueField (U.ι x))).toRingedSpace) (op ⊤) ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso (S.residueField (U.ι x))).inv.hom ⋙
          ModuleCat.extendScalars (U.ι.residueFieldMap x).hom) := by
  let : HasDerivedCategory.{u + 1} U.toScheme.Modules :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace)) :=
    HasDerivedCategory.standard _
  let : (Scheme.Modules.overEquiv U).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  obtain ⟨e⟩ := nonempty_localizedResidueHomology_sheaf_restriction_iso S U x
  obtain ⟨d⟩ := nonempty_fieldSpec_tensorPullback_globalSections_iso
    (S.residueField (U.ι x)) (U.toScheme.residueField x) (U.ι.residueFieldMap x)
  let G := SheafOfModules.evaluation
    (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace) (op ⊤) ⋙
      ModuleCat.restrictScalars (Scheme.ΓSpecIso (U.toScheme.residueField x)).inv.hom
  refine ⟨?_⟩
  exact Functor.isoWhiskerRight e G ≪≫
    Functor.isoWhiskerLeft
      (derivedPullback (S.fromSpecResidueField (U.ι x)) ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u}
            (moduleRings (Spec (S.residueField (U.ι x))).toRingedSpace)) 0) d


end AlgebraicGeometry
