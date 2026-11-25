/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import WeilConjectures.AlgebraicGeometry.ProjectionMateAffineChartCertificate
import WeilConjectures.Topology.SheafIsomorphismLocalOpenCover

/-! # Affine descent for supplied derived projection mates

Source: Stacks Project, Tag 08EU, local reduction of the projection formula.
(blueprint: lem-pc-qcqs-projection-mate-affine-descent).
-/

@[expose] public section

universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

/-- The projection-mate theorem for affine targets implies its global case.
Source: Stacks Project, Tag 08EU, first sentence of the proof.
(blueprint: lem-pc-qcqs-projection-mate-affine-descent).

Proof: cover Y by affine opens V, each identified with Spec Gamma(V,O).
The inverse image U is quasi-compact since f is quasi-compact and V is affine,
and it is quasi-separated since X is quasi-separated. Restriction is exact
and is a localization whose derived direct-image right adjoint is fully
faithful. Pullback and tensor commute with open restriction and direct image
commutes with restriction on the target. Thus both bifunctors compared by t
factor through these localizations. Evaluate t on the fully faithful right
adjoints and use the invertible localization counits to descend the supplied
tensor comparison. Transport the supplied adjunction by the same procedure.
The restricted displayed Hom-equivalence mate is precisely this transported
mate, by the counit formula for the Hom equivalence. Change chosen derived
localizations to standard ones by their canonical localization equivalences;
these equivalences transport the K-flat tensor, pullback, direct image, t and
p. Transport also across V isomorphic to Spec Gamma(V,O). Apply haffine and
reflect invertibility through these equivalences. Restriction preserves
quasi-coherent cohomology. Finally exact restriction commutes with cohomology,
and isomorphisms of cohomology sheaves are detected on the affine open cover,
so the original mate is invertible. For empty Y the cover is empty and all
cohomology sheaves are zero, giving the same conclusion. -/
theorem qcqsProjectionMate_of_affine
    (haffine : ∀ (A : Type u) [CommRing A] (Z : Scheme.{u})
      [CompactSpace Z] [QuasiSeparatedSpace Z]
      [HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
      [HasDerivedCategory.{u + 1}
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
      (g : Z ⟶ Spec (.of A)) [QuasiCompact g] [QuasiSeparated g]
      (q : derivedPullback g ⊣ schemeDerivedDirectImage g)
      (s : tensor (schemeDerivedCategory (Spec (.of A))) ⋙ derivedPullback g ≅
        (derivedPullback g).prod (derivedPullback g) ⋙ tensor (schemeDerivedCategory Z))
      (N : schemeDerivedQCohCategory (Spec (.of A))) (E : schemeDerivedQCohCategory Z),
      IsIso (q.homEquiv (N.obj ⊗ (schemeDerivedDirectImage g).obj E.obj)
        ((derivedPullback g).obj N.obj ⊗ E.obj)
          (s.hom.app (N.obj, (schemeDerivedDirectImage g).obj E.obj) ≫
            (𝟙 ((derivedPullback g).obj N.obj) ⊗ₘ q.counit.app E.obj))))
    (X Y : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
    (M : schemeDerivedQCohCategory Y) (L : schemeDerivedQCohCategory X) :
    IsIso (p.homEquiv (M.obj ⊗ (schemeDerivedDirectImage f).obj L.obj)
      ((derivedPullback f).obj M.obj ⊗ L.obj)
        (t.hom.app (M.obj, (schemeDerivedDirectImage f).obj L.obj) ≫
          (𝟙 ((derivedPullback f).obj M.obj) ⊗ₘ p.counit.app L.obj))) := by
  classical
  let α := p.homEquiv (M.obj ⊗ (schemeDerivedDirectImage f).obj L.obj)
    ((derivedPullback f).obj M.obj ⊗ L.obj)
    (t.hom.app (M.obj, (schemeDerivedDirectImage f).obj L.obj) ≫
      (𝟙 ((derivedPullback f).obj M.obj) ⊗ₘ p.counit.app L.obj))
  change IsIso α
  apply (DerivedCategory.isIso_iff _ α).2
  intro n
  apply (sheaf_module_isIso_iff_isIso_over_open_cover Y.toRingedSpace Y.affineOpens
    (fun V ↦ V.1) (iSup_affineOpens_eq_top Y) _ _ _).2
  intro V
  obtain ⟨A, hA, Z, hZ, hZqs, g, hg, hgqs, _eV, _eZ, _hchart, q, s, N, E, hc⟩ :=
    exists_projectionMate_affineChart_certificate X Y f p t M L V.1 V.2
  let := hA
  let := hZ
  let := hZqs
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
  let := hg
  let := hgqs
  exact hc (haffine A Z g q s N E) n


end AlgebraicGeometry
