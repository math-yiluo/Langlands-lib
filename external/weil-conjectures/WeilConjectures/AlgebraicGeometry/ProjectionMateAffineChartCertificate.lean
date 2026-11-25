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
import WeilConjectures.AlgebraicGeometry.ProjectionMateAffineChartData
import WeilConjectures.AlgebraicGeometry.ProjectionMateAffineChartTransport

/-! # A local affine comparison certificate for a supplied projection mate

Source: Stacks Project, Tag 08EU, affine-local reduction of the projection formula.
(blueprint: lem-pc-projection-mate-affine-chart-certificate).
-/

@[expose] public section

universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

-- Eliminating the nested chart witnesses elaborates two standard localization instances.
/-- Every affine chart supplies an affine projection mate whose invertibility implies
invertibility of the original mate on the cohomology sheaves restricted to that chart.
There is no affine projection-formula hypothesis in this comparison theorem.
Source: Stacks Project, Tag 08EU, first sentence of the proof; the localization
transport argument in lem-pc-qcqs-projection-mate-affine-descent, steps 1--3.
(blueprint: lem-pc-projection-mate-affine-chart-certificate).

Proof: let A be the ring of sections of V and Z the inverse-image open in X.
Quasi-compactness of f makes Z quasi-compact; open restriction preserves
quasi-separatedness. Identify V with Spec A by its canonical affine chart.
Use the standard derived localizations, of morphism universe u+1, on Z and Spec A.
Exact open restriction is a localization, with fully faithful derived right adjoint:
on a K-injective representative the counit restricts direct image back to the same
complex. Write RY and RX for restriction to V and its inverse image. Pullback and
tensor commute naturally with restriction, and direct image commutes naturally with
target restriction. Consequently Lf* takes maps inverted by RY to maps inverted by RX,
and Rf* takes maps inverted by RX to maps inverted by RY. Localize the supplied
adjunction p along RY and RX: its unit and counit descend by naturality, and their
triangle identities remain true after restriction. This gives the local adjunction.
Both bifunctors in the restriction of t factor through RY in each variable. Lift t
and its inverse through the product localization (equivalently evaluate on the fully
faithful right adjoints and conjugate by localization counits). Naturality with the
localization units identifies the lifted components with the original restricted
components, and their two inverse identities give the local natural isomorphism.
The localized adjunction counit at RX(L) is the image of the original counit at L,
conjugated by the direct-image and pullback comparisons. Expanding the counit formula
for homEquiv and using naturality of the lifted t therefore identifies restriction
of the original mate with the local mate, up to invertible source and target maps.
Canonical equivalences
between derived localizations and the affine chart isomorphism transport the tensor,
pullback, direct image, q and s to the standard affine categories. Restrict M and L
and transport them to obtain N and E; exact restriction preserves quasi-coherent
cohomology. An invertible affine mate remains invertible under these equivalences.
Since exact restriction commutes with cohomology, its cohomology in each degree is
precisely the restriction of the original cohomology map, proving the implication.
An empty chart gives zero restricted cohomology and the same construction. -/
theorem exists_projectionMate_affineChart_certificate
    (X Y : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X))
    (M : schemeDerivedQCohCategory Y) (L : schemeDerivedQCohCategory X)
    (V : Y.Opens) (hV : IsAffineOpen V) :
    ∃ (A : Type u) (hA : CommRing A),
      letI := hA
      ∃ (Z : Scheme.{u}) (hZ : CompactSpace Z) (hZqs : QuasiSeparatedSpace Z),
        letI := hZ
        letI := hZqs
        letI := HasDerivedCategory.standard
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
        letI := HasDerivedCategory.standard
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
        ∃ (g : Z ⟶ Spec (.of A)) (hg : QuasiCompact g) (hgqs : QuasiSeparated g),
          letI := hg
          letI := hgqs
          ∃ (eV : Spec (.of A) ≅ V.toScheme)
            (eZ : Z ≅ (f ⁻¹ᵁ V).toScheme),
            g ≫ eV.hom = eZ.hom ≫ (f ∣_ V) ∧
          ∃ (q : derivedPullback g ⊣ schemeDerivedDirectImage g)
            (s : tensor (schemeDerivedCategory (Spec (.of A))) ⋙ derivedPullback g ≅
              (derivedPullback g).prod (derivedPullback g) ⋙ tensor (schemeDerivedCategory Z))
            (N : schemeDerivedQCohCategory (Spec (.of A))) (E : schemeDerivedQCohCategory Z),
            IsIso (q.homEquiv (N.obj ⊗ (schemeDerivedDirectImage g).obj E.obj)
              ((derivedPullback g).obj N.obj ⊗ E.obj)
              (s.hom.app (N.obj, (schemeDerivedDirectImage g).obj E.obj) ≫
                (𝟙 ((derivedPullback g).obj N.obj) ⊗ₘ q.counit.app E.obj))) →
            ∀ n : ℤ, IsIso (((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).map
              (p.homEquiv (M.obj ⊗ (schemeDerivedDirectImage f).obj L.obj)
              ((derivedPullback f).obj M.obj ⊗ L.obj)
              (t.hom.app (M.obj, (schemeDerivedDirectImage f).obj L.obj) ≫
                (𝟙 ((derivedPullback f).obj M.obj) ⊗ₘ p.counit.app L.obj)))).over V) := by
  obtain ⟨A, hA, Z, hZ, hZqs, g, hg, hgqs, eV, eZ, hcomm⟩ :=
    exists_projectionMate_affineChart_data X Y f V hV
  let := hA
  let := hZ
  let := hZqs
  let := hg
  let := hgqs
  obtain ⟨q, s, N, E, htransport⟩ :=
    projectionMate_affineChart_transport X Y f p t M L V A Z g eV eZ hcomm
  exact ⟨A, hA, Z, hZ, hZqs, g, hg, hgqs, eV, eZ, hcomm, q, s, N, E, htransport⟩

end AlgebraicGeometry
